
import os
import pickle
import subprocess
from base.defs import MARIPOSA
from base.solver import output_as_rcode
from proof_builder import ProofBuilder, ProofInfo
from utils.query_utils import emit_mutant_query, parse_trace
from utils.system_utils import log_check, log_info, log_warn, subprocess_run


TRACE_TIME_LIMIT_SEC = 10
CORE_TIME_LIMIT_SEC = 60

TRACE_GOAL_COUNT = 4
CORE_GOAL_COUNT = 2
PROOF_GOAL_COUNT = 1

TRACES = "traces"
MUTANTS = "mutants"
INSTS = "insts"
CORES = "cores"

class MutantInfo:
    def __init__(self, sub_root, mutation, seed):
        self.seed = seed
        self.orig_path = f"{sub_root}/orig.smt2"
        self.lbl_path = f"{sub_root}/lbl.smt2"
        self.mutation = mutation
        self.mut_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.smt2"
        self.trace_path = f"{sub_root}/{TRACES}/{mutation}.{seed}"
        self.insts_path = f"{sub_root}/{INSTS}/{mutation}.{seed}"
        self.core_path = f"{sub_root}/{CORES}/{mutation}.{seed}.smt2"
        self.core_log = f"{sub_root}/{CORES}/{mutation}.{seed}.log"
        self.graph_path = f"{sub_root}/graphs/{mutation}.{seed}.txt"

        self.trace_rcode = -1
        self.trace_time = -1
        self.proof_time = -1

    def __hash__(self) -> int:
        return hash((self.mutation, self.seed))

    def create_mutant(self, source=None):
        if source is None:
            source = self.orig_path

        if os.path.exists(self.mut_path):
            return

        emit_mutant_query(source, self.mut_path, self.mutation, self.seed)

    def build_trace(self):
        self.create_mutant()

        solver_args = [
            "./bin/z3-4.13.0",
            f"-t:{TRACE_TIME_LIMIT_SEC*1000}",
            self.mut_path,
            "trace=true",
            f"trace_file_name={self.trace_path}",
        ]

        stdout, stderr, elapsed = subprocess_run(solver_args, check=True, debug=False)
        res = output_as_rcode(stdout)
        return (res, elapsed)

    def get_trace_size(self):
        if not os.path.exists(self.trace_path):
            return 0
        size = os.path.getsize(self.trace_path)
        return size

    def get_qids(self):
        return parse_trace(self.orig_path, self.trace_path)

    def load_insts(self):
        with open(self.insts_path, "rb") as f:
            self.proof_info: ProofInfo = pickle.load(f)

    def build_core(self):
        self.create_mutant(self.lbl_path)

        with open(self.mut_path, "a") as f:
            f.write("(get-unsat-core)\n")

        log_info(f"[core] attempt {self.mut_path}")

        cf = open(self.core_log, "w+")
        subprocess.run(
            [
                "./bin/z3-4.13.0",
                self.mut_path,
                f"-t:{CORE_TIME_LIMIT_SEC*1000}",
            ],
            stdout=cf,
        )
        cf.close()
        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()

        if len(lines) == 0 or "unsat\n" not in lines:
            return None

        args = [
            MARIPOSA,
            "-i",
            self.lbl_path,
            "--action=reduce-core",
            f"--core-log-path={self.core_log}",
            f"-o",
            self.core_path,
        ]

        # if self.keep_quantified:
        #     args.append("--core-keep-quantified")

        subprocess_run(args, check=True, debug=True)

        log_check(
            os.path.exists(self.core_path),
            f"failed to create core query {self.core_path}",
        )

        return True

    def build_graph(self, clear=False):
        graph_dir = os.path.dirname(self.graph_path)
        if not os.path.exists(graph_dir):
            os.makedirs(graph_dir)

        if os.path.exists(self.graph_path):
            log_info(f"[graph] found {self.graph_path}")
            if clear:
                os.remove(self.graph_path)
            else:
                return self.graph_path

        with open(self.graph_path, "w") as outfile:
            log_info(f"[graph] building {self.graph_path}")
            subprocess.run(
                [
                    "/home/yizhou7/axiom-profiler-2/target/release/smt-log-parser",
                    "dependencies",
                    self.trace_path,
                ],
                stdout=outfile,
            )
        assert os.path.exists(self.graph_path)
        return self.graph_path