import json
import os
import pickle
import subprocess
from base.defs import MARIPOSA
from base.solver import RCode, output_as_rcode
from proof_builder import ProofBuilder, ProofInfo
from utils.query_utils import Mutation, emit_mutant_query
from debugger.quant_graph import *
from utils.system_utils import log_check, log_debug, log_info, log_warn, subprocess_run


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
        self.sub_root = sub_root

        self.orig_path = f"{sub_root}/orig.smt2"
        
        self.lbl_path = f"{sub_root}/lbl.smt2"

        self.mutation = mutation

        self.mut_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.smt2"
        self.mut_lbl_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.lbl.smt2"

        self.trace_path = f"{sub_root}/{TRACES}/{mutation}.{seed}"
        self.insts_path = f"{sub_root}/{INSTS}/{mutation}.{seed}"

        self.core_path = f"{sub_root}/{CORES}/{mutation}.{seed}.smt2"
        self.core_log = f"{sub_root}/{CORES}/{mutation}.{seed}.log"

        self.graph_path = f"{sub_root}/graphs/{mutation}.{seed}.txt"
        self.stats_path = f"{sub_root}/stats/{mutation}.{seed}.txt"

        self.meta_path = f"{sub_root}/meta/{mutation}.{seed}.json"

        # have not ran yet!
        self.trace_rcode = RCode.ERROR
        self.trace_time = -1
        self.proof_time = -1

        self.discard = False

    @staticmethod
    def from_dict(d):
        mi = MutantInfo(d["sub_root"], Mutation(d["mutation"]), d["seed"])
        mi.trace_rcode = RCode(d["trace_rcode"])
        mi.trace_time = d["trace_time"]
        return mi

    def to_dict(self):
        return {
            "sub_root": self.sub_root,
            "mutation": str(self.mutation),
            "seed": self.seed,
            "trace_rcode": self.trace_rcode.value,
            "trace_time": self.trace_time,
        }

    def __del__(self):
        if self.discard:
            for path in [
                self.mut_path,
                self.trace_path,
                self.insts_path,
                self.core_path,
                self.core_log,
                self.graph_path,
                self.stats_path,
                self.meta_path,
            ]:
                if os.path.exists(path):
                    os.remove(path)
            return

        self.__should_build(self.meta_path, clear=True)

        with open(self.meta_path, "w+") as f:
            json.dump(self.to_dict(), f)

    def __should_build(self, output_path, clear=False) -> bool:
        log_check(
            output_path.startswith(self.sub_root),
            f"output path {output_path} not under sub_root {self.sub_root}",
        )

        if os.path.exists(output_path):
            if clear:
                os.remove(output_path)
                return True
            return False

        out_dir = os.path.dirname(output_path)

        if not os.path.exists(out_dir):
            os.makedirs(out_dir)

        return True

    def __hash__(self) -> int:
        return hash((self.mutation, self.seed))

    def build_mutant_query(self, use_lbl=False):
        src = self.lbl_path if use_lbl else self.orig_path
        dst = self.mut_lbl_path if use_lbl else self.mut_path
        if not self.__should_build(dst):
            return
        emit_mutant_query(src, dst, self.mutation, self.seed, keep_core=use_lbl)

    def has_trace(self):
        return os.path.exists(self.trace_path)
    
    def get_trace_size(self):
        if not self.has_trace():
            return 0
        return os.path.getsize(self.trace_path)

    def build_trace_log(self, clear=False):
        if not self.__should_build(self.trace_path, clear):
            log_info(f"[trace] found {self.trace_path}")
            return
        self.build_mutant_query()

        # soft timeout (-t) is used, otherwise the log might be malformed
        solver_args = [
            "./bin/z3-4.13.0",
            f"-t:{TRACE_TIME_LIMIT_SEC*1000}",
            self.mut_path,
            "trace=true",
            f"trace_file_name={self.trace_path}",
        ]

        stdout, _, elapsed = subprocess_run(solver_args, check=True, debug=False)
        res = output_as_rcode(stdout)
        self.trace_rcode = res
        self.trace_time = elapsed

    def has_core(self):
        return os.path.exists(self.core_path)

    def build_core_query(self, clear=False):
        if not self.__should_build(self.core_path, clear):
            return True
        self.build_mutant_query(use_lbl=True)

        log_info(f"[core] attempt {self.mut_lbl_path}")

        cf = open(self.core_log, "w+")
        subprocess.run(
            [
                "./bin/z3-4.13.0",
                self.mut_lbl_path,
                f"-t:{CORE_TIME_LIMIT_SEC*1000}",
            ],
            stdout=cf,
        )
        cf.close()
        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()

        if len(lines) <= 1 or "unsat\n" not in lines:
            output = "".join(lines)
            log_debug(f"[core] failed {self.core_log} {output}")
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

        subprocess_run(args, check=True, debug=True)

        log_check(
            os.path.exists(self.core_path),
            f"failed to create core query {self.core_path}",
        )
        # os.remove(self.core_log)
        return True

    def has_proof(self):
        return os.path.exists(self.insts_path)

    def build_graph_log(self, clear=False):
        if not self.__should_build(self.graph_path, clear):
            log_info(f"[graph] found {self.graph_path}")
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

    def build_stats_log(self, clear=False):
        if not self.__should_build(self.stats_path, clear):
            log_info(f"[stats] found {self.stats_path}")
            return self.stats_path

        with open(self.stats_path, "w") as outfile:
            log_info(f"[stats] building {self.stats_path}")
            subprocess.run(
                [
                    "/home/yizhou7/axiom-profiler-2/target/release/smt-log-parser",
                    "stats",
                    self.trace_path,
                ],
                stdout=outfile,
            )
        assert os.path.exists(self.stats_path)
        return self.stats_path
