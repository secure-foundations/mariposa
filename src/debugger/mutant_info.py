from enum import Enum
import hashlib
import json
import os
import subprocess
from base.defs import MARIPOSA
from base.solver import RCode, output_as_rcode
from debugger.z3_utils import dump_z3_proof
from debugger.inst_graph import *
from debugger.options import DebugOptions
from utils.query_utils import (
    Mutation,
    emit_mutant_query,
    get_trace_stats_axiom_profiler,
)
from utils.system_utils import log_check, log_debug, log_info, log_warn, subprocess_run


TRACES = "traces"
MUTANTS = "mutants"
CORES = "cores"


class TraceFailure(Enum):
    TIMEOUT = "timeout"
    SLOW_UNKNOWN = "slow_unknown"
    FAST_UNKNOWN = "fast_unknown"
    NOT_FAIL = "did not fail"
    FAST2 = "fast2"


class MutantInfo:
    def __init__(self, sub_root, mutation, seed, options):
        self.seed = seed
        self.sub_root = sub_root

        self.orig_path = f"{sub_root}/orig.smt2"
        self.lbl_path = f"{sub_root}/lbl.smt2"

        self.mutation = mutation

        self.mut_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.smt2"
        self.mut_lbl_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.lbl.smt2"

        self.trace_path = f"{sub_root}/{TRACES}/{mutation}.{seed}"
        self.proof_path = f"{sub_root}/proofs/{mutation}.{seed}.proof"

        self.core_path = f"{sub_root}/{CORES}/{mutation}.{seed}.smt2"
        self.core_log = f"{sub_root}/{CORES}/{mutation}.{seed}.log"

        self.graph_path = f"{sub_root}/graphs/{mutation}.{seed}.txt"
        self.stats_path = f"{sub_root}/stats/{mutation}.{seed}.txt"

        self.meta_path = f"{sub_root}/meta/{mutation}.{seed}.json"

        # have not ran yet!
        self.trace_rcode = RCode.ERROR
        self.trace_time = -1
        self.proof_time = -1

        self.options: DebugOptions = options

        self.discard = False
        self._graph = None

    @staticmethod
    def from_dict(d, options):
        mi = MutantInfo(d["sub_root"], Mutation(d["mutation"]), d["seed"], options)
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

    def save(self):
        if self.discard:
            return self.clear()

        self.__should_build(self.meta_path, clear=True)

        with open(self.meta_path, "w+") as f:
            json.dump(self.to_dict(), f)

    def clear(self):
        for path in [
            self.mut_path,
            self.trace_path,
            self.proof_path,
            self.core_path,
            self.core_log,
            self.graph_path,
            self.stats_path,
            self.meta_path,
        ]:
            if os.path.exists(path):
                os.remove(path)

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

    def build_trace(self, clear=False) -> bool:
        if not self.__should_build(self.trace_path, clear):
            log_info(f"[trace] found {self.trace_path}")
            return True
        self.build_mutant_query()

        # soft timeout (-t) is used, otherwise the log might be malformed
        solver_args = [
            "./bin/z3-4.13.0",
            f"-t:{self.options.per_trace_time_sec *1000}",
            self.mut_path,
            "trace=true",
            f"trace_file_name={self.trace_path}",
        ]

        stdout, _, elapsed = subprocess_run(solver_args, check=True, debug=False)
        res = output_as_rcode(stdout)
        self.trace_rcode = res
        self.trace_time = elapsed
        return True

    def trace_passed(self):
        rc = self.trace_rcode

        assert self.has_trace()
        assert rc != RCode.ERROR

        if (
            rc == RCode.UNSAT
            and self.trace_time / 1000 < self.options.per_trace_time_sec
        ):
            return True

        return False

    def fmt_trace_info(self):
        rc = self.trace_rcode
        assert self.has_trace()
        assert rc != RCode.ERROR
        return f"{self.trace_path} {rc} {self.trace_time/1000}"

    def has_core(self):
        return os.path.exists(self.core_path)

    def build_core_query(self, clear=False) -> bool:
        if not self.__should_build(self.core_path, clear):
            return True
        self.build_mutant_query(use_lbl=True)

        log_info(f"[core] attempt {self.mut_lbl_path}")

        cf = open(self.core_log, "w+")
        subprocess.run(
            [
                "./bin/z3-4.13.0",
                self.mut_lbl_path,
                f"-t:{self.options.per_core_time_sec*1000}",
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
            return False

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
        return os.path.exists(self.proof_path)

    def build_proof(self, clear=False) -> bool:
        if not self.__should_build(self.proof_path, clear):
            return True

        query_path = self.mut_path
        if os.path.exists(self.core_path):
            log_info(f"[proof] attempt from core (!) {self.core_path}")
            query_path = self.core_path
        else:
            self.build_mutant_query()
            log_info(f"[proof] attempt from mutant {self.mut_path}")

        return dump_z3_proof(
            query_path, self.proof_path, timeout=self.options.per_proof_time_sec * 1000
        )

    def build_graph_log(self, clear=False) -> bool:
        if not self.__should_build(self.graph_path, clear):
            log_info(f"[graph] found {self.graph_path}")
            return True

        with open(self.graph_path, "w") as outfile:
            log_info(f"[graph] building {self.graph_path}")
            subprocess.run(
                [
                    "/home/yizhou7/axiom-profiler-2/target/release/smt-scope",
                    "dependencies",
                    self.trace_path,
                ],
                stdout=outfile,
                check=True,
            )
        assert os.path.exists(self.graph_path)
        return True

    def build_stats_log(self, clear=False) -> bool:
        if not self.__should_build(self.stats_path, clear):
            log_info(f"[stats] found {self.stats_path}")
            return True

        with open(self.stats_path, "w") as outfile:
            log_info(f"[stats] building {self.stats_path}")
            subprocess.run(
                [
                    "/home/yizhou7/axiom-profiler-2/target/release/smt-scope",
                    "stats",
                    self.trace_path,
                ],
                check=True,
                stdout=outfile,
            )
        assert os.path.exists(self.stats_path)
        return True

    def get_trace_graph(self, clear=False) -> TraceInstGraph:
        assert self.has_trace()
        if self._graph is not None and not clear:
            return self._graph
        self.build_graph_log(clear)
        self.build_stats_log(clear)
        self._graph = TraceInstGraph(self.graph_path, self.stats_path)
        return self._graph

    def get_qi_counts(self):
        assert self.has_trace()
        return get_trace_stats_axiom_profiler(self.trace_path)

    def get_failed_reason(self) -> TraceFailure:
        assert self.has_trace()

        rtime = self.trace_time / 1000
        assert self.trace_rcode != RCode.ERROR

        if self.trace_rcode == RCode.TIMEOUT or rtime >= 10:
            return TraceFailure.TIMEOUT

        if self.trace_rcode == RCode.UNSAT:
            return TraceFailure.NOT_FAIL  # ???

        assert self.trace_rcode == RCode.UNKNOWN

        if rtime <= 4:
            return TraceFailure.FAST_UNKNOWN

        return TraceFailure.SLOW_UNKNOWN
