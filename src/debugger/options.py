from enum import Enum
import json
import os

from utils.query_utils import find_verus_procedure_name
from utils.system_utils import log_check, log_info, log_warn


class DbgMode(Enum):
    AUTO = "auto"
    SINGLETON = "singleton"
    DOUBLETON = "doubleton"
    FAST_FAIL = "fast_fail"
    TIMEOUT = "timeout"
    FAST2 = "fast2"
    SKOLEM = "skolem"

    def get_report_suffix(self):
        return {
            DbgMode.SINGLETON: ".report",
            DbgMode.DOUBLETON: ".22.report",
            # DbgMode.DOUBLETON: ".2.report",
            DbgMode.FAST_FAIL: ".ff.report",
            DbgMode.TIMEOUT: ".to.report",
            DbgMode.FAST2: ".ff2.report",
            DbgMode.SKOLEM: ".sk.report",
        }[self]

    def project_prefix(self):
        return {
            DbgMode.SINGLETON: "singleton_",
            DbgMode.DOUBLETON: "doubleton2_",
            # DbgMode.DOUBLETON: "doubleton_",
            DbgMode.FAST_FAIL: "fast_fail_",
            DbgMode.TIMEOUT: "timeout_",
            DbgMode.FAST2: "fast2_",
            DbgMode.SKOLEM: "skolem_",
        }[self]


class DebugOptions:
    def __init__(self):
        self.ids_available = False
        self.skip_core = False
        self.retry_failed = False
        self.verbose = False
        self.build_proof = True

        self.mutant_count = 30

        self.trace_target_count = 1
        self.total_trace_time_sec = 60
        self.per_trace_time_sec = 10

        self.core_target_count = 1
        self.total_core_time_sec = 120
        self.per_core_time_sec = 60

        self.proof_goal_count = 1
        self.total_proof_time_sec = 120
        self.per_proof_time_sec = 30

        self.edit_count = 10
        self.is_verus = None  # auto-conf if None

        self.mode = DbgMode.AUTO  # auto-conf

    def resolve_input_path(self, input_path):
        if len(input_path) == 10:
            input_path = f"dbg/{input_path}"
        if input_path.startswith("dbg/") or input_path.startswith("./dbg/"):
            assert not input_path.endswith(".smt2")
            meta = json.load(open(f"{input_path}/meta.json", "r"))
            input_path = meta["given_query"]
            if self.verbose:
                log_info(f"[init] resolved to {input_path}")
        log_check(
            os.path.exists(input_path), f"[init] query path {input_path} not found"
        )
        v_proc = find_verus_procedure_name(input_path)
        is_verus = v_proc != "no procedure found"
        if self.is_verus is None:
            self.is_verus = is_verus
        log_check(
            self.is_verus == is_verus,
            f"[init] query {input_path} is{'' if is_verus else ' NOT'} Verus, differ from the given option",
        )
        return input_path
