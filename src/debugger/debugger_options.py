from enum import Enum
import json
import os

from utils.system_utils import log_check, log_info


class DbgMode(Enum):
    AUTO = "auto"
    SINGLETON = "singleton"
    DOUBLETON = "doubleton"
    FAST_FAIL = "fast_fail"
    TIMEOUT = "timeout"

class DebugOptions:
    def __init__(self):
        self.ids_available = False
        self.skip_core = False
        self.retry_failed = False
        self.verbose = False

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
        self.is_verus = False

        self.mode = DbgMode.AUTO

def resolve_input_path(input_path, verbose):
    if len(input_path) == 10:
        input_path = f"dbg/{input_path}"
    if input_path.startswith("dbg/") or input_path.startswith("./dbg/"):
        assert not input_path.endswith(".smt2")
        meta = json.load(open(f"{input_path}/meta.json", "r"))
        input_path = meta["given_query"]
        if verbose:
            log_info(f"[init] resolved to {input_path}")
    log_check(os.path.exists(input_path), f"[init] query path {input_path} not found")
    return input_path
