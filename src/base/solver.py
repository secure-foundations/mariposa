import time, os, json
import subprocess, select
from enum import Enum

from utils.query_utils import QUAKE_MESSAGE
from utils.system_utils import log_check, log_warn, subprocess_run

class RCode(Enum):
    SAT = 1
    UNSAT = 2
    TIMEOUT = 3
    UNKNOWN = 4
    ERROR = 5

    def __str__(self):
        if self == RCode.SAT:
            return "sat"
        elif self == RCode.UNSAT:
            return "unsat"
        elif self == RCode.TIMEOUT:
            return "timeout"
        elif self == RCode.UNKNOWN:
            return "unknown"
        elif self == RCode.ERROR:
            return "error"
        assert False

EXPECTED_CODES = [RCode.UNSAT, RCode.UNKNOWN, RCode.TIMEOUT]

def output_as_rcode(output):
    if "unsat" in output:
        return RCode.UNSAT
    elif "sat" in output:
        return RCode.SAT
    elif "timeout" in output:
        return RCode.TIMEOUT
    elif "unknown" in output:
        return RCode.UNKNOWN
    return RCode.ERROR

class SolverType(Enum):
    Z3 = "z3"
    CVC5 = "cvc5"

class Solver:
    # do not create a solver object directly, use the factory method
    def __init__(self, name, obj):
        self.proc = None
        self.poll_obj = None
        self.name = name
        self.date = obj["date"]
        self.path = obj["path"]
        self.stype = SolverType(self.name.split("_")[0])

        assert os.path.exists(self.path)

    def __str__(self):
        return self.name

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)

    def pretty_name(self):
        tokens = self.name.split("_")
        version = ".".join(tokens[1:])
        return f"{tokens[0].upper()} {version}"

    def start_process(self, query_path, timeout):
        log_check(timeout < 1000, "timeout should be in seconds")
        log_check(self.stype == SolverType.Z3, "interactive mode only supported for z3 solver")

        args = [self.path, query_path]
        p = subprocess.Popen(args, stdout=subprocess.PIPE)

        poll_obj = select.poll()
        poll_obj.register(p.stdout, select.POLLIN)
        self.failed = False

        self.proc = p
        self.poll_obj = poll_obj

    def run_quake_iteration(self, timeout):
        if self.failed:
            return RCode.ERROR, 0 

        start_time = time.time()
        poll_result = self.poll_obj.poll((timeout + 1) * 1000)
        elapsed = time.time() - start_time

        std_out = ""

        if poll_result:
            outputs = []
            while QUAKE_MESSAGE not in std_out:
                # try:
                std_out = self.proc.stdout.readline()
                # except 
                std_out = std_out.decode("utf-8").strip()
                outputs.append(std_out)

                if std_out == "":
                    break

            std_out = "".join(outputs)
            # print(std_out)
            rcode = output_as_rcode(std_out)
        else:
            assert std_out == ""
            log_warn(f"solver timeout in quake, elapsed {elapsed}, early termination")
            self.failed = True
            rcode = RCode.TIMEOUT

        return rcode, elapsed * 1000

    def end_process(self):
        self.proc.stdout.close()
        self.proc.terminate()
        self.poll_obj = None

class Z3Solver(Solver):
    def __init__(self, name, obj):
        super().__init__(name, obj)

    def run(self, query_path, time_limit, seeds=None):
        command = [self.path, 
                   f"'{query_path}'",
                   f"-T:{time_limit}"]
        if seeds is not None:
            command += [f"sat.random_seed={seeds}",
                f"smt.random_seed={seeds}"]

        command = " ".join(command)
        out, err, elapsed = subprocess_run(command)
        rcode = output_as_rcode(out)

        return rcode, elapsed

class CVC5Solver(Solver):
    def __init__(self, name, obj):
        super().__init__(name, obj)

    def run(self, query_path, time_limit, seeds=None, more_options=[]):
        assert time_limit < 1000
        options = [
            f"'{query_path}'",
            "--quiet",
            f"--tlimit-per={time_limit * 1000}",
        ]

        if seeds is not None:
            options += [
                f"--sat-random-seed={str(seeds)}",
                f"--seed={str(seeds)}", 
            ]

        command = [self.path] + options + more_options
        command = " ".join(command)
        out, err, elapsed = subprocess_run(command)

        if elapsed >= time_limit * 1000 or "interrupted by SIGTERM" in out:
            rcode = RCode.TIMEOUT
        else:
            rcode = output_as_rcode(out)     

        if rcode == RCode.ERROR:
            print("[INFO] solver error: {} {} {}".format(command, out, err))

        return rcode, elapsed