from enum import Enum
import subprocess, select
import time
from utils.sys_utils import subprocess_run
from configure.solver import SolverType

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

    @staticmethod
    def empty_map():
        return {r: 0 for r in RCode}

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

class SolverRunner:
    def __init__(self, si):
        self._si = si
        self.proc = None
        self.poll_obj = None

    def __getattr__(self, item):
        return getattr(self._si, item)
    
    def __str__(self):
        return str(self._si)

    def start_process(self, query_path, timeout):
        assert timeout < 1000
        if self.type == SolverType.Z3:
            args = [self.path, query_path]
        elif self.type == SolverType.CVC5:
            args = [self.path, 
                "--incremental", 
                "-q",
                "--tlimit-per", 
                str(timeout * 1000),
                query_path]
        else:
            assert False
        p = subprocess.Popen(args, stdout=subprocess.PIPE)

        poll_obj = select.poll()
        poll_obj.register(p.stdout, select.POLLIN)
        self.failed = False

        self.proc = p
        self.poll_obj = poll_obj

    def run_quake_iteration(self, timeout):
        if self.failed:
            return RCode.ERROR.value, 0 

        start_time = time.time()
        poll_result = self.poll_obj.poll((timeout + 1) * 1000)
        elapsed = time.time() - start_time

        std_out = ""

        if poll_result:
            outputs = []
            while "[INFO] mariposa-quake" not in std_out:
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
            print(f"[INFO] solver timeout in quake, elapsed {elapsed}, early termination")
            self.failed = True
            rcode = RCode.TIMEOUT
        return rcode.value, elapsed

    def end_process(self):
        self.proc.stdout.close()
        self.proc.terminate()
        self.poll_obj = None

    def run(self, query_path, timelimit, seeds=None):
        if self.type == SolverType.Z3:
            command = f"{self.path} '{query_path}' -T:{timelimit}"
            out, err, elapsed = subprocess_run(command)
            rcode = output_as_rcode(out)
        else:
            assert self.type == SolverType.CVC5
            seed_options = ""

            if seeds is not None:
                seed_options = f"--sat-random-seed {seeds} --seed {seeds}"

            command = f"{self.path} --incremental --quiet --tlimit-per {timelimit * 1000} '{query_path}' {seed_options}"
            out, err, elapsed = subprocess_run(command, timeout=timelimit + 1)

            if elapsed >= timelimit * 1000 or "interrupted by SIGTERM" in out:
                rcode = RCode.TIMEOUT
            else:
                rcode = output_as_rcode(out)     

        if rcode == RCode.ERROR:
            print("[INFO] solver error: {} {} {}".format(command, out, err))

        return rcode.value, elapsed