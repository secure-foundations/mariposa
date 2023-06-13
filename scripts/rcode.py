from enum import Enum

class RCode(Enum):
    SAT = 1
    UNSAT = 2
    TIMEOUT = 3
    UNKNOWN = 4
    ERROR = 5

    def from_str(s):
        if s == "sat":
            return RCode.SAT
        elif s == "unsat":
            return RCode.UNSAT
        elif s == "timeout":
            return RCode.TIMEOUT
        elif s == "unknown":
            return RCode.UNKNOWN
        elif s == "error":
            return RCode.ERROR
        else:
            assert False

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
        else:
            assert False

