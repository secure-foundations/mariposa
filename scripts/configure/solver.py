import os, json
from enum import Enum
from utils.sys_utils import *

SOLVER_CONFIG_PATH = "configs/solvers.json"

class SolverType(str, Enum):
    Z3 = "z3"
    CVC5 = "cvc5"

class SolverInfo:
    def __init__(self, name):
        objs = json.loads(open(SOLVER_CONFIG_PATH).read())
        obj = objs[name]
        self.name = name
        self.date = obj["date"]
        self.path = obj["path"]
        self.type = SolverType(self.name.split("_")[0])
        san_check(os.path.exists(self.path), 
            f"[ERROR] solver binary {self.path} does not exist")

    def pretty_name(self):
        tokens = self.name.split("_")
        version = ".".join(tokens[1:])
        return f"{tokens[0].upper()} {version}"

    def __str__(self):
        return scrub(self.name).lower()

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)
