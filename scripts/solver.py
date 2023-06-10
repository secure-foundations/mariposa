import os
from basic_utils import *
import json

class SolverInfo:
    def __init__(self, name, date, path):
        self.name = name
        self.date = date
        self.path = path
        exit_with_on_fail(os.path.exists(self.path), f"[ERROR] solver binary {self.path} does not exist")

    def __str__(self):
        return scrub(self.name).lower()

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)

def load_known_solvers():
    solvers = dict()
    with open("configs/solvers.json") as f:
        objs = json.loads(f.read())
        for obj in objs:
            s = SolverInfo(obj["name"], obj["date"], obj["path"])
            solvers[s.path] = s
    return solvers

KNOWN_SOLVERS = load_known_solvers()

Z3_4_4_2 = KNOWN_SOLVERS["solvers/z3-4.4.2"]
Z3_4_5_0 = KNOWN_SOLVERS["solvers/z3-4.5.0"]
Z3_4_6_0 = KNOWN_SOLVERS["solvers/z3-4.6.0"]
Z3_4_8_5 = KNOWN_SOLVERS["solvers/z3-4.8.5"]
Z3_4_8_8 = KNOWN_SOLVERS["solvers/z3-4.8.8"]
Z3_4_8_11 = KNOWN_SOLVERS["solvers/z3-4.8.11"]
Z3_4_11_2 = KNOWN_SOLVERS["solvers/z3-4.11.2"]
Z3_4_12_1 = KNOWN_SOLVERS["solvers/z3-4.12.1"]

MAIN_Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_11_2, Z3_4_12_1]
