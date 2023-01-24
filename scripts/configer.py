import os
from enum import Enum

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    SSEED = "sseed"

ALL_MUTS = [e.value for e in Mutation]

class SolverName(str, Enum):
    Z3 = "z3"
    CVC5 = "cvc5"

def check_solver_exists(solver_path):
    assert (solver_path.startswith("solvers/"))
    assert (os.path.exists(solver_path))

class ExpConfig:
    def __init__(self, name, solvers, queries):
        self.name = name
        self.solver_paths = []

        # which solvers to use?
        for solver in solvers:
            path = "solvers/" + solver
            check_solver_exists(path)
            self.solver_paths.append(path)

        self.queries = queries

        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at least
        self.min_mutants = 10

        # how many mutants to generate at most
        self.max_mutants = 50

        # how long do we wait? (seconds)
        self.timeout = 45

        # how many solver processes to run in parallel?
        self.num_procs = 8

        self.table_name = self.name + "_results"

        ## margin of error in time (seconds)
        # self.time_moe_limit = 3

        # margin of error in success rate (0.0 - 1.0)
        self.res_moe_limit = 0.05

        # confidence level
        self.confidence_level = 0.95

#     def __str__(self):
#         return f"""qlist path: {self.qlist_path}
# experiment name: {self.name}
# trials per query: {self.trials}
# solver: {self.solver_paths}
# timeout (seconds): {self.timeout}
# processes: {self.procs}"""

# SERVAL_KOMODO_IDEAL = Config("serval_komodo_ideal", "cs_komodo", ["z3-4.4.2"])
# print(SERVAL_KOMODO_IDEAL)