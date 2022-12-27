import os

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

        # ho long do we wait?
        self.timeout = 30

        # how many solver processes to run in parallel?
        self.num_procs = 8

        self.table_name = self.name + "_results"

#     def __str__(self):
#         return f"""qlist path: {self.qlist_path}
# experiment name: {self.name}
# trials per query: {self.trials}
# solver: {self.solver_paths}
# timeout (seconds): {self.timeout}
# processes: {self.procs}"""

# SERVAL_KOMODO_IDEAL = Config("serval_komodo_ideal", "cs_komodo", ["z3-4.4.2"])
# print(SERVAL_KOMODO_IDEAL)