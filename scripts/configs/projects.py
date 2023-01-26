import os
import random
from enum import Enum

# solver related
class SolverBrand(Enum):
    Z3 = "z3"
    CVC5 = "cvc5"

SOLVER_BINS_DIR = "solvers/"

class SolverInfo:
    def __init__(self, bin_name):
        self.path = SOLVER_BINS_DIR + bin_name
        assert (os.path.exists(self.path))

        self.brand = None
        for e in SolverBrand:
            if e.value in bin_name:
                self.brand = e
                break
        assert (self.brand)
        self.ver = bin_name[len(self.brand.value)+1::]

    def __str__(self):
        return self.brand.value + "-" + self.ver

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)

Z3_4_5_0 = SolverInfo("z3-4.5.0")
Z3_4_4_2 = SolverInfo("z3-4.4.2")
Z3_4_11_2 = SolverInfo("z3-4.11.2")
CVC5_1_0_3 = SolverInfo("cvc5-1.0.3")

# ALL_SOLVERS = [Z3_4_5_0, Z3_4_4_2, Z3_4_11_2, CVC5_1_0_3]
ALL_SOLVERS = [SolverInfo(p) for p in os.listdir(SOLVER_BINS_DIR)]

# project related

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths

class FrameworkName(str, Enum):
    DAFNY = "dafny"
    SERVAL = "serval"

class ProjectConfig:
    def __init__(self, name, framework, plain_dir):
        self.name = name
        self.framework = framework
        self._plain_dir = plain_dir
        assert (plain_dir.endswith("/"))
        assert (os.path.exists(self._plain_dir))
        self.clean_dirs = dict()

    def get_plain_dir(self):
        return self._plain_dir

    def assign_z3_dirs(self, dir):
        assert (os.path.exists(dir))
        assert (dir.endswith("/"))
        for solver in ALL_SOLVERS:
            if solver.brand == SolverBrand.Z3:
                self.clean_dirs[solver] = dir

    def assign_cvc5_dirs(self, dir):
        assert (os.path.exists(dir))
        assert (dir.endswith("/"))
        for solver in ALL_SOLVERS:
            if solver.brand == SolverBrand.CVC5:
                self.clean_dirs[solver] = dir

    def __str__(self):
        solver_assigns = [f"{s}: {d}" for s, d in self.clean_dirs.items()]
        solver_assigns = "\n".join(solver_assigns)
        s = f"""{self.name} {self.framework}
{self._plain_dir}
{solver_assigns}
"""
        return s

# independently sample for each unique directory (NOT for each solver!)
# because we can't guarantee the same query name exists
def get_samples(project, enabled_solvers, count=None):
    samples = dict()
    enabled_dirs = set()

    for solver in enabled_solvers:
        dir = project.clean_dirs[solver]
        enabled_dirs.add(dir)

    dir_samples = dict()
    for dir in enabled_dirs:
        queries = list_smt2_files(dir)
        if count is not None:
            queries = random.choices(queries, k=count)
        dir_samples[dir] = queries

    for solver in enabled_solvers:
        dir = project.clean_dirs[solver]
        samples[solver] = dir_samples[dir]

    return samples

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, "data/s_komodo_plain/")
# all solvers use the clean set
S_KOMODO.assign_cvc5_dirs("data/s_komodo_clean/")
S_KOMODO.assign_z3_dirs("data/s_komodo_clean/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, "data/d_komodo_plain/")
# z3 uses the clean set
D_KOMODO.assign_z3_dirs("data/d_komodo_clean/")