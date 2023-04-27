import os
import random
from enum import Enum

# solver related
class SolverBrand(Enum):
    Z3 = "z3"
    CVC5 = "cvc5"

SOLVER_BINS_DIR = "solvers/"

class SolverInfo:
    def __init__(self, bin_name, date):
        self.path = SOLVER_BINS_DIR + bin_name
        self.data = date
        assert (os.path.exists(self.path))

        self.brand = None
        for e in SolverBrand:
            if e.value in bin_name:
                self.brand = e
                break
        assert (self.brand)
        self.ver = bin_name[len(self.brand.value)+1::]

    def __str__(self):
        return self.brand.value + "_" + self.ver.replace(".", "_")

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)

    def pstr(self):
        assert self.brand.value == "z3"
        return "Z3 " + self.ver

Z3_4_4_2 = SolverInfo("z3-4.4.2", "2015/10/05")
Z3_4_5_0 = SolverInfo("z3-4.5.0", "2016/11/07")
Z3_4_6_0 = SolverInfo("z3-4.6.0", "2017/12/18")
Z3_4_8_5 = SolverInfo("z3-4.8.5","2019/06/02")

# Z3_4_8_6 = SolverInfo("z3-4.8.6","2019/09/19")
# Z3_4_8_7 = SolverInfo("z3-4.8.7","2019/11/19")
Z3_4_8_8 = SolverInfo("z3-4.8.8","2020/05/08")
Z3_4_8_11 = SolverInfo("z3-4.8.11","2021/07/11")

# Z3_4_10_1 = SolverInfo("z3-4.10.1","2021/07/22")

# Z3_4_8_17 = SolverInfo("z3-4.8.17","2022/05/04")
Z3_4_11_2 = SolverInfo("z3-4.11.2", "2022/09/03")
Z3_4_12_1 = SolverInfo("z3-4.12.1", "2023/01/18")

CVC5_1_0_3 = SolverInfo("cvc5-1.0.3", "2022/12/12")

Z3_SOLVERS_ALL = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_11_2, Z3_4_12_1]

# ALL_SOLVERS = [SolverInfo(p) for p in os.listdir(SOLVER_BINS_DIR)]

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths

# project related

class FrameworkName(str, Enum):
    DAFNY = "dafny"
    SERVAL = "serval"
    FSTAR = "fstar"
    VERUS = "verus"

class ProjectConfig:
    def __init__(self, name, framework, orig_solver):
        self.name = name
        self.framework = framework
        self._plain_dir = f"data/{name}_plain/"
        # if not os.path.exists(self._plain_dir):
            # print(f"[WARN] project {self.name} plain dir {self._plain_dir} does not exist")
        self.clean_dirs = dict()
        self.assign_z3_dirs(self._plain_dir.replace("_plain", "_z3_clean"))
        # self.assign_cvc5_dirs(self._plain_dir.replace("_plain", "_cvc5_clean"))
        self.orig_solver = orig_solver

    def get_plain_dir(self):
        return self._plain_dir

    def assign_z3_dirs(self, qdir):
        # if not os.path.exists(qdir):
            # print(f"[WARN] project {self.name} z3 dir {qdir} does not exist")
        assert (qdir.endswith("/"))
        for solver in Z3_SOLVERS_ALL:
            if solver.brand == SolverBrand.Z3:
                self.clean_dirs[solver] = qdir

    def assign_cvc5_dirs(self, qdir):
        # if not os.path.exists(qdir):
            # print(f"[WARN] project {self.name} z3 dir {qdir} does not exist")
        assert (qdir.endswith("/"))
        for solver in Z3_SOLVERS_ALL:
            if solver.brand == SolverBrand.CVC5:
                self.clean_dirs[solver] = qdir

    # independently sample for each unique directory (NOT for each solver!)
    # because we can't guarantee the same query name exists
    def get_samples(self, enabled_solvers, count=None):
        samples = dict()
        enabled_dirs = set()
        # we should have consistent choices if dir is not updated
        random.seed(12345) 

        for solver in enabled_solvers:
            dir = self.clean_dirs[solver]
            enabled_dirs.add(dir)

        dir_samples = dict()
        for dir in enabled_dirs:
            queries = list_smt2_files(dir)
            if count is not None:
                queries = random.sample(queries, k=count)
            dir_samples[dir] = queries

        for solver in enabled_solvers:
            dir = self.clean_dirs[solver]
            samples[solver] = dir_samples[dir]

        return samples