import os
import random
from enum import Enum
from basic_utils import *

# solver related
class SolverBrand(Enum):
    Z3 = "z3"
    CVC5 = "cvc5"
    CUSTOM = "custom_solver"

SOLVER_BINS_DIR = "solvers/"

class SolverInfo:
    def __init__(self, bin_name, date):
        self.path = SOLVER_BINS_DIR + bin_name
        self.data = date
        assert (os.path.exists(self.path))

        self.brand = SolverBrand.CUSTOM
        for e in SolverBrand:
            if e.value in bin_name:
                self.brand = e
                break
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
# Z3_4_8_17 = SolverInfo("z3-4.8.17","2022/05/04")
# Z3_4_10_1 = SolverInfo("z3-4.10.1","2021/07/22")
Z3_4_11_2 = SolverInfo("z3-4.11.2", "2022/09/03")
Z3_4_12_1 = SolverInfo("z3-4.12.1", "2023/01/18")
CVC5_1_0_3 = SolverInfo("cvc5-1.0.3", "2022/12/12")

Z3_SOLVERS_ALL = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_11_2, Z3_4_12_1]

def solver_from_path(spath):
    path = os.path.abspath(spath)
    for s in Z3_SOLVERS_ALL:
        if os.path.abspath(s.path) == path:
            print(f"[INFO] { spath } matches a known solver {s.pstr()}")
            return s
    s = SolverInfo("", "")
    s.ver = ""
    s.path = path
    return s

# ALL_SOLVERS = [SolverInfo(p) for p in os.listdir(SOLVER_BINS_DIR)]

class FrameworkName(str, Enum):
    DAFNY = "dafny"
    SERVAL = "serval"
    FSTAR = "fstar"
    VERUS = "verus"
    OTHER = "other"

class ProjectInfo:
    def __init__(self, name, framework, orig_solver):
        self.name = name
        self.framework = framework
        self._plain_dir = f"data/{name}_plain/"
        self.orig_solver = orig_solver
        self.clean_root_dir = f"data/{name}_z3_clean/"

    def list_queries(self, size=None):
        queries = list_smt2_files(self.clean_root_dir)
        if size is None:
            return queries
        return random.sample(queries, size)

S_KOMODO = ProjectInfo("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
D_KOMODO = ProjectInfo("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
D_FVBKV = ProjectInfo("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectInfo("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)
FS_VWASM = ProjectInfo("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_DICE = ProjectInfo("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

DUMMY = ProjectInfo("dummy", FrameworkName.OTHER, Z3_4_12_1)

ALL_PROJS = [S_KOMODO, D_KOMODO, D_FVBKV, D_LVBKV, FS_VWASM, FS_DICE]
