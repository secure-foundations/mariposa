from configs.projects import *

DB_PATH = "data/mariposa.db"

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    # SSEED = "sseed"
    # SMT_SEED = "smt_seed"
    # SAT_SEED = "sat_seed"
    RSEED = "rseed"
    LOWER_SHUFFLE = "lower_shuffle"

    def __str__(self):
        return str.__str__(self)

class QueryExpConfig:
    def __init__(self, name, project, db_path):
        self.name = name

        assert isinstance(project, ProjectConfig)

        self.project = project

        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at most
        self.max_mutants = 60

        # how long do we wait? (seconds)
        self.timeout = 60

        self.enabled_muts = [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RSEED]

        self.db_path = db_path

    def get_solver_table_name(self, solver):
        # assert (solver in self.samples)
        return f"{self.name}_{str(solver)}"

class ExpConfig:
    def __init__(self, name, project, solvers, db_path, count=None, load_list=False):
        self.qcfg = QueryExpConfig(name, project, db_path)
        for s in solvers:
            assert isinstance(s, SolverInfo)
        # how many solver processes to run in parallel?
        self.num_procs = 7

        self.samples = dict()
        # these are the enabled solvers and their sampled queries
        if load_list:
            total = 0
            for solver in solvers:
                lname = f"data/sample_lists/{name}_{str(solver)}"
                if not os.path.isfile(lname):
                    print(f"[WARN] sample list not found: {lname}")
                else:
                    solver_samples = set()
                    for line in open(lname).readlines():
                        line = line.strip()
                        solver_samples.add(line)
                    self.samples[solver] = solver_samples
                    total += len(solver_samples)
            # print(name, total)
        else:
            self.samples = project.get_samples(solvers, count)

    def get_solver_summary_table_name(self, solver):
        return self.qcfg.get_solver_table_name(solver) + "_summary"

    def get_project_name(self):
        return self.qcfg.project.name

    # def set_plain_only(self):
    #     self.max_mutants = 0

    # def load_sample_list(self):
        # with open(list_path) as f:
        #     for line in f:

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
S_KOMODO.assign_z3_dirs("data/s_komodo_clean/")
S_KOMODO.assign_cvc5_dirs("data/s_komodo_clean/")

S_CERTIKOS = ProjectConfig("s_certikos", FrameworkName.SERVAL, Z3_4_4_2)
S_CERTIKOS.assign_z3_dirs("data/s_certikos_clean/")
S_CERTIKOS.assign_cvc5_dirs("data/s_certikos_clean/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
# D_KOMODO.assign_cvc5_dirs("data/d_komodo_cvc5_clean/")

D_FVBKV = ProjectConfig("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectConfig("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)

FS_VWASM = ProjectConfig("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_VWASM.assign_cvc5_dirs("data/fs_vwasm_cvc5_clean/")

FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

# Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_8_17, Z3_4_11_2]

S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, Z3_SOLVERS_ALL, DB_PATH)
D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, Z3_SOLVERS_ALL, DB_PATH)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS_ALL, DB_PATH)
D_FVBKV_CFG = ExpConfig("D_FVBKV", D_FVBKV, Z3_SOLVERS_ALL, DB_PATH)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS_ALL, DB_PATH)
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, Z3_SOLVERS_ALL, DB_PATH)
S_CERTIKOS_CFG = ExpConfig("S_CERTIKOS", S_CERTIKOS, Z3_SOLVERS_ALL, DB_PATH)

ALL_CFGS = [D_KOMODO_CFG, S_KOMODO_CFG, D_FVBKV_CFG, D_LVBKV_CFG, FS_DICE_CFG, FS_VWASM_CFG]

D_KOMODO_TO = ProjectConfig("d_komodo_to", FrameworkName.DAFNY, Z3_4_12_1)
D_KOMODO_TO.assign_z3_dirs("data/d_komodo_z3_clean_z3_4_12_1_ext/")
D_KOMODO_TO_CFG = ExpConfig("D_KOMODO_TO", D_KOMODO_TO, [Z3_4_12_1], DB_PATH)

D_FVBKV_TO = ProjectConfig("d_fvbkv_to", FrameworkName.DAFNY, Z3_4_12_1)
D_FVBKV_TO.assign_z3_dirs("data/d_fvbkv_z3_clean_z3_4_12_1_ext/")
D_FVBKV_TO_CFG = ExpConfig("D_FVBKV_TO", D_FVBKV_TO, [Z3_4_12_1], DB_PATH)

D_LVBKV_TO = ProjectConfig("d_lvbkv_to", FrameworkName.DAFNY, Z3_4_12_1)
D_LVBKV_TO.assign_z3_dirs("data/d_lvbkv_z3_clean_z3_4_12_1_ext/")
D_LVBKV_TO_CFG = ExpConfig("D_LVBKV_TO", D_FVBKV_TO, [Z3_4_12_1], DB_PATH)

FS_DICE_TO = ProjectConfig("fs_dice_to", FrameworkName.FSTAR, Z3_4_12_1)
FS_DICE_TO.assign_z3_dirs("data/fs_dice_z3_clean_z3_4_12_1_ext/")
FS_DICE_TO_CFG = ExpConfig("FS_DICE_TO", FS_DICE_TO, [Z3_4_12_1], DB_PATH)

TO_CFGS = [D_KOMODO_TO_CFG, D_FVBKV_TO_CFG, D_LVBKV_TO_CFG, FS_DICE_TO_CFG]

for cfg in TO_CFGS:
    cfg.qcfg.timeout = 150
    cfg.qcfg.max_mutants = 0
