import sys
import os
import random
from config_utils import *
from convert_utils import *

SMT_PLAIN_QLIST_PATH = "data/qlists/smtlib_all_plain_status.csv"

# same query (mutation), same seed, different runs are in the same TrailGroup
class TrailGroup:
    def __init__(self, exp_path, trials, seed=None):
        # number of trials
        self.trials = trials
        # path of the experiment file
        self.exp_path = exp_path
        # path of the result files
        self.ress = list()

        self.seed = seed

        if trials == 1:
            self.ress.append(exp_path + f".r")
        else:
            for i in range(trials):
                self.ress.append(exp_path + f".{i}.r")

    def get_single_res_path(self):
        assert (self.trials == 1)
        assert (len(self.ress) == 1)
        return self.ress[0]

# same mutation, different seeds are in the the same MutationGroup
class MutationGroup:
    def __init__(self, exp_prefix, suffix, config):
        self.tgroups = []
        # path of all result files
        self.ress = []

        for seed in config.seeds:
            exp_path = exp_prefix + "." + str(seed) + "." + suffix
            tg = TrailGroup(exp_path, config.trials, seed)
            self.tgroups.append(tg)
            self.ress += tg.ress

class QPath:
    def __init__(self, query_path, config):
        assert(os.path.exists(query_path))
        assert(query_path.startswith("data/"))
        assert(query_path.endswith(".smt2"))
        self.orig = query_path
        gen_path_pre = config.prefix + query_path[5::]

        # there is only one trail group for plain
        self.plain_tg = TrailGroup(gen_path_pre + ".pe", config.trials)

        if config.seeds != []:
            # each mutation group contains several trail groups
            self.normalize_mg = MutationGroup(gen_path_pre, "ne", config)
            self.shuffle_mg = MutationGroup(gen_path_pre, "se", config)
            self.mixed_mg = MutationGroup(gen_path_pre, "me", config)
        
        # model path
        # self.model = self.gen_path_pre + ".mdl"

        # # test paths
        # self.plain_test = self.model + ".tp"
        # self.plain_test_res = self.plain_test + ".r"

        # self.shuffle_test = self.model + ".ts"
        # self.shuffle_test_res = self.shuffle_test + ".r"

        # self.normalize_test = self.model + ".tn"
        # self.normalize_test_res = self.normalize_test + ".r"

def load_smtlib_qlist(status=None):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if status == None or line[1] == status:
                filtered.append(line[0])
    return filtered

# def load_random_smtlib_sat_qlist(count):
#     file_paths = load_smtlib_qlist("sat")
#     randlist = random.sample(file_paths, k=count)
#     return randlist

# def load_random_smtlib_unsat_qlist(count):
#     file_paths = load_smtlib_qlist("unsat")
#     randlist = random.sample(file_paths, k=count)
#     return randlist

# def load_random_smtlib_known_qlist(count):
#     file_paths = load_smtlib_qlist("unsat") +  load_smtlib_qlist("sat") 
#     randlist = random.sample(file_paths, k=count)
#     return randlist

# def load_dafny_qlist(count):
#     file_paths = list_smt2_files(DFY_CLEAN_DIR)
#     file_paths = random.sample(file_paths, k=count)
#     for file_path in file_paths:
#         print(file_path)

def load_qlist(config):
    f = open(config.qlist_path)
    return [QPath(l.strip(), config) for l in f.readlines()]

if __name__ == "__main__":
    # clean_dafny_queries()
    # replace_path_colons()
    # load_dafny_qlist(1000)
    # qpaths = load_qlist(DFY100_STABLE_EXP_CONFIG)
    # for qp in qpaths:
    #     ptg = qp.plain_tg
    #     assert(len(ptg.ress) == 1)
    #     assert(len(set(qp.normalize_mg.ress)) == 3)
    #     assert(len(set(qp.shuffle_mg.ress)) == 3)
    #     assert(len(set(qp.mixed_mg.ress)) == 3)

    file_paths = list_smt2_files(DFY_CVC5_CLEAN_DIR)
    randlist = random.sample(file_paths, k=100)
    for f in randlist:
        print(f)
