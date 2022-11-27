import sys
import os

DFY_ALL_DIR = "data/dafny/"
SMT_ALL_DIR = "data/smtlib/"
GEN_DIR = "gen/"

## one time file renaming
def replace_path_colons():
    file_paths = list_smt2_files(SMT_ALL_DIR)
    for file_path in file_paths:
        if ":" in file_path or "=" in file_path:
            new_path = file_path.replace(":", "_")
            new_path = file_path.replace("=", "_")
            os.system(f"mv {file_path} {new_path}")

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(SMT2_EXT):
                file_paths.append(os.path.join(root, file))
    return file_paths

class QPath:
    def __init__(self, query_path):
        assert(os.path.exists(query_path))
        assert(query_path.startswith("data/"))
        assert(query_path.endswith(".smt2"))
        self.orig = query_path
        gen_path_pre = GEN_DIR + query_path[5::]

        # model path
        self.model = gen_path_pre + ".mdl"

        # test paths
        self.plain_test = self.model + ".tp"
        self.plain_test_res = self.plain_test + ".r"

        self.shuffle_test = self.model + ".ts"
        self.shuffle_test_res = self.shuffle_test + ".r"

        self.normalize_test = self.model + ".tn"
        self.normalize_test_res = self.normalize_test + ".r"

        # actual experiment paths

        self.plain_exp_res = gen_path_pre + ".pe.r"

        self.normalize_exp = gen_path_pre + ".ne"
        self.normalize_exp_res = self.normalize_exp + ".r"

        self.shuffle_exp = gen_path_pre + ".se"
        self.shuffle_exp_res = self.shuffle_exp + ".r"

def load_qlist(qlist_path):
    f = open(qlist_path)
    return [QPath(l.strip()) for l in f.readlines()]

# replace_path_colons()
