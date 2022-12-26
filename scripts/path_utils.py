import os

DFY_RAW_DIR = "data/dafny/"
DFY_CLEAN_DIR = "data/cdafny/"
DFY_CVC5_CLEAN_DIR = "data/cvc5_cdafny/"

SKOMODO_RAW_DIR = "data/s_komodo"
SKOMODO_CLEAN_DIR = "data/cs_komodo"

SMT_ALL_DIR = "data/smtlib/"

GEN_DIR = "gen/"

DB_PATH = "data/mariposa.db"

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths

