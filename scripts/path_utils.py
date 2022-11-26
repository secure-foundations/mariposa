import sys
import os

DFY_ALL_DIR = "data/dafny/"
SMT_ALL_DIR = "data/smtlib/"
GEN_DIR = "gen/"

SMT2_EXT = ".smt2"
PARSE_CHECK_EXT = ".chk"
MODEL_EXT = ".mdl"
MODEL_TEST_EXT = ".mdlt"
MODEL_TEST_RESULT_EXT = ".mdltr"

## one time file renaming
def replace_path_colons():
    file_paths = list_smt2_files(SMT_ALL_DIR)
    for file_path in file_paths:
        if ":" in file_path or "=" in file_path:
            new_path = file_path.replace(":", "_")
            new_path = file_path.replace("=", "_")
            os.system(f"mv {file_path} {new_path}")

def to_gen_path(query_path, ext):
    if query_path.startswith("data/"):
        assert(query_path.endswith(SMT2_EXT))
        return GEN_DIR + query_path[5::] + ext
    else:
        assert(query_path.startswith("gen/"))
        return query_path + ext

def to_parse_check_path(query_path):
    return to_gen_path(query_path, PARSE_CHECK_EXT)

def to_model_path(query_path):
    return to_gen_path(query_path, MODEL_EXT)

def to_model_test_path(query_path):
    return to_gen_path(query_path, MODEL_TEST_EXT)

def to_model_test_res_path(query_path):
    return to_gen_path(query_path, MODEL_TEST_RESULT_EXT)

def to_shuffle_model_test_path(query_path):
    return to_gen_path(query_path, ".smdlt")

def to_normalize_model_test_path(query_path):
    return to_gen_path(query_path, ".nmdlt")

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(SMT2_EXT):
                file_paths.append(os.path.join(root, file))
    return file_paths

# replace_path_colons()
