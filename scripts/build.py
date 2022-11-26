import subprocess
import random
import re
import sys
from analyze import load_smtlib_qlist
from path_utils import *
from wrap_utils import *

def rules():
    return f"""
rule build_src
    command = cargo build --release

rule mariposa_parse_check 
    command = {MARIPOSA_BIN_PATH} -i $in -o $out  

rule mariposa_gen_model_test
    command = python3 scripts/wrap_utils.py mariposa_gen_model_test $query $model $out 

rule mariposa_gen_shuffle_model_test
    command = python3 scripts/wrap_utils.py mariposa_gen_shuffle_model_test $in $out

rule mariposa_gen_normalize_model_test
    command = python3 scripts/wrap_utils.py mariposa_gen_normalize_model_test $in $out

rule z3_get_model
    command = python3 scripts/wrap_utils.py z3_get_model $in $out

rule z3_run_model_test
    command = python3 scripts/wrap_utils.py z3_run_model_test $in $out

build 
"""

# def emit_parse_check_build(file_paths):
#     print(rules())
#     for file_path in file_paths:
#         chk_path = to_parse_check_path(file_path)
#         print(f'build {chk_path}: mariposa_parse_check {file_path} | {MARIPOSA_BIN_PATH}')

def emit_z3_model_test_rules(file_paths):
    print(rules())
    mdl_paths = []
    mdlt_paths = []
    mdltr_paths = []

    for file_path in file_paths:
        # get models from z3
        mdl_path = to_model_path(file_path)
        print(f'build {mdl_path}: z3_get_model {file_path}')

        mdl_paths.append(mdl_path)

        # combine model and original query into a test
        mdlt_path = to_model_test_path(file_path)
        print(f'build {mdlt_path}: mariposa_gen_model_test {file_path} {mdl_path} | {MARIPOSA_BIN_PATH}')
        print(f'    query={file_path}')
        print(f'    model={mdl_path}')

        mdlt_paths.append(mdlt_path)

        mdltr_path = to_model_test_res_path(file_path)
        print(f'build {mdltr_path}: z3_run_model_test {mdlt_path}')

        mdltr_paths.append(mdltr_path)

        smdl_path = to_shuffle_model_test_path(file_path)
        print(f'build {smdl_path}: mariposa_gen_shuffle_model_test {mdlt_path} | {MARIPOSA_BIN_PATH}')

        mdltr_path = to_model_test_res_path(smdl_path)
        print(f'build {mdltr_path}: z3_run_model_test {smdl_path}')

        nmdl_path = to_normalize_model_test_path(file_path)

        print(f'build {nmdl_path}: mariposa_gen_normalize_model_test {mdlt_path} | {MARIPOSA_BIN_PATH}')

        mdltr_path = to_model_test_res_path(nmdl_path)
        print(f'build {mdltr_path}: z3_run_model_test {nmdl_path}')

# def parse_check_smtlib_suites():
#     file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
#     emit_parse_check_build(file_paths)

# def parse_check_dafny_suites():
#     file_paths = list_smt2_files(DFY_ALL_DIR)
#     emit_parse_check_build(file_paths)

def load_qlist(qlist_path):
    f = open(qlist_path)
    return [l.strip() for l in f.readlines()]

if __name__ == "__main__":
    process = subprocess.Popen("cargo build --release --quiet", shell=True)
    process.wait()
    assert(process.returncode == 0)

    file_paths = load_qlist(sys.argv[1])
    emit_z3_model_test_rules(file_paths)
