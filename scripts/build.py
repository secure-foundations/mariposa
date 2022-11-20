import subprocess
import random
import re
import sys
from tqdm import tqdm
from analyze import load_smtlib_qlist
from path_utils import *

MARIPOSA_BIN_PATH = "./target/release/mariposa"

def rules():
    return f"""
rule build_src
    command = cargo build --release

rule mariposa_parse_check 
    command = {MARIPOSA_BIN_PATH} -i $in -o $out  

rule mariposa_gen_model_test
    command = {MARIPOSA_BIN_PATH} -i $query -m $model -o $out 

rule z3_get_model
    command = python3 scripts/solver_utils.py z3_get_model $in $out

rule z3_run_model_test
    command = python3 scripts/solver_utils.py z3_run_model_test $in $out
"""

def emit_parse_check_build(file_paths):
    print(rules())
    for file_path in file_paths:
        chk_path = to_parse_check_path(file_path)
        print(f'build {chk_path}: mariposa_parse_check {file_path} | {MARIPOSA_BIN_PATH}')

def emit_z3_get_model(file_paths):
    print(rules())
    for file_path in file_paths:
        mdl_path = to_model_path(file_path)
        print(f'build {mdl_path}: z3_get_model {file_path}')

def emit_gen_model_test(file_paths):
    print(rules())
    for file_path in file_paths:
        mdl_path = to_model_path(file_path)
        if not os.path.exists(mdl_path):
            continue
        if "unknown" in open(mdl_path).read():
            continue
        mdlt_path = to_model_test_path(file_path)
        print(f'build {mdlt_path}: mariposa_gen_model_test {file_path} {mdl_path} | {MARIPOSA_BIN_PATH}')
        print(f'    query={file_path}')
        print(f'    model={mdl_path}')

def emit_z3_run_model_test(file_paths):
    print(rules())
    for file_path in file_paths:
        mdlt_path = to_model_test_path(file_path)
        mdltr_path = to_model_test_res_path(file_path)
        if not os.path.exists(mdlt_path):
            continue
        if open(mdlt_path).read() == "":
            continue
        file_path = file_path.strip()
        print(f'build {mdltr_path}: z3_run_model_test {mdlt_path}')

def parse_check_smtlib_suites():
    file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
    emit_parse_check_build(file_paths)

def parse_check_dafny_suites():
    file_paths = list_smt2_files(DFY_ALL_DIR)
    emit_parse_check_build(file_paths)

def load_qlist(qlist_path):
    f = open(qlist_path)
    return [l.strip() for l in f.readlines()]

def main():
    process = subprocess.Popen("cargo build --release --quiet", shell=True)
    process.wait()
    assert(process.returncode == 0)

    if len(sys.argv) >= 2:
        file_paths = load_qlist(sys.argv[2])
        eval(sys.argv[1] + "(file_paths)")
    else:
        eval(sys.argv[1] + "()")

if __name__ == "__main__":
    main()
