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

rule mp_gen_plain_test
    command = python3 scripts/wrap_utils.py mp_gen_plain_test $in $out 

rule mp_gen_shuffle_test
    command = python3 scripts/wrap_utils.py mp_gen_shuffle_test $in $out

rule mp_gen_normalize_test
    command = python3 scripts/wrap_utils.py mp_gen_normalize_test $in $out

rule z3_gen_model
    command = python3 scripts/wrap_utils.py z3_gen_model $in $out

rule z3_run
    command = python3 scripts/wrap_utils.py z3_run $in $out

rule mp_gen_normalize_exp
    command = python3 scripts/wrap_utils.py mp_gen_normalize_exp $in $out

rule mp_gen_shuffle_exp
    command = python3 scripts/wrap_utils.py mp_gen_shuffle_exp $in $out
"""

# def emit_parse_check_build(file_paths):
#     print(rules())
#     for file_path in file_paths:
#         chk_path = to_parse_check_path(file_path)
#         print(f'build {chk_path}: mariposa_parse_check {file_path} | {MARIPOSA_BIN_PATH}')

def emit_z3_model_test_rules(query_paths):
    print(rules())
    for qp in query_paths:
        # get models from z3
        print(f'build {qp.model}: z3_gen_model {qp.orig}')

        # combine model and original query into a test
        print(f'build {qp.plain_test}: mp_gen_plain_test {qp.orig} {qp.model} | {MARIPOSA_BIN_PATH}')
        print(f'build {qp.plain_test_res}: z3_run {qp.plain_test}')

        # shuffle the original test
        print(f'build {qp.shuffle_test}: mp_gen_shuffle_test {qp.plain_test} | {MARIPOSA_BIN_PATH}')
        print(f'build {qp.shuffle_test_res}: z3_run {qp.shuffle_test}')

        # normalize the original test
        print(f'build {qp.normalize_test}: mp_gen_normalize_test {qp.shuffle_test} | {MARIPOSA_BIN_PATH}')
        print(f'build {qp.normalize_test_res}: z3_run {qp.normalize_test}')


def emit_z3_exp_rules(query_paths):
    print(rules())
    for qp in query_paths:
        # plain experiment
        print(f'build {qp.plain_exp_res}: z3_run {qp.orig}')

        # normalize experiment
        print(f'build {qp.normalize_exp}: mp_gen_normalize_exp {qp.orig} | {MARIPOSA_BIN_PATH}')
        print(f'build {qp.normalize_exp_res}: z3_run {qp.normalize_exp}')

        # normalize experiment
        print(f'build {qp.shuffle_exp}: mp_gen_shuffle_exp {qp.orig} | {MARIPOSA_BIN_PATH}')
        print(f'build {qp.shuffle_exp_res}: z3_run {qp.shuffle_exp}')

# def parse_check_smtlib_suites():
#     file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
#     emit_parse_check_build(file_paths)

# def parse_check_dafny_suites():
#     file_paths = list_smt2_files(DFY_ALL_DIR)
#     emit_parse_check_build(file_paths)

if __name__ == "__main__":
    process = subprocess.Popen("cargo build --release --quiet", shell=True)
    process.wait()
    assert(process.returncode == 0)

    query_paths = load_qlist(sys.argv[1])
    emit_z3_exp_rules(query_paths)
