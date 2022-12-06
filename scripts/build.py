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
    command = python3 scripts/wrap_utils.py z3_run $in $out $timeout

rule mp_gen_normalize_exp
    command = python3 scripts/wrap_utils.py mp_gen_normalize_exp $in $out $seed

rule mp_gen_shuffle_exp
    command = python3 scripts/wrap_utils.py mp_gen_shuffle_exp $in $out $seed

rule mp_gen_mix_exp
    command = python3 scripts/wrap_utils.py mp_gen_mix_exp $in $out $seed
"""

# def emit_parse_check_build(file_paths):
#     print(rules())
#     for file_path in file_paths:
#         chk_path = to_parse_check_path(file_path)
#         print(f'build {chk_path}: mariposa_parse_check {file_path} | {MARIPOSA_BIN_PATH}')

def z3_run_stmts(res_path, query_path, timeout):
    stmts = f"""build {res_path}: z3_run {query_path}
    timeout = {timeout}"""
    return stmts

# def mp_test_stmts(orig, )

# def append_model_test_stmts(qp, stmts, timeout):
#     # get models from z3
#     stmts.append(f'build {qp.model}: z3_gen_model {qp.orig}')

#     # combine model and original query into a test
#     stmts.append(f'build {qp.plain_test}: mp_gen_plain_test {qp.orig} {qp.model} | {MARIPOSA_BIN_PATH}')
#     stmts.append(z3_run_stmts(qp.plain_test_res, qp.plain_test))

# def emit_z3_model_test_rules(query_paths):
#     print(rules())
#     for qp in query_paths:
#         # shuffle the original test
#         print(f'build {qp.shuffle_test}: mp_gen_shuffle_test {qp.plain_test} | {MARIPOSA_BIN_PATH}')
#         print(f'build {qp.shuffle_test_res}: z3_run {qp.shuffle_test}')
#         # normalize the original test
#         print(f'build {qp.normalize_test}: mp_gen_normalize_test {qp.shuffle_test} | {MARIPOSA_BIN_PATH}')
#         print(f'build {qp.normalize_test_res}: z3_run {qp.normalize_test}')

def emit_z3_exp_rules(cfg):
    print(rules())
    query_paths = load_qlist(cfg)
    for qp in query_paths:
        print("# emit plain experiment")
        ptg = qp.plain_tg
        res = ptg.get_single_res_path()
        print(z3_run_stmts(res, qp.orig, cfg.timeout))

        print("# emit normalize experiment")
        for e in qp.normalize_mg.tgroups:
            print(f'build {e.exp_path}: mp_gen_normalize_exp {qp.orig} | {MARIPOSA_BIN_PATH}')
            print(f"    seed = {e.seed}")
            res = e.get_single_res_path()
            print(z3_run_stmts(res, e.exp_path, cfg.timeout))

        print("# emit shuffle experiment")
        for e in qp.shuffle_mg.tgroups:
            print(f'build {e.exp_path}: mp_gen_shuffle_exp {qp.orig} | {MARIPOSA_BIN_PATH}')
            print(f"    seed = {e.seed}")
            res = e.get_single_res_path()
            print(z3_run_stmts(res, e.exp_path, cfg.timeout))

        print("# emit mix experiment")
        for e in qp.mixed_mg.tgroups:
            print(f'build {e.exp_path}: mp_gen_mix_exp {qp.orig} | {MARIPOSA_BIN_PATH}')
            print(f"    seed = {e.seed}")
            res = e.get_single_res_path()
            print(z3_run_stmts(res, e.exp_path, cfg.timeout))

# def parse_check_smtlib_suites():
#     file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
#     emit_parse_check_build(file_paths)

# def parse_check_dafny_suites():
#     file_paths = list_smt2_files(DFY_ALL_DIR)
#     emit_parse_check_build(file_paths)

def time_rlimit_correlation_exp():
    cfg = TIME_RLIMIT_CORRELATION_CONFIG
    query_paths = load_qlist(cfg)
    print(rules())
    for qp in query_paths:
        ptg = qp.plain_tg
        res = ptg.get_single_res_path()
        print(z3_run_stmts(res, qp.orig, cfg.timeout))

def time_consistency_exp():
    cfg = CONSISTENCY_EXP_CONFIG
    qpaths = load_qlist(cfg)
    print(rules())
    for qp in qpaths:
        ptg = qp.plain_tg
        assert(len(ptg.ress) == 4)
        for res in ptg.ress:
            print(z3_run_stmts(res, qp.orig, cfg.timeout))

def smtlib_rand1k_stable_exp():
    cfg = SMT1K_STABLE_EXP_CONFIG
    emit_z3_exp_rules(cfg)

# def thread_consistency_exp():
if __name__ == "__main__":
    process = subprocess.Popen("cargo build --release --quiet", shell=True)
    process.wait()
    assert(process.returncode == 0)
    smtlib_rand1k_stable_exp()