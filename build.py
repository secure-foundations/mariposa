import os
import subprocess
import random
import re
from tqdm import tqdm

DFY_ALL_DIR = "data/dafny/"
SMT_ALL_DIR = "data/smtlib/"

SMT_PLAIN_QLIST_PATH = "data/qlists/smtlib_all_plain_status.csv"
SMT_EXLUDE_QLIST_PATH = "data/qlists/smtlib_exclude"

MARIPOSA_BIN_PATH = "./target/release/mariposa"

def rules():
    return f"""
rule build_src
    command = cargo build --release

rule parse_check
    command = {MARIPOSA_BIN_PATH} -i $in -o $out

rule z3_get_model
    command = time z3 $in -model -T:20 > $out
"""

## one time file renaming
# def replace_file_name_colons():
#     file_paths = list_smt2_files(SMT_ALL_DIR)
#     for file_path in file_paths:
#         if ":" in file_path:
#             new_path = file_path.replace(":", "_")
#             os.system(f"mv {file_path} {new_path}")

def load_smlib_exclude_qlist():
    excludes = set()
    with open(SMT_EXLUDE_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip()
            excludes.add(line)
    return excludes

excludes = load_smlib_exclude_qlist()

def dump_smtlib_plain_status():
    file_paths = list_smt2_files(SMT_ALL_DIR)
    for file_path in file_paths:
        with open(file_path) as f:
            query = f.read()
            if "(set-info :status unsat)" in query:
                print(file_path + ",unsat")
            elif "(set-info :status sat)" in query:
                print(file_path + ",sat")
            else:
                print(file_path + ",unknown")

def list_smt2_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths

def load_smtlib_qlist(status):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if line[1] == status and line[0] not in excludes:
                filtered.append(line[0])
    return filtered

def load_random_smtlib_sat_qlist():
    file_paths = load_smtlib_qlist("sat") 
    randlist = random.choices(file_paths, k=100)
    return randlist

def smt2_to_chk(query_path):
    assert(query_path.endswith(".smt2"))
    return f"gen/{query_path}.chk"

def smt2_to_mdl(query_path):
    assert(query_path.endswith(".smt2"))
    return f"gen/{query_path}.mdl"

def parse_check_smtlib_solved():
    file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
    print(rules())
    for file_path in file_paths:
        chk_path = smt2_to_chk(file_path)
        print(f'build {chk_path}: parse_check {file_path}')

def parse_check_dafny_tests():
    print(rules())
    file_paths = list_smt2_files(DFY_ALL_DIR)
    for file_path in file_paths:
        chk_path = smt2_to_chk(file_path)
        print(f'build {chk_path}: parse_check {file_path}')

def get_models_smtlib_solved():
    print(rules())
    with open("data/qlists/smtlib_rand100_sat") as f:
        for file_path in f.readlines():
            file_path = file_path.strip()
            mdl_path = smt2_to_mdl(file_path)
            print(f'build {mdl_path}: z3_get_model {file_path}')
    # with open("data/qlists/smtlib_rand100_sat") as f:
    #     for file_path in f.readlines():
    
# def merge_model(file_path):
#     mdl_path = smt2_to_mdl(file_path)
#     defind = set()
#     define_pattern = re.compile("define\-fun ((.)+) \(")
#     declare_pattern = re.compile("declare\-fun ((.)+) \(")

#     with open(mdl_path) as f:
#         for line in f.readlines():
#             match = re.search(define_pattern, line)
#             if match:
#                 defind.add(match.group(1))

#     with open(file_path) as f:
#         for line in f.readlines():
#             match = re.search(declare_pattern, line)
#             if match and match.group(1) in defind:
#                 pass
#             else:
#                 print(line, end="")
#                 # print(line)


def main():
    process = subprocess.Popen("cargo build --release --quiet", shell=True)
    process.wait()
    assert(process.returncode == 0)
    parse_check_dafny_tests()
    # get_models_smtlib_solved()

if __name__ == "__main__":
    main()
