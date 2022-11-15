import os
import subprocess
import random
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
    command = {MARIPOSA_BIN_PATH} -i $in -s > $out
"""
## one time file renaming
# def replace_file_name_colons():
#     file_paths = list_smt2_files(SMT_ALL_DIR)
#     for file_path in file_paths:
#         if ":" in file_path:
#             new_path = file_path.replace(":", "_")
#             os.system(f"mv {file_path} {new_path}")

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

def load_smlib_exclude_qlist():
    excludes = set()
    with open(SMT_EXLUDE_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip()
            excludes.add(line)
    return excludes

def load_smtlib_qlist(status):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if line[1] == status:
                filtered.append(line[0])
    return filtered

def load_random_smtlib_sat_qlist():
    file_paths = load_smtlib_qlist("sat") 
    randlist = random.choices(file_paths, k=100)
    for item in randlist:
        print(item)

def parse_check_smtlib_solved():
    file_paths = load_smtlib_qlist("sat") + load_smtlib_qlist("unsat")
    print(rules())
    excludes = load_smlib_exclude_qlist()
    for file_path in file_paths:
        if file_path not in excludes:
            print(f'build gen/{file_path}.chk: parse_check {file_path}')

def main():
    # process = subprocess.Popen("cargo build --release --quiet", shell=True)
    # process.wait()
    # assert(process.returncode == 0)
    # parse_check_smtlib_solved()
    load_random_smtlib_sat_qlist()

if __name__ == "__main__":
    main()
