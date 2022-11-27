import random
from tqdm import tqdm
from path_utils import *
from wrap_utils import RCodes, RCode, code_des

SMT_PLAIN_QLIST_PATH = "data/qlists/smtlib_all_plain_status.csv"
SMT_EXLUDE_QLIST_PATH = "data/qlists/smtlib_exclude"

def dump_smtlib_plain_status():
    file_paths = list_smt2_files(SMT_ALL_DIR)
    with open(SMT_PLAIN_QLIST_PATH, "w+") as out:
        for file_path in tqdm(file_paths):
            with open(file_path) as f:
                query = f.read()
                if "(set-info :status unsat)" in query:
                    out.write(file_path + ",unsat\n")
                elif "(set-info :status sat)" in query:
                    out.write(file_path + ",sat\n")
                else:
                    assert("(set-info :status unknown)" in query)
                    out.write(file_path + ",unknown\n")

def load_smlib_exclude_qlist():
    excludes = set()
    with open(SMT_EXLUDE_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip()
            excludes.add(line)
    return excludes

excludes = load_smlib_exclude_qlist()

def load_smtlib_qlist(status):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if line[1] == status and line[0] not in excludes:
                filtered.append(line[0])
    return filtered

def load_random_smtlib_sat_qlist(count):
    file_paths = load_smtlib_qlist("sat")
    randlist = random.sample(file_paths, k=count)
    return randlist

def print_results(des, results):
    total = sum([results[k] for k in RCodes])
    print(des)
    print(f"total count: {total}")
    for k in RCodes:
        count = results[k]
        if count != 0:
            print(f"{code_des[k]}: {count}")
    print("")

def load_res_file(path):
    return RCode(open(path).read())

def analyze_model_test():
    plain_tests = {k:0 for k in RCodes}
    shuffle_tests = {k:0 for k in RCodes}
    normalize_tests = {k:0 for k in RCodes}
    normalize_exps = {k:0 for k in RCodes}

    query_paths = load_qlist("data/qlists/smtlib_rand1K_sat")
    # query_paths = load_qlist("data/qlists/smtlib_rand100_sat")
    for qp in query_paths:
        plain_tests[load_res_file(qp.plain_test_res)] += 1
        shuffle_tests[load_res_file(qp.shuffle_test_res)] += 1
        normalize_tests[load_res_file(qp.normalize_test_res)] += 1
        normalize_exps[load_res_file(qp.normalize_exp_res)] += 1
      
    print_results("plain test", plain_tests)
    print_results("shuffle test", shuffle_tests)
    print_results("normalize test", normalize_tests)
    print_results("normalize experiment", normalize_exps)

if __name__ == "__main__":
    analyze_model_test()
