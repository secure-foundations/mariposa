import random
from tqdm import tqdm
from path_utils import *
from wrap_utils import RCodes, RCode

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

def print_results(results):
    total = sum([results[k] for k in RCodes])
    print(total)
    for k in RCodes:
        count = results[k]
        if count != 0:
            print(f"{RCode(k).get_description()}: {count}")

def analyze_model_test():
    plain_tests = {k:0 for k in RCodes}
    shuffle_tests = {k:0 for k in RCodes}
    normalize_tests = {k:0 for k in RCodes}

    with open("data/qlists/smtlib_rand1K_sat") as f:
    # with open("data/qlists/smtlib_rand100_sat") as f:
        for file_path in f.readlines():
            file_path = file_path.strip()
            mdltr_path = to_model_test_res_path(file_path)
            plain_tests[RCode(open(mdltr_path).read())] += 1

            smdl_path = to_shuffle_model_test_path(file_path)
            mdltr_path = to_model_test_res_path(smdl_path)
            shuffle_tests[RCode(open(mdltr_path).read())] += 1

            nmdl_path = to_normalize_model_test_path(file_path)
            mdltr_path = to_model_test_res_path(nmdl_path)
            normalize_tests[RCode(open(mdltr_path).read())] += 1

        print("plain test count: ", end="")
        print_results(plain_tests)

        print("\nshuffle test count: ", end="")
        print_results(shuffle_tests)

        print("\nnormalize test count: ", end="")
        print_results(normalize_tests)

if __name__ == "__main__":
    analyze_model_test()
    # dump_smtlib_plain_status()
    # load_random_smtlib_sat_qlist(1000)
    # for f in load_random_smtlib_sat_qlist(1000):
    #     print(f)
