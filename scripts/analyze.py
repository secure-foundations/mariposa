import random
from tqdm import tqdm
from path_utils import *
from wrap_utils import *

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

# def load_smlib_exclude_qlist():
#     excludes = set()
#     with open(SMT_EXLUDE_QLIST_PATH) as f:
#         for line in f.readlines():
#             line = line.strip()
#             excludes.add(line)
#     return excludes

# excludes = load_smlib_exclude_qlist()

def load_smtlib_qlist(status):
    filtered = []
    with open(SMT_PLAIN_QLIST_PATH) as f:
        for line in f.readlines():
            line = line.strip().split(",")
            assert(len(line) == 2)
            if line[1] == status:
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
    stats = dict()
    for line in open(path).readlines():
        line = line.strip().split(",")
        key = line[0]
        if key == "rlimit-count":
            stats[key] = int(line[1])
        else:
            stats[key] = line[1]
    if "rlimit-count" not in stats:
        stats["rlimit-count"] = GLOBAL_RLIMIT * 2
    return stats

def precent_change(curr, orig):
    return (round((curr - orig) * 100 / orig, 2))

def analyze_test_res():
    plain_tests = {k:0 for k in RCodes}
    shuffle_tests = {k:0 for k in RCodes}
    normalize_tests = {k:0 for k in RCodes}

    ratios = []

    for qp in query_paths:
        ptrs = load_res_file(qp.plain_test_res)
        strs = load_res_file(qp.shuffle_test_res)
        ntrs = load_res_file(qp.normalize_test_res)

        plain_tests[ptrs["rcode"]] += 1
        shuffle_tests[strs["rcode"]] += 1
        normalize_tests[ntrs["rcode"]] += 1

        o = pers["rlimit-count"]

        a = ptrs["rlimit-count"]
        b = strs["rlimit-count"]
        c = ntrs["rlimit-count"]

        # ratios.append(a / b)
        # ratios.append(a / c)
        ratios.append(o / a)

    print(len(ratios), sum(ratios) / len(ratios))

    print_results("plain test", plain_tests)
    print_results("shuffle test", shuffle_tests)
    print_results("normalize test", normalize_tests)

def analyze_exp_res(query_paths):
    plain_exps = {k:0 for k in RCodes}
    normalize_exps = {k:0 for k in RCodes}
    shuffle_exps = {k:0 for k in RCodes}

    for qp in query_paths:
        pers = load_res_file(qp.plain_exp_res)
        ners = load_res_file(qp.normalize_exp_res)
        sers = load_res_file(qp.shuffle_exp_res)

        plain_exps[pers["rcode"]] += 1
        normalize_exps[ners["rcode"]] += 1
        shuffle_exps[sers["rcode"]] += 1

        a = pers["rlimit-count"]
        b = ners["rlimit-count"]
        c = sers["rlimit-count"]

        pb = precent_change(b, a)
        pc = precent_change(c, a)
        if pb > 100 or pb < -100:
            print(qp.orig)
        if pc > 100 or pc < -100:
            print(qp.orig)
    # print_results("plain experiment", plain_exps)
    # print_results("normalize experiment", normalize_exps)
    # print_results("shuffle experiment", shuffle_exps)

if __name__ == "__main__":
    # query_paths = load_qlist("data/qlists/smtlib_rand100_sat")
    query_paths = load_qlist("data/qlists/smtlib_rand1K_sat")
    analyze_exp_res(query_paths)
