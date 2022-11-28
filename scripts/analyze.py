from tqdm import tqdm
from path_utils import *
from wrap_utils import *


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

        # o = pers["rlimit-count"]

        # a = ptrs["rlimit-count"]
        # b = strs["rlimit-count"]
        # c = ntrs["rlimit-count"]

        # ratios.append(a / b)
        # ratios.append(a / c)
        # ratios.append(o / a)

    # print(len(ratios), sum(ratios) / len(ratios))

    print_results("plain test", plain_tests)
    print_results("shuffle test", shuffle_tests)
    print_results("normalize test", normalize_tests)

def compute_raw_score(org_res, cur_res):
    if org_res["rcode"] != RCode.Z3_R_US:
        # print("cannot compute rscore: " + org_res["rcode"])
        return None

    org_rl = org_res["rlimit-count"]

    if cur_res["rcode"] == RCode.Z3_R_TO:
        return 5 * org_rl

    if cur_res["rcode"] == RCode.Z3_R_US:
        cur_rl = cur_res["rlimit-count"]
        if (cur_rl > 2 * org_rl):
            return 5 * org_rl
        return cur_rl
    elif cur_res["rcode"] == RCode.Z3_R_U:
        cur_rl = cur_res["rlimit-count"]
        if (cur_rl > 2 * org_rl):
            return 5 * org_rl
        return cur_rl + 2 * org_rl
    else:
        return None

def compute_rscore(org_res, cur_res):
    rrs = compute_raw_score(org_res, cur_res)
    if rrs == None:
        return None
    else:
        rl_5x = 5 * org_res["rlimit-count"]
        return  (rl_5x -  rrs) / rl_5x

def analyze_exp_res(query_paths):
    plain_exps = {k:0 for k in RCodes}
    normalize_exps = {k:0 for k in RCodes}
    shuffle_exps = {k:0 for k in RCodes}

    for qp in query_paths:
        pers = load_res_file(qp.plain_exp_res)
        ners = load_res_file(qp.normalize_exp_res)
        sers = load_res_file(qp.shuffle_exp_res)
        mers = load_res_file(qp.mix_exp_res)

        plain_exps[pers["rcode"]] += 1
        normalize_exps[ners["rcode"]] += 1
        shuffle_exps[sers["rcode"]] += 1

        rs1 = compute_rscore(pers, ners)
        rs2 = compute_rscore(pers, sers)
        rs3 = compute_rscore(pers, mers)
        if rs1 != None and rs2 != None and rs3 != None:
            avg = round((rs1 + rs2 + rs3) / 3, 2)
            if avg >= 0.85 or avg <= 0.75:
                print(qp.orig)
                print(avg)

    # print_results("plain experiment", plain_exps)
    # print_results("normalize experiment", normalize_exps)
    # print_results("shuffle experiment", shuffle_exps)

if __name__ == "__main__":
    # query_paths = load_qlist("data/qlists/smtlib_rand100_sat")
    # query_paths = load_qlist("data/qlists/dafny_rand1K")
    query_paths = load_qlist("data/qlists/smtlib_rand1K_unsat")
    # query_paths = load_qlist("data/qlists/smtlib_rand1K_sat")
    analyze_exp_res(query_paths)
