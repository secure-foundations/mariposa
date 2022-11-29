from tqdm import tqdm
from path_utils import *
from wrap_utils import *
import math
import hashlib

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

def compute_raw_score(qp, org_res, cur_res):
    if org_res["rcode"] != RCode.Z3_R_US:
        # print("cannot compute rscore: " + org_res["rcode"])
        if cur_res["rcode"] != org_res["rcode"]:
            print(org_res["rcode"], cur_res["rcode"])
            print(org_res["rlimit-count"])
            print(cur_res["rlimit-count"])
            print(qp.orig)
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

def compute_rscore(qp, org_res, cur_res):
    rrs = compute_raw_score(qp, org_res, cur_res)
    if rrs == None:
        return None
    else:
        rl_5x = 5 * org_res["rlimit-count"]
        return  (rl_5x -  rrs) / rl_5x

# BUF_SIZE = 65536

# def file_hash(file_path):
#     md5 = hashlib.md5()
#     with open(file_path, 'rb') as f:
#         while True:
#             data = f.read(BUF_SIZE)
#             if not data:
#                 break
#             md5.update(data)
#     return md5.hexdigest()

def compute_deviation(r_scores):
    vs = []
    for r_score in r_scores:
        v = abs(r_score - 0.8)
        vs.append(v * v)
    s = sum(vs) / len(r_scores)
    return math.sqrt(s)

def analyze_exp_res(query_paths):
    # plain_exps = {k:0 for k in RCodes}
    # normalize_exps = {k:0 for k in RCodes}
    # shuffle_exps = {k:0 for k in RCodes}

    skipped = 0
    bad = 0
    for qp in query_paths:
        pers = load_res_file(qp.plain_exp_res)
        exps = qp.normalize_exps() + qp.mix_exps() + qp.shuffle_exps()
        skip = False

        rss = []
        # hashes = set()
        for e in exps:
            # h = file_hash(e.exp)
            # hashes.add(h)
            res = load_res_file(e.res)
            rss.append(compute_rscore(qp, pers, res))

        if None in rss:
            # print(qp.orig)
            skipped += 1
        else:
            dv = compute_deviation(rss)
            pass

    print(f"total: {len(query_paths)}")
    print(f"skipped: {skipped}")
    print(f"bad: {bad}")

    # print_results("plain experiment", plain_exps)
    # print_results("normalize experiment", normalize_exps)
    # print_results("shuffle experiment", shuffle_exps)

if __name__ == "__main__":
    seeds = [10615679144982909142, 16335111916646947812, 9748429691088265249]
    # seeds = [15015368442047288680, 5939703375613848744, 13399430324673592423];
    # query_paths = load_qlist("data/qlists/smtlib_rand100_sat")
    # query_paths = load_qlist("data/qlists/dafny_rand1K")
    # query_paths = load_qlist("data/qlists/dafny_rand100", seeds)
    query_paths = load_qlist("data/qlists/smtlib_rand1K_unsat", seeds)
    # query_paths = load_qlist("data/qlists/smtlib_rand1K_sat")
    analyze_exp_res(query_paths)
