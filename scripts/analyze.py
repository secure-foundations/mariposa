# from tqdm import tqdm
from path_utils import *
from wrap_utils import *
import math
import hashlib
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.pyplot import figure

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

def percent_change(curr, orig):
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
            print(org_res)
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

RC_KEY = "rlimit-count"
TT_KEY = "total-time"

def analyze_percent_change_thread(query_paths):
    rc_skipped = 0
    tt_skipped = 0

    rpcs_8_4 = list()
    rpcs_16_4 = list()

    tpcs_8_4 = list()
    raw_tpcs_8_4 = list()
    tpcs_16_4 = list()
    raw_tpcs_16_4 = list()

    for qp in query_paths:
        pers4 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/old/smtlib4/"))
        pers8 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/old/smtlib8/"))
        pers16 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/old/smtlib16/"))

        if pers4['rcode'] == RCode.Z3_R_TO:
            rc_skipped += 1
            tt_skipped += 1
            continue

        if RC_KEY in pers16 and RC_KEY in pers8 and RC_KEY in pers4:
            r4 = int(pers4[RC_KEY])
            r8 = int(pers8[RC_KEY])
            r16 = int(pers16[RC_KEY])

            rpc_8_4 = percent_change(r8, r4)
            rpcs_8_4.append(rpc_8_4)

            rpc_16_4 = percent_change(r16, r4)
            rpcs_16_4.append(rpc_16_4)
        else:
            rc_skipped += 1

        if TT_KEY in pers16 and TT_KEY in pers8 and TT_KEY in pers4:
            t4 = max(float(pers4[TT_KEY]), 0.01)
            t8 = max(float(pers8[TT_KEY]), 0.01)
            t16 = max(float(pers16[TT_KEY]), 0.01)

            pc_8_4 = percent_change(t8, t4)
            pc_16_4 = percent_change(t16, t4)

            if abs(t8 - t4) < 1:
                tpcs_8_4.append(0)
            else:
                tpcs_8_4.append(pc_8_4)

            if abs(t16 - t4) < 1:
                tpcs_16_4.append(0)
            else:
                tpcs_16_4.append(pc_16_4)
                if pc_16_4 > 100:
                    print(qp.orig)


            raw_tpcs_8_4.append(pc_8_4)
            raw_tpcs_16_4.append(pc_16_4)
        else:
            tt_skipped += 1

    print(rc_skipped, len(rpcs_8_4))
    print(tt_skipped, len(raw_tpcs_8_4))

    tpcs_16_4 = [400 if i >= 400 else i for i in tpcs_16_4]
    raw_tpcs_16_4 = [400 if i >= 400 else i for i in raw_tpcs_16_4]

    figure, axis = plt.subplots(3, 1)
    figure.set_figheight(15)
    figure.set_figwidth(10)

    assert len(rpcs_8_4) == len(rpcs_16_4)
    n = len(rpcs_8_4)
    y = np.arange(n) / float(n)

    sp = axis[0]
    sp.set_title('thread count impact on rlimit')
    sp.plot(np.sort(rpcs_8_4), y, marker=',', label='8 threads rlimit')
    sp.plot(np.sort(rpcs_16_4), y, marker=',', label='16 threads rlimit')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("percent change vs 4 threads baseline")
    sp.legend()

    assert len(raw_tpcs_8_4) == len(tpcs_16_4)
    n = len(raw_tpcs_8_4)
    y = np.arange(n) / float(n)

    sp = axis[1]
    sp.set_title('thread count impact on time (raw)')
    sp.plot(np.sort(raw_tpcs_8_4), y, marker=',', label='8 threads time')
    sp.plot(np.sort(raw_tpcs_16_4), y, marker=',', label='16 threads time')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("percent change vs 4 threads baseline")
    sp.legend()

    sp = axis[2]
    sp.set_title('thread count impact on time (smoothed)')
    sp.plot(np.sort(tpcs_8_4), y, marker=',', label='8 threads time')
    sp.plot(np.sort(tpcs_16_4), y, marker=',', label='16 threads time')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("percent change vs 4 threads baseline")
    sp.legend()

    plt.savefig("fig/percent_change")

from scipy.stats import gaussian_kde

def analyze_time_rlimit(query_paths):
    skipped = 0
    # np.array()
    xs = []
    ys = []
    for qp in query_paths:
        # pers = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/old/smtlib10K_rbound/"))
        pers = load_res_file(qp.plain_exp_res)

        if pers['rcode'] == RCode.Z3_R_TO:
            skipped += 1
            continue
        if int(pers[RC_KEY]) > 200000000:
            skipped += 1
            continue
        xs.append(float(pers[TT_KEY]))
        ys.append(int(pers[RC_KEY]))
    print(skipped, len(xs))
    
    xy = np.vstack([xs,ys])

    fig, ax = plt.subplots()
    z = gaussian_kde(xy)(xy)
    ax.scatter(xs, ys, c=z, marker=".")
    ax.set_title('rlimit and time (30s timeout)')
    ax.set_ylabel("rlimit")
    ax.set_xlabel("seconds")
    plt.savefig("fig/time_rlimit")

# def analyze_exp_res(query_paths):
#     # plain_exps = {k:0 for k in RCodes}
#     # normalize_exps = {k:0 for k in RCodes}
#     # shuffle_exps = {k:0 for k in RCodes}

#     skipped = 0
#     bad = 0
#     for qp in query_paths:
#         pers = load_res_file(qp.plain_exp_res)
#         # exps = qp.normalize_exps() + qp.mix_exps() + qp.shuffle_exps()
#         pers8 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/smtlib8/"))
#         pers16 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/smtlib16/"))

#         if "rlimit-count" in pers16 and "rlimit-count" in pers:
#             o = int(pers["rlimit-count"]) 
#             a = int(pers16["rlimit-count"])
#             pc = percent_change(a, o)
#             if pc > 50:
#                 print(pc)
#         else:
#             skipped += 1


#     print(f"total: {len(query_paths)}")
#     print(f"skipped: {skipped}")
#     print(f"bad: {bad}")

    # print_results("plain experiment", plain_exps)
    # print_results("normalize experiment", normalize_exps)
    # print_results("shuffle experiment", shuffle_exps)

if __name__ == "__main__":
    seeds = load_seeds_file("data/seeds/3_seeds")
    # query_paths = load_qlist("data/qlists/smtlib_rand100_sat", "seeds")
    # query_paths = load_qlist("data/qlists/dafny_rand1K", seeds)
    # query_paths = load_qlist("data/qlists/dafny_rand100", seeds)
    # query_paths = load_qlist("data/qlists/smtlib_rand1K_known", seeds)
    # analyze_percent_change_thread(query_paths)

    query_paths = load_qlist("data/qlists/smtlib_rand10K_known", seeds)
    analyze_time_rlimit(query_paths)
    # query_paths = load_qlist("data/qlists/smtlib_rand1K_sat")
