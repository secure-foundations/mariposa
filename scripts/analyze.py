# from tqdm import tqdm
from path_utils import *
from wrap_utils import *
from config_utils import *
import math
import hashlib
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.pyplot import figure
from matplotlib import ticker
from scipy.stats import gaussian_kde
import statistics

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

RL_KEY = "rlimit-count"
RC_KEY = "rcode"
TT_KEY = "total-time"

def load_res_file(path):
    stats = dict()
    for line in open(path).readlines():
        line = line.strip().split(",")
        key = line[0]
        if key == RL_KEY:
            stats[key] = int(line[1])
        elif key == TT_KEY:
            # assume at least take 0.01 second
            stats[TT_KEY] = max(float(line[1]), 0.01)
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

    # print(len(ratios), sum(ratios) / len(ratios))

    print_results("plain test", plain_tests)
    print_results("shuffle test", shuffle_tests)
    print_results("normalize test", normalize_tests)

# def compute_raw_score(qp, org_res, cur_res):
#     if org_res["rcode"] != RCode.Z3_R_US:
#         # print("cannot compute rscore: " + org_res["rcode"])
#         if cur_res["rcode"] != org_res["rcode"]:
#             print(org_res["rcode"], cur_res["rcode"])
#             print(org_res["rlimit-count"])
#             print(cur_res["rlimit-count"])
#             print(org_res)
#             print(qp.orig)
#         return None

#     org_rl = org_res["rlimit-count"]

#     if cur_res["rcode"] == RCode.Z3_R_TO:
#         return 5 * org_rl

#     if cur_res["rcode"] == RCode.Z3_R_US:
#         cur_rl = cur_res["rlimit-count"]
#         if (cur_rl > 2 * org_rl):
#             return 5 * org_rl
#         return cur_rl
#     elif cur_res["rcode"] == RCode.Z3_R_U:
#         cur_rl = cur_res["rlimit-count"]
#         if (cur_rl > 2 * org_rl):
#             return 5 * org_rl
#         return cur_rl + 2 * org_rl
#     else:
#         return None

# def compute_rscore(qp, org_res, cur_res):
#     rrs = compute_raw_score(qp, org_res, cur_res)
#     if rrs == None:
#         return None
#     else:
#         rl_5x = 5 * org_res["rlimit-count"]
#         return  (rl_5x -  rrs) / rl_5x

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


def res_percent_change(curr, orig, key):
    if key not in curr or key not in orig:
        return None
    return percent_change(curr[key], orig[key])

def res_raw_change(curr, orig, key):
    if key not in curr or key not in orig:
        return None
    return (curr[key] - orig[key])

def plot_cdf(sp, data, label):
    n = len(data)
    y = np.arange(n) / float(n)
    label = label + f" ({len(data)})"
    sp.plot(np.sort(data), y, marker=',', label=label)

def append_if_some(l, v):
    if v is not None:
        l.append(v)

def load_changes(query_paths, alt):
    rpcs = list()
    racs = list()
    tpcs = list()
    tacs = list()

    for qp in query_paths:
        pers4 = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", "gen/smtlib_4t_60s/"))
        pers = load_res_file(qp.plain_exp_res.replace("gen/smtlib/", alt))
        append_if_some(rpcs, res_percent_change(pers, pers4, RL_KEY))
        append_if_some(racs, res_raw_change(pers, pers4, RL_KEY))
        append_if_some(tpcs, res_percent_change(pers, pers4, TT_KEY))
        append_if_some(tacs, res_raw_change(pers, pers4, TT_KEY))

    return rpcs, racs, tpcs, tacs

def analyze_perf_change_thread():
    rc_skipped = 0
    tt_skipped = 0
    qlist = "data/qlists/smtlib_rand1K_known"
    query_paths = load_qlist(qlist, [])

    rpcs_7_4, racs_7_4, tpcs_7_4, tacs_7_4 = load_changes(query_paths, "gen/smtlib_7t_60s/")
    rpcs_8_4, racs_8_4, tpcs_8_4, tacs_8_4 = load_changes(query_paths, "gen/smtlib_8t_60s/")
    rpcs_16_4, racs_16_4, tpcs_16_4, tacs_16_4 = load_changes(query_paths, "gen/smtlib_16t_60s/")

    figure, axis = plt.subplots(4, 1)
    figure.set_figheight(20)
    figure.set_figwidth(10)

    sp = axis[0]
    sp.set_title('thread count impact on rlimit (percent change)')
    plot_cdf(sp, rpcs_7_4, '7 threads rlimit')
    plot_cdf(sp, rpcs_8_4, '8 threads rlimit')
    plot_cdf(sp, rpcs_16_4, '16 threads rlimit')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("percent change vs 4 threads baseline")
    sp.legend()

    sp = axis[1]
    sp.set_title('thread count impact on rlimit (raw change)')
    plot_cdf(sp, racs_7_4, '7 threads rlimit')
    plot_cdf(sp, racs_8_4, '8 threads rlimit')
    plot_cdf(sp, racs_16_4, '16 threads rlimit')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("raw change vs 4 threads baseline")
    sp.legend()

    sp = axis[2]
    sp.set_title('thread count impact on time (percent change)')
    plot_cdf(sp, tpcs_7_4, '7 threads time')
    plot_cdf(sp, tpcs_8_4, '8 threads time')
    plot_cdf(sp, tpcs_16_4, '16 threads time')
    sp.set_ylabel("cumulative probability")
    sp.set_xlabel("percent change vs 4 threads baseline")
    sp.legend()

    sp = axis[3]
    sp.set_title('thread count impact on time (raw change)')
    plot_cdf(sp, tacs_7_4, '7 threads time')
    plot_cdf(sp, tacs_8_4, '8 threads time')
    plot_cdf(sp, tacs_16_4, '16 threads time')
    sp.set_ylabel("cumulative probability")
    # sp.set_xscale("log")
    sp.set_xlabel("raw seconds change vs 4 threads baseline")
    sp.legend()
    text = f"""
data set:
        {qlist}
total queries count:
    {len(query_paths)}
"""
    figure.text(0.1, 0.05, text, wrap=False)
    plt.savefig("fig/thread_count_perf_change")

def analyze_time_rlimit_correlation():
    qlist = "data/qlists/smtlib_rand10K_known"
    qpaths = load_qlist(qlist, prefix="gen/smtlib_10K_120s_TO/", seeds=[], trials=1)
    tskipped = 0
    rskipped = 0

    xs = []
    ys = []
    for qp in qpaths:
        ptg = qp.plain_tg
        assert(len(ptg.ress) == 1)
        for resf in ptg.ress:
            resf = resf.replace("smtlib/", "", 1)
            try:
                res = load_res_file(resf)
                xs.append(res[TT_KEY])
                ys.append(res[RL_KEY])
            except:
                print(resf)
                print("oops")

    xy = np.vstack([xs,ys])

    fig, ax = plt.subplots()
    z = gaussian_kde(xy)(xy)
    ax.scatter(xs, ys, c=z, marker=".")
    ax.set_title(f'rlimit and time (120s timeout)\n over {qlist}')
    ax.set_ylabel("rlimit")
    text = f"""
data set:
    {qlist}
total queries count:
    {len(qpaths)}
thread count:
    8

skipped queries (200000000 rlimit):
    {rskipped}
"""
    ax.set_xlabel(text, x=0, horizontalalignment='left')
    plt.savefig("fig/time_rlimit", bbox_inches='tight')

# def analyze_time_distribution():
#     qlist = "data/qlists/smtlib_rand10K_known_30s_TO"
#     query_paths = load_qlist(qlist, [])
#     xs = []

#     for qp in query_paths:
#         pers = load_res_file(qp.plain_exp_res.replace("gen/smtlib", "gen/smtlib_10K_TO_30_120s"))
#         if pers[RC_KEY] == RCode.Z3_R_TO:
#             xs.append(120)
#         else:
#             xs.append(pers[TT_KEY])

#     qlist = "data/qlists/smtlib_rand10K_known"

#     query_paths = load_qlist(qlist, [])

#     for qp in query_paths:
#         pers = load_res_file(qp.plain_exp_res.replace("gen/smtlib", "gen/smtlib_10K_tbound"))
#         if pers[RC_KEY] == RCode.Z3_R_TO:
#             pass
#         else:
#             xs.append(pers[TT_KEY])

    # plt.title(f"time cdf on {qlist} (120s)")
    # plot_cdf(plt, xs, "all")
    # # xs = list(filter(lambda x: x >= 1, xs))
    # # plot_cdf(plt, xs, "1 second and above")
    # plt.legend()
    # plt.ylabel("cumulative probability")
    # # plt.xscale("log", basex=2)
    # plt.savefig("fig/time_cdf")

def compute_deviation(r_scores):
    vs = []
    for r_score in r_scores:
        v = abs(r_score - 0.8)
        vs.append(v * v)
    s = sum(vs) / len(r_scores)
    return math.sqrt(s)

def rlimit_fmt(x, pos): # your custom formatter function: divide by 100.0
    s = '{}e6'.format(x / 1000000)
    return s

def analyze_perf_consistency():
    qpaths = load_qlist(CONSISTENCY_EXP_CONFIG)

    time_sds = []
    rlimit_sds = []

    for qp in qpaths:
        ptg = qp.plain_tg
        times = []
        rlimits = []
        for resf in ptg.ress:
            res = load_res_file(resf)
            times.append(res[TT_KEY])
            rlimits.append(res[RL_KEY])
        assert(len(times) == len(rlimits) == 4)
        sd = statistics.stdev(times)
        time_sds.append(round(sd, 4))
        sd = statistics.stdev(rlimits)
        rlimit_sds.append(sd)

    figure, axis = plt.subplots(2, 1)
    figure.set_figheight(10)
    figure.set_figwidth(10)

    sp = axis[0]
    sp.set_title('histrgram of standard deviation of run time')
    sp.hist(time_sds, 100)
    sp.set_ylabel("count")
    sp.set_xlabel("seconds (30 seconds timeout)")

    sp = axis[1]
    sp.set_title('histrgram of standard deviation of rlimit-count')
    sp.hist(rlimit_sds, 100)
    sp.set_ylabel("count")
    xfmt = ticker.FuncFormatter(rlimit_fmt)
    sp.xaxis.set_major_formatter(xfmt)
    sp.set_xlabel("rlimit (3.0e6 cosidered 1 second)\n\n" + str(CONSISTENCY_EXP_CONFIG), x=0, horizontalalignment='left')
    plt.savefig("fig/perf_std")

def analyze_exp_res(query_paths):
    for qp in query_paths:
        pers = load_res_file(qp.plain_exp_res)
        exps = qp.normalize_exps() + qp.shuffle_exps() + qp.mix_exps()
        flip_count = 0
        print(ers[RC_KEY])

        for exp in exps:
            ers = load_res_file(exp.res)
            print(ers[RC_KEY])
            # if ers[RC_KEY] in {RCode.MP_GSE_EP, RCode.MP_GNE_EP, RCode.MP_GME_EP}:
            #     print("oh no")
            #     continue
            # if ers[RC_KEY] != pers[RC_KEY]:
            #     print(qp.orig)
            #     print(exp.exp)
            #     print(pers)
            #     print(ers)
            #     flip_count += 1
            #     print("")
        # if flip_count != 0:
        #     print(flip_count)

    # print_results("plain experiment", plain_exps)
    # print_results("normalize experiment", normalize_exps)
    # print_results("shuffle experiment", shuffle_exps)

# def get_timeout_qlist():
#     qlist = "data/qlists/smtlib_rand10K_known"
#     query_paths = load_qlist(qlist, [])
#     timeouts = []

#     for qp in query_paths:
#         pers = load_res_file(qp.plain_exp_res.replace("gen/smtlib", "gen/smtlib_10K_tbound"))
#         if pers[RC_KEY] == RCode.Z3_R_TO:
#             print(qp.orig)

if __name__ == "__main__":
    # analyze_perf_change_thread()
    # analyze_time_rlimit_correlation()
    # analyze_time_distribution()
    # get_timeout_qlist()
    analyze_perf_consistency()

