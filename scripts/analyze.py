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
import seaborn as sns

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
            stats[key] = round(float(line[1]), 0)
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

def plot_scatter(sp, points, label):
    count = len(points)
    sp.scatter(points[::,0], points[::,1], label=f"{label}:{count}")
    return count

def plot_scatters(sp, dataset):
    count = 0
    for (pts, label) in dataset:
        count += plot_scatter(sp, pts, label)
    return count

def plot_linear_reg(sp, points, label):
    xs = points[::,0]
    ys = points[::,1]
    A = np.vstack([xs, np.ones(len(xs))]).T
    m, c = np.linalg.lstsq(A, ys, rcond=None)[0]
    plot_scatter(sp, points, label)
    sp.plot(xs, m*xs + c, label=f'rc = {round(m, 2)} * t + {round(c, 2)}')
    return len(xs)

def filter_pts(points, time=None, rcount=None):
    results = []
    for pt in points:
        if (rcount != None and pt[1] <= rcount) or (time != None and pt[0] <= time):
            results.append(pt)
    return np.array(results)

def analyze_time_rlimit_common():
    config = TIME_RLIMIT_CORRELATION_CONFIG
    qpaths = load_qlist(config)

    pts_sat = []
    pts_unsat = []
    pts_unknown = []
    pts_timeout = []
    z3_error = 0

    for i, qp in enumerate(qpaths):
        ptg = qp.plain_tg
        assert(len(ptg.ress) == 1)
        res = load_res_file(ptg.ress[0])
        code = res[RC_KEY]
        if code == RCode.Z3_R_ESF:
            z3_error += 1
            continue
        point = [res[TT_KEY], res[RL_KEY]]
        if code == RCode.Z3_R_S:
            pts_sat.append(point)
        elif code == RCode.Z3_R_US:
            pts_unsat.append(point)
        elif code == RCode.Z3_R_U:
            pts_unknown.append(point)
        else:
            pts_timeout.append(point)
            assert code == RCode.Z3_R_TO

    pts_sat = np.array(pts_sat)
    pts_unsat = np.array(pts_unsat)
    pts_unknown = np.array(pts_unknown)
    pts_timeout = np.array(pts_timeout)

    return (pts_sat, pts_unsat, pts_unknown, pts_timeout)

def analyze_time_rlimit_correlation():
    config = TIME_RLIMIT_CORRELATION_CONFIG

    def sp_finish_up(sp):
        sp.legend()
        sp.set_ylabel("rlimit-count")
        sp.set_xlabel("seconds")

    pts_sat, pts_unsat, pts_unknown, pts_timeout = analyze_time_rlimit_common()

    figure, axis = plt.subplots(4, 1)
    figure.set_figheight(25)
    figure.set_figwidth(10)

    sp = axis[0]
    ds = [(pts_sat, "sat"), (pts_unsat, "unsat"), (pts_unknown, "unknown"), (pts_timeout, "timeout")]
    count = plot_scatters(sp, ds)
    sp.set_title(f"rlimit-count vs time (180 seconds TO) {count} queries")
    sp_finish_up(sp)

    sp = axis[1]
    ds = [(pts_sat, "sat"), (pts_unsat, "unsat"), (pts_unknown, "unknown")]
    count = plot_scatters(sp, ds)
    sp.set_title(f"rlimit-count vs time (excluded: TO) {count} queries")
    sp_finish_up(sp)

    sp = axis[2]
    count = plot_linear_reg(sp, pts_sat, "sat")
    count += plot_linear_reg(sp, pts_unsat, "unsat")
    sp.set_title(f"rlimit-count vs time (excluded: TO, U) {count} queries")
    sp_finish_up(sp)

    sp = axis[3]
    pts_sat_ = filter_pts(pts_sat, time=30)
    pts_unsat_ = filter_pts(pts_unsat, time=30)
    # pts_unknown_ = filter_pts(pts_unknown, time=30)
    count = plot_linear_reg(sp, pts_sat_, "sat")
    count += plot_linear_reg(sp, pts_unsat_, "unsat")
    # count += plot_linear_reg(sp, pts_unknown_, "unknown")
    sp.set_title(f"rlimit-count vs time (excluded: >30s, U) {count} queries")
    sp_finish_up(sp)

    figure.text(0.1,0.92,str(config) + "z3 errors:" + str(z3_error), ha="left")

    plt.savefig("fig/time_rlimit", bbox_inches='tight')

def analyze_time_result_distribution():
    pts_sat, pts_unsat, pts_unknown, pts_timeout = analyze_time_rlimit_common()
    pts_sat = pts_sat[::,0]
    pts_unsat = pts_unsat[::,0]
    pts_unknown = pts_unknown[::,0]
    pts_timeout = pts_timeout[::,0]
    data = {"sat": pts_sat, "unsat" :pts_unsat, "unknown": pts_unknown, "timeout": pts_timeout}

    sns.histplot(data, label='sat', bins=180, multiple="stack")
    plt.savefig("fig/time_result", bbox_inches='tight')

def compute_deviation(r_scores):
    vs = []
    for r_score in r_scores:
        v = abs(r_score - 0.8)
        vs.append(v * v)
    s = sum(vs) / len(r_scores)
    return math.sqrt(s)

def rlimit_fmt(x, pos): 
    s = '{}e6'.format(x / 1000000)
    return s

def analyze_perf_consistency():
    config = CONSISTENCY_EXP_CONFIG
    qpaths = load_qlist(config)

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
    sp.set_xlabel("rlimit (3.0e6 cosidered 1 second)\n\n" + str(config), x=0, horizontalalignment='left')
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
    analyze_time_result_distribution()
    # get_timeout_qlist()
    # analyze_perf_consistency()

