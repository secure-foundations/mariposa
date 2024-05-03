#!/usr/bin/env python3

import argparse
from analysis.core_analyzer import CoreAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.defs import MARIPOSA, MARIPOSA_GROUPS
from base.factory import FACT
from base.project import KnownExt, Project, ProjectType as PT
from base.query_analyzer import Stability as STB
from base.solver import RCode
from utils.analysis_utils import Categorizer, PartialCDF
from utils.cache_utils import load_cache, load_cache_or, save_cache
from utils.option_utils import deep_parse_args
from utils.system_utils import log_info, log_warn, subprocess_run
from utils.plot_utils import *
import random
from matplotlib import pyplot as plt
import numpy as np
from tqdm import tqdm

def handle_create_benchmark():
    ana = FACT.get_analyzer("60nq")
    random.seed(1342681237269884202)

    for gid in MARIPOSA_GROUPS:
        group = FACT.get_group(gid)
        proj = group.get_project(PT.from_str("base.z3"))
        exp = FACT.load_any_analysis(proj, ana)
        # print(len(exp.get_overall()[STB.STABLE].items))
        qids = random.sample(exp.get_overall()[STB.STABLE].items, 110)
        for qid in qids:
            i = proj.get_path(qid)
            o = f"data/projs/bench_stable/base.z3/{gid}--{qid}.smt2"
            print(f"{MARIPOSA} -a add-ids -i {i} -o {o}")


BU_GID = "bench_unstable"
BS_GID = "bench_stable"

def handle_core_analysis():
    # buc = CoreAnalyzer(FACT.get_group(BU_GID))
    # buc.print_status()
    # bsc = CoreAnalyzer(FACT.get_group(BS_GID))
    # bsc.print_status()

    for gid in MARIPOSA_GROUPS:
        ca = CoreAnalyzer(FACT.get_group(gid))
        counts = load_cache_or(f"{gid}_asserts", ca.get_assert_counts)
        ratios = counts[:,1] * 100 / counts[:,0]
        ratios = PartialCDF(ratios)
        # print(gid)
        # print(counts)
        pm = GROUP_PLOT_META[gid]
        plt.plot(ratios.xs, ratios.ys, label=pm.tex_name, color=pm.color)
        p50 = ratios.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
        if gid != "d_lvbkv" and gid != "d_fvbkv":
            plt.text(p50[0] * 1.15, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
        else:
            plt.text(p50[0] * 0.55, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
    
    plt.legend()
    plt.xlabel("Query Relevance Ratio (\%)")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))
    # plt.xlim(0, 100)
    plt.ylim(0, 100)
    plt.xscale("log")
    plt.grid()
    plt.savefig(f"fig/overall_RR.pdf")

# def handle_quantifier_count():
#     for gid in MARIPOSA_GROUPS:
#         p = FACT.get_group(gid).get_project("base.z3")
#         counts = load_cache_or(f"{gid}_assert_count", lambda: p.get_assert_stats())
#         counts = np.array(counts)
#         ratios = 100 - counts[:,0] * 100 / counts[:,1]
#         data = PartialCDF(ratios)
#         plt.plot(data.xs, data.ys, label=GROUP_PLOT_META[gid].tex_name, color=GROUP_PLOT_META[gid].color)
#         p50 = data.valid_median
#         plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
#         if gid == "d_fvbkv":
#             plt.text(p50[0]+1, p50[1]+1, f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
#         if gid == "fs_vwasm" or gid == "fs_dice":
#             plt.text(p50[0]-5, p50[1]+1, f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
#         # if gid == "d_komodo":
#         #     plt.text(p50[0]-5, p50[1]-2, f"{round(p50[0], 2)}\%", fontsize=8, va="top")

#     plt.grid()
#     plt.yticks(np.arange(0, 101, 10))
#     plt.ylim(0, 100)
#     # plt.xscale("log")
#     plt.legend()
#     plt.xlabel("Quantified Assertion Ratio (\%)")
#     plt.ylabel("CDF (\%)")
#     plt.savefig("fig/qf_assert_ratio.pdf")

def handle_quantifier_count():
    for gid in MARIPOSA_GROUPS:
        p = FACT.get_group(gid).get_project("base.z3")
        p.get_quantifier_stats()
        break

def handle_shake_analysis2():
    from scipy.stats import gaussian_kde

    ana = FACT.get_analyzer("60nq")
    shko = FACT.load_any_analysis(FACT.get_group(BU_GID).get_project("shko.z3"), ana)
    # exp.print_status()
    base = FACT.load_any_analysis(FACT.get_group(BU_GID).get_project("base.z3"), ana)

    bcats = Categorizer()
    scats = Categorizer()
    ratios = []
    for qid in base.qids:
        # bs, bm = base[qid].get_original_status()
        # bcats.add_item(RCode(bs), qid)
        # ss, sm = shko[qid].get_original_status()
        # ratios += [[sm, bm]]
        # scats.add_item(RCode(ss), qid)
        bm = base[qid].get_mean_time()
        sm = shko[qid].get_mean_time()
        ratios += [[sm, bm]]
        

    ratios = np.array(ratios)
    # plt.scatter(ratios[:,0], ratios[:,1], alpha=0.5)
    x = ratios[:,0]
    y = ratios[:,1]

    xy = np.vstack([x,y])
    z = gaussian_kde(xy)(xy)
    plt.scatter(ratios[:,0], ratios[:,1], c=z, s=10)

    # plt.xlabel("Shake Status")
    # plt.ylabel("Base Status")
    # plt.hist(ratios[:,1] / ratios[:,0], bins=100)
    # cdf = PartialCDF(ratios[:,0] / ratios[:,1])
    
    # plt.plot(cdf.xs, cdf.ys)
    # p50 = cdf.valid_median
    # plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
    # plt.text(p50[0], p50[1], f"{round(p50[0], 2)}", fontsize=8, va="bottom")
    # p90 = cdf.get_point_by_percent(90, True)
    # plt.plot(p90[0], p90[1], c="black", marker="o", markersize=3)
    # plt.text(p90[0], p90[1], f"{round(p90[0], 2)}", fontsize=8, va="bottom")
    # p10 = cdf.get_point_by_percent(10, True)
    # plt.plot(p10[0], p10[1], c="black", marker="o", markersize=3)
    # plt.text(p10[0], p10[1], f"{round(p10[0], 2)}", fontsize=8, va="bottom")
    
    # plt.xscale("log")
    # plt.ylim(0, 100)
    # plt.yticks(np.arange(0, 101, 10))
    plt.xscale("log")
    plt.yscale("log")
    plt.plot([10, 6e4], [10, 6e4], color="black", linestyle="--")
    plt.gca().set_aspect('equal')

    plt.grid()
    plt.savefig("fig/shake_ratio.pdf")

    bcats.finalize()
    scats.finalize()

    bcats.print_status()
    scats.print_status()
        # print(f"{bm},{bs},{sm},{ss}")

    # simp = FACT.load_any_analysis(FACT.get_group("bench_unstable_simp").get_project("shko.z3"), ana)
    # # simp.print_status()
    
    # cc = exp.stability_categories
    # sc = simp.stability_categories

    # mc = sc.get_migration_status(cc)
    # for k, v in mc.items():
    #     print(f"{k}")
    #     v.print_status()

    # exp = FACT.load_any_analysis(FACT.get_group(BS_GID).get_project("shko.z3"), ana)
    # exp.print_status()

def handle_shake_analysis():
    ana = FACT.get_analyzer("60nq")
    group = FACT.get_group("d_komodo")
    base = FACT.load_any_analysis(group.get_project("base.z3"), ana)
    base.print_plain_status()    
    # shko = group.get_project("shko.z3")

    # for qid in base.stability_categories[STB.UNSOLVABLE].items:
    #     print(shko.get_path(qid))
    #     # print(qid)
    #     base_path = base.get_path(qid)
    #     shake_log = base.get_path(qid, KnownExt.SHK_LOG)

    #     # print(
    #     #     "./src/query_wizard.py debug-shake",
    #     #     "-i %s --core-query-path %s --input-log-path %s"
    #     #     % (base_path, base_path, shake_log),
    #     # )
    #     print(
    #         "cp %s tmp/woot.smt2"
    #         (base_path),
    #     )

def handle_shake_time_analysis():
    ana = FACT.get_analyzer("60nq")
    base = FACT.load_any_analysis(FACT.get_group(BS_GID).get_project("base.z3"), ana)

    # for qid in base.qids:
    #     path = base.get_path(qid)
    #     o = subprocess_run(f"{MARIPOSA} -a shake -i {path}", shell=True)[0]
    #     o = o.split("\n")
    #     assert len(o) == 2
    #     parse_time = int(o[0].split(": ")[-1])
    #     shake_time = int(o[1].split(": ")[-1])
    #     print(f"{qid},{parse_time},{shake_time}")

    dps = []
    for line in open("doc/stable_shake_time"):
        line = line.strip().split(",")
        qid = line[0]
        m = base[qid].get_mean_time()
        dps.append((int(line[1]), int(line[2]), m))

    dps = np.array(dps)
    dps = np.sort(dps, axis=0)
    
    for i in range(0, len(dps)):
        if i != 0:
            plt.bar(i, dps[i,1], color="blue", alpha=0.5)
            plt.bar(i, dps[i,0], bottom=dps[i,1], color="red", alpha=0.5)
            plt.bar(i, dps[i,2], color="green", alpha=0.5)
        else:
            plt.bar(i, dps[i,1], color="blue", alpha=0.5, label="shake")
            plt.bar(i, dps[i,0], bottom=dps[i,1], color="red", alpha=0.5, label="parse")
            plt.bar(i, dps[i,2], color="green", alpha=0.5, label="solve (success mean)")

    print(np.median(dps[i,0]/dps[i,2]))
    # # plt.yticks(np.arange(0, 101, 10))
    plt.xlim(0)
    # plt.xticks([])
    # plt.ylim(0, 1000)
    # # plt.xlabel("Ratio")
    plt.ylabel("time (ms)")
    plt.xlabel("queries (sorted by solve time)")
    plt.legend()
    # # plt.grid()
    plt.savefig("fig/shake_stable_time.pdf")

def handle_wombo_analysis():
    wuc = WomboAnalyzer(FACT.get_group(BU_GID))
    wuc.temp.print_status()
    wsc = WomboAnalyzer(FACT.get_group(BS_GID))
    wsc.temp.print_status()

    u_ic = load_cache_or("wombo_unstable_insts", lambda: wuc.get_inst_stats())[1]
    s_ic = load_cache_or("wombo_stable_insts", lambda: wsc.get_inst_stats())[1]

    u_ic = PartialCDF(u_ic)
    s_ic = PartialCDF(s_ic)

    plt.plot(u_ic.xs, u_ic.ys, label="unstable")
    p50 = u_ic.valid_median
    plt.plot(p50[0], p50[1], "black", marker="o")
    plt.text(p50[0] + 10, p50[1], f"{int(p50[0])}", fontsize=8, va="bottom")
    p90 = u_ic.get_point_by_percent(90, True)
    plt.plot(p90[0], p90[1], "black", marker="o")
    plt.text(p90[0] + 10, p90[1], f"{int(p90[0])}", fontsize=8, va="bottom")
    no_ic = u_ic.get_point_by_value(0, True)
    plt.plot(no_ic[0], no_ic[1], "black", marker="*")

    plt.plot(s_ic.xs, s_ic.ys, label="stable")
    p50 = s_ic.valid_median
    plt.plot(p50[0], p50[1], "black", marker="o")
    plt.text(p50[0] + 10, p50[1], f"{int(p50[0])}", fontsize=8,va="bottom",)
    p90 = s_ic.get_point_by_percent(90, True)
    plt.plot(p90[0], p90[1], "black", marker="o")
    plt.text(p90[0] + 10, p90[1], f"{int(p90[0])}", fontsize=8, va="bottom")

    no_ic = s_ic.get_point_by_value(0, True)
    plt.plot(no_ic[0], no_ic[1], "black", marker="*")

    plt.xlabel("Instance Count at Convergence")
    plt.ylabel("CDF (\%)")

    plt.yticks(np.arange(0, 101, 10))
    plt.xlim(0, 800)
    plt.ylim(0, 100)
    plt.legend()
    plt.grid()
    plt.savefig("fig/wombo_combo.pdf")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Mariposa Meta Wizard operates on multiple projects."
    )
    subparsers = parser.add_subparsers(
        dest="sub_command", help="the sub-command to run"
    )

    subparsers.add_parser("bench", help="create benchmark projects")
    subparsers.add_parser("core", help="analyze core")
    subparsers.add_parser("wombo", help="analyze wombo")
    subparsers.add_parser("shake", help="analyze shake")
    subparsers.add_parser("stat", help="analyze quantifier count")
    subparsers.add_parser("shake-time", help="analyze shake time")

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "bench":
        handle_create_benchmark()
    elif args.sub_command == "core":
        handle_core_analysis()
    elif args.sub_command == "shake":
        handle_shake_analysis()
    elif args.sub_command == "shake-time":
        handle_shake_time_analysis()
    elif args.sub_command == "wombo":
        handle_wombo_analysis()
    elif args.sub_command == "stat":
        handle_quantifier_count()
