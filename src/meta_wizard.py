#!/usr/bin/env python3

import argparse
from analysis.core_analyzer import CoreAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.defs import MARIPOSA, MARIPOSA_GROUPS
from base.factory import FACT
from base.project import KnownExt, Project, ProjectType as PT
from base.query_analyzer import Stability as STB
from utils.analysis_utils import PartialCDF
from utils.cache_utils import load_cache, load_cache_or, save_cache
from utils.option_utils import deep_parse_args
from utils.system_utils import log_info, log_warn
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

def handle_shake_analysis():
    ana = FACT.get_analyzer("60nq")
    exp = FACT.load_any_analysis(FACT.get_group(BU_GID).get_project("shko.z3"), ana)
    exp.print_status()

    exp = FACT.load_any_analysis(FACT.get_group(BS_GID).get_project("shko.z3"), ana)
    exp.print_status()

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

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "bench":
        handle_create_benchmark()
    elif args.sub_command == "core":
        handle_core_analysis()
    elif args.sub_command == "shake":
        handle_shake_analysis()
    elif args.sub_command == "wombo":
        handle_wombo_analysis()
    elif args.sub_command == "stat":
        handle_quantifier_count()
