#!/usr/bin/env python3

import argparse
from analysis.core_analyzer import CoreAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.defs import MARIPOSA, MARIPOSA_GROUPS
from base.factory import FACT
from base.project import ProjectType as PT
from base.query_analyzer import Stability as STB
from utils.analysis_utils import PartialCDF
from utils.cache_utils import load_cache, load_cache_or, save_cache
from utils.option_utils import deep_parse_args
from utils.system_utils import log_info, log_warn
import random
from matplotlib import pyplot as plt
import numpy as np


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
    buc = CoreAnalyzer(FACT.get_group(BU_GID))
    buc.print_status()

    bsc = CoreAnalyzer(FACT.get_group(BS_GID))
    bsc.print_status()


def handle_shake_analysis():
    pass


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
    plt.ylabel("CDF (%)")

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
