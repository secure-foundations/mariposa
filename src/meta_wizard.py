#!/usr/bin/env python3

import argparse
import multiprocessing
import os
from analysis.shake_context import handle_shake_depth_analysis, handle_core_context_analysis, handle_shake_context_analysis
from analysis.core_analyzer import CoreAnalyzer
from analysis.shake_stability import handle_core_stability_analysis, handle_shake_stability_analysis
from analysis.shake_survivial import get_shake_times, handle_shake_survival
from analysis.wombo_analyzer import WomboAnalyzer
from base.defs import MARIPOSA, MARIPOSA_GROUPS
from base.exper_analyzer import QueryAnaResult
from base.factory import FACT
from base.project import KnownExt, Project, ProjectType as PT
from base.query_analyzer import Stability as STB
from base.solver import RCode
from utils.analysis_utils import Categorizer, PartialCDF
from utils.cache_utils import has_cache, load_cache, load_cache_or, save_cache
from utils.option_utils import deep_parse_args
from utils.query_utils import count_asserts, normalize_line
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

def handle_shake_cvc5(gid):
    ana = FACT.get_analyzer("60nq")
    group = FACT.get_group(gid)
    proj = group.get_project("base.cvc5")
    exp = FACT.load_any_analysis(proj, ana)
    for qid in exp.qids:
        qr = exp[qid]
        rc, et = qr.get_original_status()
        if rc == RCode.UNSAT.value and et < 6e4:
            i = proj.get_path(qid)
            o = f"data/projs/pre_cvc5/base.cvc5/{gid}--{qid}.smt2"
            # print(f"{MARIPOSA} -a add-ids -i {i} -o {o} --reassign-ids")
            print(f"cp {i} {o}")

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

def fix_query_cids(args):
    (new_base_f, old_base_f, new_query) = args

    if os.path.exists(new_query + ".fixed"):
        return
    
    new_base = open(new_base_f, "r").readlines()
    old_base = []
    for line in open(old_base_f, "r").readlines():
        if not line.startswith("(set-info"):
            old_base.append(line)
    mapping = dict()

    if len(new_base) != len(old_base):
        print(new_base_f, len(new_base), old_base_f, len(old_base), new_query)
        assert False

    for i in range(len(old_base)):
        old = old_base[i]
        new = new_base[i].strip()
        if old.startswith("(assert"):
            old = normalize_line(old)
            assert new.startswith("(assert")
            mapping[old] = new
    
    fixed_query = open(new_query + ".fixed", "w+")
    new_query = open(new_query, "r").readlines()

    for i in range(len(new_query)):
        woo = new_query[i].strip()
        if woo.startswith("(assert"):
            woo = normalize_line(woo)
            assert woo in mapping
            fixed_query.write(mapping[woo] + "\n")
        else:
            fixed_query.write(woo + "\n")
    fixed_query.close()

def fix_cids(gid):
    group = FACT.get_group(gid)
    qid_group = FACT.get_group(gid + ".qids")

    base = group.get_project("base.z3")
    core = group.get_project("core.z3")
    extd = group.get_project("extd.z3")
    
    cids = qid_group.get_project("base.z3")

    args = []

    for qid in core.qids:
        cids_path = cids.get_path(qid)
        base_path = base.get_path(qid)
        core_path = core.get_path(qid)
        args.append((base_path, cids_path, core_path))

    for qid in extd.qids:
        cids_path = cids.get_path(qid)
        base_path = base.get_path(qid)
        core_path = extd.get_path(qid)
        args.append((base_path, cids_path, core_path))

    pool = multiprocessing.Pool(7)
    pool.map(fix_query_cids, args)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Mariposa Meta Wizard operates on multiple projects."
    )
    subparsers = parser.add_subparsers(
        dest="sub_command", help="the sub-command to run"
    )

    subparsers.add_parser("bench", help="create benchmark projects")
    subparsers.add_parser("core-ctx", help="analyze core")
    subparsers.add_parser("core-stb", help="analyze core")
    subparsers.add_parser("wombo", help="analyze wombo")
    subparsers.add_parser("shake", help="analyze shake")
    subparsers.add_parser("stat", help="analyze quantifier count")
    subparsers.add_parser("shake-time", help="analyze shake time")
    subparsers.add_parser("fix-cids", help="fix cid in queries")
    subparsers.add_parser("shake-ctx", help="analyze shake ctx")
    subparsers.add_parser("shake-depth", help="analyze shake depth")
    subparsers.add_parser("shake-stb", help="analyze shake stability")

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "bench":
        handle_create_benchmark()
    elif args.sub_command == "core-ctx":
        handle_core_context_analysis()
    elif args.sub_command == "core-stb":
        handle_core_stability_analysis()
    elif args.sub_command == "shake":
        for gid in MARIPOSA_GROUPS:
            handle_shake_survival(gid)
            # handle_shake_cvc5(gid)
    elif args.sub_command == "shake-stb":
        handle_shake_stability_analysis()
    elif args.sub_command == "shake-time":
        for gid in MARIPOSA_GROUPS:
            get_shake_times(gid)
    elif args.sub_command == "shake-ctx":
        handle_shake_context_analysis()
    elif args.sub_command == "shake-depth":
        handle_shake_depth_analysis()
    elif args.sub_command == "wombo":
        handle_wombo_analysis()
    elif args.sub_command == "fix-cids":
        for gid in MARIPOSA_GROUPS:
            fix_cids(gid)
