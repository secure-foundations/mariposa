#!/usr/bin/env python3

import argparse
import multiprocessing
import os
from analysis.shake_context import handle_shake_create, handle_shake_depth_analysis, handle_core_context_analysis, handle_shake_context_analysis
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


def plot_stability_impact():
    # 1 len(base_stable),
    # 2 len(core_stable),
    # 3 len(base_unstable),
    # 4 len(core_unstable),
    # 5 len(base_unstable & core_stable),
    # 6 len(base_stable & core_stable),

    # data = {
    #     "d_komodo": [2054, 1914, 1986, 93, 21, 84, 1902],
    #     "d_fvbkv":  [5170, 4983, 5071, 172, 84, 111, 4960],
    #     "d_lvbkv":  [5334, 4999, 5191, 256, 64, 214, 4977],
    #     "fs_dice":  [1536, 1483, 1495, 20, 8, 18, 1477],
    #     "fs_vwasm": [1755, 1731, 1728, 4, 7, 0, 1728],
    # }

    data_core_z3 = {
        "d_komodo": [93, 84, 1986, 1902],
        "d_fvbkv": [172, 111, 5071, 4960],
        "d_lvbkv": [256, 214, 5191, 4977],
        "fs_dice": [20, 18, 1495, 1477],
        "fs_vwasm": [4, 0, 1728, 1728],
    }

    data_shake_z3 = {
        "d_komodo": [93, 23, 110, 110],
        "d_fvbkv": [172, 40, 110, 108],
        "d_lvbkv": [256, 97, 110, 110],
        "fs_dice": [20, 4, 110, 110],
        "fs_vwasm": [4, 0, 110, 106],
    }

    data_naive_shake_z3 = {
        "d_komodo": [93, 7, 110, 109],
        "d_fvbkv": [172, 21, 110, 110],
        "d_lvbkv": [256, 30, 110, 110],
        "fs_dice": [20, 2, 110, 110],
        "fs_vwasm": [4, 0, 110, 110],
    }

    data_shake_cvc5 = {
        "d_komodo": [36, 15, 110, 110],
        "d_fvbkv": [143, 69, 110, 104],
        "d_lvbkv": [210, 78, 110, 110],
        "fs_dice": [17, 17, 110, 110],
        "fs_vwasm": [27, 0, 110, 109],
    }

    for data in [data_core_z3, data_shake_z3, data_shake_cvc5, data_naive_shake_z3]:
        solver = "cvc5" if data == data_shake_cvc5 else "z3"

        is_shake = data == data_shake_z3 or data == data_shake_cvc5 or data == data_naive_shake_z3

        for ver in [0, 1]:
            fig, ax = plt.subplots(1, 2, figsize=(10, 3.5), squeeze=False)

            orig = [data[i][0] for i in data]
            curr = [data[i][1] for i in data]
            _plot_stability_impact(ax[0][0], data.keys(), orig, curr, True, is_shake, solver, ver)
            fig.supylabel(r"Query Count", rotation=0, va="center", fontsize=10)

            orig = [data[i][2] for i in data]
            curr = [data[i][3] for i in data]
            _plot_stability_impact(ax[0][1], data.keys(), orig, curr, False, is_shake, solver, ver)

            name = "shake" if is_shake else "core"

            if data == data_naive_shake_z3:
                name = "naive_shake"

            plt.tight_layout()
            plt.savefig(f"fig/stability/{name}.{solver}.{ver}.png", bbox_inches='tight',pad_inches=0.1, dpi=600)
            plt.close()

def _plot_stability_impact(sp, labels, orig, curr, is_miti, is_shake, solver, ver):
    bar_width = 0.1
    x = np.arange(len(orig)) / 4

    if is_miti:
        color = "orange"
        title = "Instability Mitigation"
        label_0 = "Unstable (Original)"
    else:
        color = "lightseagreen"
        title = "Stability Preservation"
        label_0 = "Stable (Original)"

    if solver == "cvc5":
        title += " (cvc5 1.1.1)"
    else:
        title += " (z3 4.12.5)"

    sp.bar(   
        x,
        orig,
        bar_width,
        label=label_0,
        color=color,
        edgecolor="black",
    )

    if ver == 1:
        label = "Stable (Shake)" if is_shake else "Stable (Core)"
        sp.bar(
            x,
            curr,
            bar_width,
            label=label,
            color="white",
            edgecolor="black",
            hatch="//",
            alpha=0.5,
        )

    sp.set_title(title)
    # if is_miti:

    sp.set_xticks(x, [GROUP_PLOT_META[i].tex_name for i in labels], fontsize=10)

    if is_miti:
        sp.legend(fontsize=8, loc="upper right")
    else:
        sp.legend(fontsize=8, loc="lower right")

def plot_unstable_count():
    data = {
        "d_komodo":  [2054, 93,],
        "d_fvbkv":   [5170,  172,],
        "d_lvbkv":   [5334,  256,],
        "fs_dice":   [1536,  20,],
        "fs_vwasm":  [1755,  4,],
    }

    bar_width = 0.1

    x = np.arange(len(data)) / 4
    
    for ver in range(3):
        plt.figure(figsize=(7, 3.5))

        # Create the stacked bar plot
        tota = [data[i][0] for i in data]
        unst = [data[i][1] for i in data]
        
        ratios = [unst[i] * 100 / tota[i] for i in range(len(tota))]
        
        plt.bar(
            x,
            tota,
            bar_width,
            label="Total",
            color="white",
            edgecolor="black",
        )

        if ver >= 1:
            plt.bar(
                x,
                unst,
                bar_width,
                label="Unstable",
                color="orange",
                edgecolor="black",
            )

        if ver >= 2:        
            for i in range(len(ratios)):
                plt.text(x[i], unst[i] + 30, f"{round(ratios[i], 1)}\%", fontsize=10, va="bottom", ha="center")

        plt.legend(fontsize=8, loc="upper right")
        plt.title("Mariposa Query Set (z3 4.12.5)")
        plt.ylabel(r"Query Count", rotation=0, labelpad=40, va="center", fontsize=10)
        plt.xticks(x, [GROUP_PLOT_META[i].tex_name for i in data], fontsize=10)

        plt.tight_layout()
        plt.savefig(f"fig/stability/query_count.{ver}.png", bbox_inches='tight',pad_inches=0.1, dpi=600)
        plt.close()

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
    subparsers.add_parser("shake-create", help="create shake queries")
    subparsers.add_parser("plot-count", help="plot unstable count")
    subparsers.add_parser("plot-impact", help="plot stability impact")

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "bench":
        handle_create_benchmark()
    elif args.sub_command == "core-ctx":
        handle_core_context_analysis()
    elif args.sub_command == "core-stb":
        handle_core_stability_analysis()
    elif args.sub_command == "shake":
        handle_shake_survival()
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
    elif args.sub_command == "shake-create":
        handle_shake_create("bench_stable")
        # handle_shake_create("bench_unstable")
    elif args.sub_command == "plot-count":
        plot_unstable_count()
    elif args.sub_command == "plot-impact":
        plot_stability_impact()
