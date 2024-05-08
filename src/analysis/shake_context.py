import multiprocessing

import numpy as np
from analysis.core_analyzer import CoreAnalyzer
from base.defs import MARIPOSA_GROUPS
from base.factory import FACT
from utils.analysis_utils import PartialCDF
from utils.cache_utils import *
from utils.plot_utils import GROUP_PLOT_META
from utils.query_utils import count_asserts
from matplotlib import pyplot as plt

def _get_query_shake_assert_count(args):
    (shko_path, shkp_path) = args
    shko_c = count_asserts(shko_path)
    shkp_c = count_asserts(shkp_path)
    return shko_c, shkp_c

def get_shake_assert_count(gid):
    cache_name = f"{gid}_shake_asserts"

    if has_cache(cache_name):
        return load_cache(cache_name)

    pool = multiprocessing.Pool(6)

    group = FACT.get_group(gid)
    shko = group.get_project("shko.z3")
    shkf = group.get_project("shkf.z3")

    paths = [(shko.get_path(qid), shkf.get_path(qid)) for qid in shkf.qids]
    ocs, fcs = zip(*pool.map(_get_query_shake_assert_count, paths))

    shake_counts = {}

    for i, qid in enumerate(shkf.qids):
        shake_counts[qid] = (ocs[i], fcs[i])

    save_cache(cache_name, shake_counts)
    return shake_counts

def _get_query_core_assert_count(args):
    core_path, base_path = args
    if core_path == base_path:
        core_c = np.nan
    else:
        core_c = count_asserts(core_path)
    base_c = count_asserts(base_path)
    return base_c, core_c

def get_core_assert_count(gid):
    cache_name = f"{gid}_core_asserts"

    if has_cache(cache_name):
        return load_cache(cache_name)

    pool = multiprocessing.Pool(6)

    ca = CoreAnalyzer(FACT.get_group(gid))
    paths = []

    for qid in ca.qids:
        qr = ca.qids[qid]
        core_path = qr.base_path
        if qr.core_is_enabled():
            core_path = qr.patch_path
        paths.append((core_path, qr.base_path))

    ocs, fcs = zip(*pool.map(_get_query_core_assert_count, paths))

    core_counts = {}

    for i, qid in enumerate(ca.qids):
        core_counts[qid] = (ocs[i], fcs[i])

    save_cache(cache_name, core_counts)
    return core_counts

def handle_core_context_analysis():
    for gid in MARIPOSA_GROUPS:
        counts = get_core_assert_count(gid)
        ratios = []
        for qid in counts:
            base_count, core_count = counts[qid]
            if np.isnan(core_count):
                core_count = base_count
            ratios.append(core_count * 100 / base_count)
        ratios = PartialCDF(ratios)

        pm = GROUP_PLOT_META[gid]
        plt.plot(ratios.xs, ratios.ys, label=pm.tex_name, color=pm.color)
        p50 = ratios.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
        if gid != "d_lvbkv" and gid != "d_fvbkv":
            plt.text(p50[0] * 1.15, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
        elif gid != "d_fvbkv":
            plt.text(p50[0] * 0.55, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
    
    plt.legend()
    plt.xlabel("Original Query Relevance Ratio Log-Scale (\%)")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))
    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xscale("log")
    plt.grid()
    plt.tight_layout()
    plt.savefig(f"fig/relevance/overall_original.pdf")
    plt.close()

def handle_shake_context_analysis():
    for gid in MARIPOSA_GROUPS:
        shke_counts = get_shake_assert_count(gid)
        core_counts = get_core_assert_count(gid)

        counts = []
        for qid in core_counts:
            base_count, core_count =  core_counts[qid]
            shko_count, shkf_count = shke_counts[qid]

            if np.isnan(shko_count):
                shko_count = base_count
            counts.append((base_count, core_count, shko_count, shkf_count))

        counts = np.array(counts)
        o_ratios = counts[:,1] * 100 / counts[:,2]
        f_ratios = counts[:,1] * 100 / counts[:,3]
        o_ratios = PartialCDF(o_ratios)
        f_ratios = PartialCDF(f_ratios)

        pm = GROUP_PLOT_META[gid]
        plt.plot(f_ratios.xs, f_ratios.ys, label=pm.tex_name, color=pm.color)
        p50 = f_ratios.valid_median
        # plt.plot(o_ratios.xs, o_ratios.ys, label=pm.tex_name, color=pm.color)
        # p50 = o_ratios.valid_median

        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
        if gid in {"fs_vwasm", "d_komodo"}:
            plt.text(p50[0] * 1.15, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
        elif gid in {"d_lvbkv", "fs_dice"}:
            plt.text(p50[0] * 0.45, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom")
    
    plt.legend()
    plt.xlabel("Query Relevance Ratio (\%)")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))

    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xscale("log")
    plt.grid()

    plt.savefig(f"fig/relevance/overall_shake.pdf")
    plt.close()
