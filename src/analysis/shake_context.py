import multiprocessing

import numpy as np
from analysis.core_analyzer import CoreAnalyzer
from analysis.shake_analyzer import ShakeAnalyzer, load_shake_stats
from base.defs import MARIPOSA_GROUPS
from base.factory import FACT
from utils.analysis_utils import PartialCDF
from utils.cache_utils import *
from utils.plot_utils import *
from utils.query_utils import count_asserts
from matplotlib import pyplot as plt
import matplotlib.patheffects as pe

def handle_core_context_analysis():
    plt.figure(figsize=(5,3.5))

    for gid in MARIPOSA_GROUPS:
        df = load_shake_stats(gid, 100)
        core_count = np.array(df.core_count, dtype=float)
        base_count = np.array(df.base_counts, dtype=float)
        ratios = core_count * 100 / base_count
        ratios = ratios[~np.isnan(ratios)]
        ratios = PartialCDF(ratios)

        pm = GROUP_PLOT_META[gid]
        plt.plot(ratios.xs, ratios.ys, label=pm.tex_name, color=pm.color)
        p50 = ratios.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
        if gid in {"fs_vwasm",  "d_komodo"}:
            plt.text(
                p50[0] * 1.15, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom"
            )
        elif gid in {"fs_dice", "d_lvbkv"}:
            plt.text(
                p50[0] * 0.4, p50[1], f"{round(p50[0], 2)}\%", fontsize=8, va="bottom"
            )
    handles, labels = plt.gca().get_legend_handles_labels()
    order = [3,1,2,0,4]
    plt.legend([handles[idx] for idx in order],[labels[idx] for idx in order], fontsize=10)

    plt.xlabel("Original Query Relevance Ratio Log Scale (\%)")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))
    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xscale("log")
    plt.grid()
    plt.tight_layout()
    plt.savefig(f"fig/relevance/overall_original.pdf", bbox_inches='tight',pad_inches = 0)
    plt.close()
    
    plt.figure(figsize=(5,3.5))

    for gid in MARIPOSA_GROUPS:
        df = load_shake_stats(gid, 100)
        base_counts = np.array(df.base_counts, dtype=float)
        base_counts = PartialCDF(base_counts)

        pm = GROUP_PLOT_META[gid]
        plt.plot(base_counts.xs, base_counts.ys, label=pm.tex_name, color=pm.color)
        p50 = base_counts.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)
        if gid in {"fs_dice", "fs_vwasm", "d_komodo"}:
            plt.text(
                p50[0] * 1.05, p50[1], f"{tex_fmt_int(int(p50[0]))}", fontsize=8, va="bottom", ha="left"
            )
        if gid in {"d_lvbkv"}:
            plt.text(
                p50[0], p50[1], f"{tex_fmt_int(int(p50[0]))}", fontsize=8, va="bottom", ha="right"
            )

    handles, labels = plt.gca().get_legend_handles_labels()
    order = [4,1,2,0,3]
    plt.legend([handles[idx] for idx in order],[labels[idx] for idx in order], fontsize=10)

    plt.xlabel("Original Query Assertion Count Log Scale")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))
    plt.ylim(0, 100)
    # plt.xlim(0.001, 100)
    plt.xscale("log")
    plt.grid()
    plt.tight_layout()
    plt.savefig(f"fig/relevance/overall_count_original.pdf", bbox_inches='tight',pad_inches = 0)
    plt.close()

def handle_shake_context_analysis():
    shake_plot_rr(0, False)
    shake_plot_rr(0, True)
    shake_plot_rr(100, False)
    shake_plot_rr(100, True)
    # oracle = True
    # for gid in MARIPOSA_GROUPS:
    #     if gid != "d_lvbkv":
    #         continue
    #     sa = ShakeAnalyzer(FACT.get_group(gid))
    #     sa.debug_shake(15)

    # for gid in MARIPOSA_GROUPS:
        # meta = GROUP_PLOT_META[gid]
        # row0 = [meta.tex_cmd, "MRR"]
        # row1 = ["", "CMR"]
        # mid, mis = foo(gid)
        # row0 += [str(mid)]
        # row1 += [str(mis)]
        # for freq in [0, 100, 30, 15, 10]:
        #     mid, mis = shake_freq_analysis(gid, freq, oracle)
        #     row0 += [str(mid)]
        #     row1 += [str(mis)]
        # print(" & ".join(row0) + " \\\\")
        # print(" & ".join(row1) + " \\\\")
        # print("\midrule")

def foo(gid):
    df = load_shake_stats(gid, 100)
    core_count = np.array(df.core_count, dtype=float)
    shkf_count = np.array(df.base_counts, dtype=float)
    
    missing = np.array(df.default_missing_count, dtype=float)
    miss_count = 0
    valid_count = 0

    ratios = []
    for i in range(len(core_count)):
        if np.isnan(core_count[i]):
            continue
        ratios += [core_count[i] * 100 / shkf_count[i]]
        valid_count += 1
    ratios = PartialCDF(ratios)
    return round(ratios.valid_median[0], 2), round(miss_count * 100 / valid_count, 2)

def shake_plot_rr(freq, oracle):
    plt.figure(figsize=(5,3.5))
    for gid in MARIPOSA_GROUPS:
        df = load_shake_stats(gid, freq)
        pm = GROUP_PLOT_META[gid]
        core_count = np.array(df.core_count, dtype=float)
        base_count = np.array(df.base_counts, dtype=float)
        if oracle:
            shko_count = np.array(df.oracle_count, dtype=float)
        else:
            shko_count = np.array(df.default_count, dtype=float)

        missing = np.array(df.default_missing_count, dtype=float)

        ratios = []
        for i in range(len(core_count)):
            if np.isnan(core_count[i]):
                continue

            shkoc = shko_count[i]
            if missing[i] != 0:
                shkoc = base_count[i]
            ratios += [core_count[i] * 100 / shkoc]

        ratios = PartialCDF(ratios)
        
        plt.plot(ratios.xs, ratios.ys, label=pm.tex_name, color=pm.color)
        p50 = ratios.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=3)

        if gid in {"fs_vwasm", "d_lvbkv"}:
            add_text(plt, p50[0]*1.2, p50[1], fmt_percent(p50[0]))
        elif gid in {"fs_dice",  "d_komodo"}:
            add_text(plt, p50[0]*0.95, p50[1], fmt_percent(p50[0]), left=False)

    handles, labels = plt.gca().get_legend_handles_labels()
    order = [3,0,1,2,4]

    if oracle:
        suffix = "oracle"
    else:
        suffix = "default"

    if freq == 0:
        suffix += "_naive"
    else:
        suffix += "_quanti"

    plt.legend([handles[idx] for idx in order],[labels[idx] for idx in order], fontsize=8)
    plt.xlabel("Shake Query Relevance Ratio Log Scale (\%)")
    plt.ylabel("CDF (\%)")
    plt.yticks(np.arange(0, 101, 10))

    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xscale("log")
    plt.grid()
    plt.tight_layout()
    
    plt.savefig(f"fig/relevance/shake_{suffix}.pdf", bbox_inches='tight',pad_inches = 0)

def shake_freq_analysis(gid, freq, oracle):
    df = load_shake_stats(gid, freq)
    core_count = np.array(df.core_count, dtype=float)
    base_count = np.array(df.base_counts, dtype=float)
    shko_count = np.array(df.oracle_count, dtype=float)
    shkf_count = np.array(df.default_count, dtype=float)
    missing = np.array(df.default_missing_count, dtype=float)
    miss_count = 0
    valid_count = 0

    ratios = []
    for i in range(len(core_count)):
        if np.isnan(core_count[i]):
            continue
        valid_count += 1

        if missing[i] != 0:
            miss_count += 1

        if oracle:
            shkoc = shko_count[i]
            if missing[i] != 0:
                shkoc = base_count[i]
            ratios += [core_count[i] * 100 / shkoc]
        else:
            if missing[i] != 0:
                continue
            ratios += [core_count[i] * 100 / shkf_count[i]]
    return round(np.median(ratios), 2), round(miss_count * 100 / valid_count, 2)


    # suffix = "oracle" if oracle else "default"
    # suffix += str(freq)

    # plt.savefig(f"fig/relevance/shake_{suffix}.pdf")
    # plt.close()

def _shake_depth_analysis(gid):
    df = load_shake_stats(gid, 100)
    plt.figure(figsize=(5,2.5))

    for naive in [False]:
        core_depths = np.array(df.max_core_depth, dtype=float)
        valid_indices = ~np.isnan(core_depths)
        core_depths = core_depths[valid_indices]
        base_depths = np.array(df.max_base_depth, dtype=float)[valid_indices]
        diff = base_depths - core_depths
        core = PartialCDF(core_depths)
        base = PartialCDF(base_depths)
        diff = PartialCDF(diff)

        suffix = "Naive Shake" if naive else ""
        color = GROUP_PLOT_META[gid].color
        plt.plot(core.xs, core.ys, label="Core " + suffix, color=color, linestyle="--", linewidth=1.5)
        plt.plot(base.xs, base.ys, label="Original " + suffix, color=color,  linewidth=1.5)
        # plt.plot(diff.xs, diff.ys, label="Difference " + suffix + " $\geq$", color=color, linestyle=":", linewidth=1.5)

        p50 = core.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=5)
        p50 = base.valid_median
        plt.plot(p50[0], p50[1], c="black", marker="o", markersize=5)

    plt.legend()

    x_max = max(core.valid_max[0], base.valid_max[0])
    plt.xlim(0, x_max)
    plt.xticks(np.arange(0, x_max + 1, 1))
    plt.ylim(0, 100)
    plt.yticks(np.arange(0, 101, 10))

    plt.xlabel("Maximum Shake Distance")
    plt.ylabel("CDF (\%)")
    plt.grid()

    plt.tight_layout()
    plt.savefig(f"fig/depth/{gid}.pdf", bbox_inches='tight',pad_inches = 0)

    plt.close()

def _shake_depth_analysis_overall():
    # if has_cache("shake_max_depth"):
    #     all_data = load_cache("shake_max_depth")
    # else:
    print("?")
    plt.figure(figsize=(5,4))

    all_data = []
    for gid in MARIPOSA_GROUPS:
        df = load_shake_stats(gid, 100)
        core_depths = np.array(df.max_core_depth, dtype=float)
        valid_indices = ~np.isnan(core_depths)
        core_depths = core_depths[valid_indices]
        base_depths = np.array(df.max_base_depth, dtype=float)[valid_indices]
        all_data.append(base_depths)
        all_data.append(core_depths)
        # save_cache("shake_max_depth", all_data)

    all_data = all_data[::-1]
    # print(all_data)
    hatches, labels, colors = [], [], []

    for gid in MARIPOSA_GROUPS[::-1]:
        meta = GROUP_PLOT_META[gid]
        color = meta.color
        colors += [color, color]
        hatches += ["///", ""]
        labels += [meta.tex_name]

    fig, ax = plt.subplots(1, 1, squeeze=False)
    sp0 = ax[0][0]

    medianprops = dict(alpha=0)
    bp = sp0.boxplot(
        all_data,
        showfliers=False,
        patch_artist=True,
        flierprops=dict(markersize=2, marker="."),
        medianprops=medianprops,
        vert=True,
    )

    handle = None
    for median in bp["medians"]:
        x, y = median.get_data()
        handle = plt.scatter(
            (x[0] + x[1])/2,
            y[0],
            color="white",
            # linewidth=2,
            # solid_capstyle="round",
            zorder=4,
            edgecolors="black",
            # path_effects=[pe.Stroke(linewidth=4, foreground="black"), pe.Normal()],
        )

    b0, b1 = bp["boxes"][0], bp["boxes"][1]
    b0.set_facecolor("white")
    b1.set_facecolor("white")
    b1.set_hatch("///")

    sp0.legend([b0, b1, handle], ["Original", "Core", "Median"], fontsize=8)

    for i, box in enumerate(bp["boxes"]):
        color = colors[i]
        hatch = hatches[i]
        box.set_facecolor(color)
        box.set_edgecolor("black")
        box.set_hatch(hatch)
        # box.set_linewidth(1.5)

    sp0.set_yticks(
        np.arange(0, 24, 1), ["%d" % (i) if i % 2 == 0 else "" for i in range(0, 24, 1)]
    )

    # for i in range(0, len(bp["boxes"]), 2):
    #     sp0.plot([-1, -0.8], [i + 1.5, i + 1.5], linestyle="dashed", color="black")

    # sp0.vlines(np.arange(1.5, len(CORE_PROJECTS)*2+1, 2), 0-1, 0.2-1, color="black")
    sp0.set_xticks(np.arange(1.5, len(MARIPOSA_GROUPS) * 2 + 1.5, 2), labels, ha="center", fontsize=12)

    sp0.set_ylim(-1, 21)
    # sp0.grid(axis="y")

    plt.tick_params(
        axis="y",  # changes apply to the x-axis
        which="both",  # both major and minor ticks are affected
        bottom=True,  # ticks along the bottom edge are off
        top=False,  # ticks along the top edge are off
    )
    plt.tick_params(
        axis="x",  # changes apply to the y-axis
        which="both",  # both major and minor ticks are affected
        left=False,  # ticks along the bottom edge are off
        right=False,  # ticks along the top edge are off
    )

    sp0.set_ylabel("Maximum Shake Distance")

    plt.tight_layout()
    plt.savefig("fig/depth/overall.pdf", bbox_inches='tight',pad_inches = 0)
    plt.close()

def handle_shake_depth_analysis():
    _shake_depth_analysis_overall()
    # for gid in MARIPOSA_GROUPS:
    #     _shake_depth_analysis(gid)
        # _shake_depth_analysis(gid, naive=True)
