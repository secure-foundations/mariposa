from tabulate import tabulate
from configure.project import PM
from analysis.core_analyzer import GroupCoreAnalyzer, CORE_PROJECTS, analyze_unsat_core
from analysis.bloat_analyzer import BloatAnalyzer
from analysis.categorizer import Categorizer
# from analysis.basic_analyzer import ExpAnalyzer
# from execute.exp_part import ExpPart
# from configure.solver import SolverInfo
from utils.analyze_utils import *
import matplotlib.pyplot as plt
from scipy.stats import gmean

def emit_core_build():
    for pname in CORE_PROJECTS:
        g = GroupCoreAnalyzer(pname, ana=Categorizer("default"))
        # g.print_status()
        g.emit_build()

def get_bloat_stats(ana, stat):
    counts = dict()
    for pname in ["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]:
        g = PM.load_project_group(pname)
        g = BloatAnalyzer(g, ana)
        if stat == "assert_counts":
            ocounts, bcounts = g.get_assert_counts()
        else:
            assert stat == "veri_times"
            ocounts, bcounts = g.get_veri_times()
        counts[pname] = (ocounts, bcounts)
        g.print_status()
    return counts

def plot_verus_assert_counts(ana):
    fig, ax = plt.subplots(5, 1, squeeze=False)
    fig.set_figheight(5 * 5)
    fig.set_figwidth(7.5 * 1)

    counts = get_bloat_stats(ana, "assert_counts")

    for i, pname in enumerate(counts.keys()):
        ocounts, bcounts = counts[pname]
        subp = ax[i][0]

        xs, ys = get_cdf_pts(ocounts)
        op = subp.plot(xs, ys, label=pname + "_original")
        xs, ys = get_cdf_pts(bcounts)

        subp.plot(xs, ys, label=pname + "_bloat", color=op[0].get_color(), linestyle="dashed")

        subp.set_ylim(0, 100)
        subp.legend()

        subp.set_title(pname)
        subp.set_ylabel("cumulative percentage of queries")
        subp.set_xlabel("number of assertions")

    # fig.suptitle("assertion counts in queries")
    plt.tight_layout()
    plt.savefig(f"fig/verus_assert_counts.png", dpi=300)
    plt.close()

def plot_verus_veri_times(ana):
    fig, ax = plt.subplots(5, 1, squeeze=False)
    fig.set_figheight(5 * 5)
    fig.set_figwidth(7.5 * 1)

    counts = get_bloat_stats(ana, "assert_counts")
    for i, pname in enumerate(counts.keys()):
        ocounts, bcounts = counts[pname]
        subp = ax[i][0]

        xs, ys = get_cdf_pts(ocounts)
        op = subp.plot(xs, ys, label=pname + "_original")

        xs, ys = get_cdf_pts(bcounts)
        subp.plot(xs, ys, label=pname + "_bloat", color=op[0].get_color(), linestyle="dashed")

        subp.set_ylim(0, 100)
        subp.legend()

        subp.set_title(pname)
        subp.set_xscale("log")
        subp.set_ylabel("cumulative percentage of queries")
        subp.set_xlabel("verification time (log scale seconds)")

    plt.tight_layout()
    plt.savefig(f"fig/verus_veri_time.png", dpi=300)
    plt.close()

def print_verus_stats(ana):
    counts = get_bloat_stats(ana, "assert_counts")
    times = get_bloat_stats(ana, "veri_times")
    table = [["project", 
              "original assert\ncounts (geomean)", 
              "bloat assert\ncounts (geomean)", 
              "assert count\nincrease (%)",
              "original verification\ntime (geomean)",
              "bloat verification\ntime (geomean)",
              "verification time\nincrease (%)"]]

    for pname in counts.keys():
        ocounts, bcounts = counts[pname]
        ocount, bcount = int(gmean(ocounts)), int(gmean(bcounts))
        count_inc = gmean(bcounts) / gmean(ocounts) * 100 - 100
        ocounts, bcounts = times[pname]
        otime, btime = gmean(ocounts), gmean(bcounts)
        time_inc = gmean(bcounts) / gmean(ocounts) * 100 - 100
        table.append([pname, ocount, bcount, count_inc, otime, btime, time_inc])

    print(tabulate(table, headers="firstrow", floatfmt=".2f"))

# def analysis_main(args):
#     # plot_verus_veri_times(ana)
#     # plot_verus_assert_counts(ana)
#     # print_verus_stats(ana)
#     analyze_unsat_cores(args)

if __name__ == "__main__":
    # analyze_unsat_core()
    g = GroupCoreAnalyzer("d_komodo", ana=Categorizer("default"))
    g.emit_build()
