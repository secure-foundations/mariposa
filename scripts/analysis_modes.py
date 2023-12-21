from configure.project import ProjectManager
from analysis.core_analyzer import GroupCoreAnalyzer
from analysis.bloat_analyzer import BloatAnalyzer
from analysis.categorizer import Categorizer
from utils.analyze_utils import *
import matplotlib.pyplot as plt

def analyze_unsat_cores(args):
    for pname in ["d_komodo", "d_lvbkv", "d_fvbkv", "fs_dice", "fs_vwasm"]:
        if pname != "fs_vwasm":
            continue
        m = ProjectManager()
        g = m.load_project_group(pname)
        g = GroupCoreAnalyzer(g)
        g.print_status()

def plot_verus_assert_counts():
    fig, ax = plt.subplots(5, 1, squeeze=False)
    fig.set_figheight(5 * 5)
    fig.set_figwidth(7.5 * 1)

    m = ProjectManager()

    for i, pname in enumerate(["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]):
        g = m.load_project_group(pname)
        g = BloatAnalyzer(g)
        ocounts, bcounts = g.get_assert_counts()
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

def plot_verus_veri_times():
    fig, ax = plt.subplots(5, 1, squeeze=False)
    fig.set_figheight(5 * 5)
    fig.set_figwidth(7.5 * 1)
    m = ProjectManager()

    for i, pname in enumerate(["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]):
        g = m.load_project_group(pname)
        g = BloatAnalyzer(g)
        ocounts, bcounts = g.get_veri_times()
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

def analysis_main(args):
    m = ProjectManager()
    for i, pname in enumerate(["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]):
        g = m.load_project_group(pname)
        g = BloatAnalyzer(g, Categorizer("default"))
        g.print_status()
