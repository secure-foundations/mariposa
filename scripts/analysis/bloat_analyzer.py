from configure.project import ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from analysis.categorizer import Stability, Categorizer
from utils.analyze_utils import print_sets_diff
from utils.cache_utils import *

class BloatAnalyzer(GroupAnalyzer):
    def __init__(self, group_name, ana):
        super().__init__(group_name, ana)
        self.blot: ExpAnalyzer = self.load_stability_status(PType.BLOT)
        # print_sets_diff(self.orig.base_names(), self.blot.base_names(), "orig", "blot")

    def get_assert_counts(self, typ):
        if typ == PType.ORIG:
            return self.orig.get_assert_counts()
        else:
            assert typ == PType.BLOT
            return self.blot.get_assert_counts()

    def get_veri_times(self, typ):
        if typ == PType.ORIG:
            return self.orig.get_veri_times()
        else:
            assert typ == PType.BLOT
            return self.blot.get_veri_times()

    def print_status(self):
        print(f"[INFO] {self.group_name} original vs. bloat")
        print(f"[INFO] analyzer {self.ana.name}")
        ocasts = self.orig.get_stability_status()
        bcasts = self.blot.get_stability_status()
        ocasts.print_compare_status(bcasts, skip_empty=True,
                                    cats=[Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE], 
                                    this_name="original", that_name="bloat")

BLOAT_PROJECTS = ["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]

# def plot_verus_assert_counts(ana):
#     fig, ax = plt.subplots(5, 1, squeeze=False)
#     fig.set_figheight(5 * 5)
#     fig.set_figwidth(7.5 * 1)

#     counts = get_bloat_stats(ana, "assert_counts")

#     for i, pname in enumerate(counts.keys()):
#         ocounts, bcounts = counts[pname]
#         subp = ax[i][0]

#         xs, ys = get_cdf_pts(ocounts)
#         op = subp.plot(xs, ys, label=pname + "_original")
#         xs, ys = get_cdf_pts(bcounts)

#         subp.plot(xs, ys, label=pname + "_bloat", color=op[0].get_color(), linestyle="dashed")

#         subp.set_ylim(0, 100)
#         subp.legend()

#         subp.set_title(pname)
#         subp.set_ylabel("cumulative percentage of queries")
#         subp.set_xlabel("number of assertions")

#     # fig.suptitle("assertion counts in queries")
#     plt.tight_layout()
#     plt.savefig(f"fig/verus_assert_counts.png", dpi=300)
#     plt.close()

# def plot_verus_veri_times(ana):
#     fig, ax = plt.subplots(5, 1, squeeze=False)
#     fig.set_figheight(5 * 5)
#     fig.set_figwidth(7.5 * 1)

#     counts = get_bloat_stats(ana, "assert_counts")
#     for i, pname in enumerate(counts.keys()):
#         ocounts, bcounts = counts[pname]
#         subp = ax[i][0]

#         xs, ys = get_cdf_pts(ocounts)
#         op = subp.plot(xs, ys, label=pname + "_original")

#         xs, ys = get_cdf_pts(bcounts)
#         subp.plot(xs, ys, label=pname + "_bloat", color=op[0].get_color(), linestyle="dashed")

#         subp.set_ylim(0, 100)
#         subp.legend()

#         subp.set_title(pname)
#         subp.set_xscale("log")
#         subp.set_ylabel("cumulative percentage of queries")
#         subp.set_xlabel("verification time (log scale seconds)")

#     plt.tight_layout()
#     plt.savefig(f"fig/verus_veri_time.png", dpi=300)
#     plt.close()
    # counts = get_bloat_stats(ana, "assert_counts")
    # times = get_bloat_stats(ana, "veri_times")
    # table = [["project", 
    #           "original assert\ncounts (geomean)", 
    #           "bloat assert\ncounts (geomean)", 
    #           "assert count\nincrease (%)",
    #           "original verification\ntime (geomean)",
    #           "bloat verification\ntime (geomean)",
    #           "verification time\nincrease (%)"]]

    # for pname in counts.keys():
    #     ocounts, bcounts = counts[pname]
    #     ocount, bcount = int(gmean(ocounts)), int(gmean(bcounts))
    #     count_inc = gmean(bcounts) / gmean(ocounts) * 100 - 100
    #     ocounts, bcounts = times[pname]
    #     otime, btime = gmean(ocounts), gmean(bcounts)
    #     time_inc = gmean(bcounts) / gmean(ocounts) * 100 - 100
    #     table.append([pname, ocount, bcount, count_inc, otime, btime, time_inc])

    # print(tabulate(table, headers="firstrow", floatfmt=".2f"))

def analyze_bloat():
    ana = Categorizer("60sec")
    for pname in BLOAT_PROJECTS:
        g = BloatAnalyzer(pname, ana)
        g.print_status()
        print("")
