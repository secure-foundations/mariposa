from configure.project import ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from analysis.categorizer import Stability, Categorizer
from tabulate import tabulate

class BloatAnalyzer(GroupAnalyzer):
    def __init__(self, group_name, ana):
        super().__init__(group_name, ana)
        self.blot: ExpAnalyzer = self.load_stability_status(PType.BLOT)
        # self.print_diff()

    def print_diff(self):
        print("[INFO] diffing:", self.group_name)
        
        diff = self.orig.base_names() - self.blot.base_names()

        if len(diff) != 0:
            print("[INFO] queries in orig but not in bolt:")
            for qn in diff:
                print("\t" + qn)
            print(f"[INFO] {len(diff)} missing")
        
        diff = self.blot.base_names() - self.orig.base_names()

        if len(diff) != 0:
            print("[INFO] queries in blot but not in orig:")
            for qn in diff:
                print("\t" + qn)
            print(f"[INFO] {len(diff)} missing")

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
        EXPECTED = [Stability.UNSTABLE, Stability.STABLE, Stability.UNSOLVABLE]
        print(f"stability status original vs. bloat {self.group_name}")
        ocasts = self.orig.get_stability_status()
        bcasts = self.blot.get_stability_status()
        table = [["category", "original", "bloat"]]
        for cat in EXPECTED:
            ocs, bcs = ocasts[cat], bcasts[cat]
            if cat not in EXPECTED:
                assert ocs.count == 0 and bcs.count == 0
                continue
            oc = f"{ocs.count} ({round(ocs.percent, 2)}%)"
            bc = f"{bcs.count} ({round(bcs.percent, 2)}%)"
            table.append([cat, oc, bc])
        table.append(["total", ocasts.total, bcasts.total])
        print(tabulate(table, headers="firstrow", tablefmt="github", floatfmt=".2f"))
        print("")

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
    ana = Categorizer("default")
    g = BloatAnalyzer("v_mimalloc", ana)
    g.print_status()
