from configure.project import ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from analysis.categorizer import Stability, Categorizer
from analysis.core_analyzer import get_stability_scores
from utils.analyze_utils import print_sets_diff, get_cdf_pts, tex_fmt_percent
from utils.cache_utils import *
import numpy as np
import matplotlib.pyplot as plt

class RevalAnalyzer(GroupAnalyzer):
    def __init__(self, group_name, ana):
        super().__init__(group_name, ana)
        self.revl: ExpAnalyzer = self.load_stability_status(PType.REVL)
        # print_sets_diff(self.orig.base_names(), self.blot.base_names(), "orig", "blot")
        self.duplicated = self.load_duplicated_queries()

    def load_duplicated_queries(self):
        from tqdm import tqdm
        cache_path = f"dircmp/opaque_{self.group_name}"

        duplicated = load_cache(cache_path)
        if not duplicated:
            duplicated = set()
            for q in tqdm(self.orig.base_names() & self.revl.base_names()):
                orig_path = f"{self.group_path}/{PType.ORIG.value}/{q}"
                revl_path = f"{self.group_path}/{PType.REVL.value}/{q}"
                if open(orig_path).read() == open(revl_path).read():
                    duplicated.add(q)
            save_cache(cache_path, duplicated)
        return duplicated

    def print_status(self):
        print(f"[INFO] {self.group_name} original vs. reveal")
        print(f"[INFO] excluded {len(self.duplicated)} duplicated queries")
        # dps = []
        # for q in self.orig.base_names() & self.revl.base_names() - self.duplicated:
        #     rcount = self.revl.get_assert_count(q)
        #     ocount = self.orig.get_assert_count(q)
        #     # dps.append(self.revl.get_assert_count(q) / self.orig.get_assert_count(q))
        #     dps.append((rcount - ocount) / ocount)
        # dps = np.array(dps)
        # print(min(dps), max(dps), np.mean(dps) * 100, np.median(dps))
        # xs, ys = get_cdf_pts(dps)
        # fig, ax = plt.subplots()
        
        # ax.plot(xs, ys, label="cdf")
        # ax.set_xlabel("assert count ratio")
        # ax.set_ylabel("cdf")
        # ax.set_title(f"{self.group_name} original vs. reveal")
        # ax.legend()
        # plt.savefig(f"fig/orig_revl.png")

        remove = (self.orig.base_names() - self.revl.base_names())
        # | self.duplicated

        ocasts = self.orig.get_stability_status()
        ocasts = ocasts.filter_out(remove)
        rcasts = self.revl.get_stability_status()
        # rcasts = rcasts.filter_out(remove)

        scores = get_stability_scores(rcasts, ocasts)
        print(scores)

        # ocasts.print_compare_status(rcasts, skip_empty=True,
        #                             cats=[Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE], 
        #                             this_name="original", that_name="transparent")

        # migration = ocasts.get_migration_status(rcasts)
        # data = dict()
        # tally = [""]
        # cats = [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]
        # for c in cats:
        #     print(f"[INFO] adjusted {c} mitigation")
        #     # migration[c].print_status()
        #     tally += [migration[c].total, ""]
        #     row = []
        #     for c2 in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        #        row += [migration[c][c2]]
        #         # print(f"[INFO] {c} -> {c2} {migration[c][c2].percent}")
        #     data[c] = row
        # df = pd.DataFrame(data, index=["stable", "unstable", "unsolvable"])
        # # df = df.transpose()
        # table = []
        # from tabulate import tabulate
        # for cat in cats:
        #     r = df.loc[cat]
        #     row = [str(cat)]
        #     for i in r:
        #         row += [i.count, tex_fmt_percent(i.percent)]
        #     table.append(row)
        # header = ["category", "stable", "", "unstable", "", "unsolvable", ""]
        # table = [tally] + table
        # print(tabulate(table, headers=header, tablefmt="latex_raw"))

OPAQUE_PROJECTS = ["d_lvbkv"]

def analyze_reveal():
    ana = Categorizer("60sec")
    for pname in OPAQUE_PROJECTS:
        g = RevalAnalyzer(pname, ana)
        g.print_status()
        print("")
