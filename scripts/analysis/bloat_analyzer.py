from configure.project import ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from analysis.categorizer import Stability
from tabulate import tabulate

class BloatAnalyzer(GroupAnalyzer):
    def __init__(self, gp, ana):
        super().__init__(gp, ana)
        self.blot: ExpAnalyzer = self.load_stability_status(gp, PType.BLOT)
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

    def get_assert_counts(self):
        return self.orig.get_assert_counts(), self.blot.get_assert_counts()

    def get_veri_times(self):
        return self.orig.get_veri_times(), self.blot.get_veri_times()

    def print_status(self):
        EXPECTED = [Stability.UNSTABLE, Stability.STABLE, Stability.UNSOLVABLE]
        print(f"stability status origin vs. bloat {self.group_name}")
        ocasts = self.orig.get_stability_status()
        bcasts = self.blot.get_stability_status()
        table = [["category", "original", "bloat"]]
        for cat in EXPECTED:
            ocs, bcs = ocasts[cat], bcasts[cat]
            if cat not in EXPECTED:
                assert ocs.count == 0 and bcs.count == 0
                continue
            table.append([cat, ocs.count, bcs.count])
        table.append(["total", ocasts.total, bcasts.total])
        print(tabulate(table, headers="firstrow", tablefmt="github", floatfmt=".2f"))
        print("")
