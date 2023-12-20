from analysis.categorizer import *
from tabulate import tabulate
from utils.math_utils import *

class ExpAnalyzer:
    def __init__(self, exp):
        assert exp.part.is_whole()
        self._exp = exp
        self.qrs = exp.load_sum_table()
        self.sanity_check()

    def __getattr__(self, item):
        return getattr(self._exp, item)

    def print_plain_status(self):
        for qr in self.qrs.values():
            qr.print_status()
            print("")

    def sanity_check(self):
        expected = set(self.proj.list_queries())
        actual = set(self.qrs.keys())

        if actual - expected != set():
            print(f"[WARN] {len(actual-expected)} queries files are missing in {self.sum_table_name}")

        if expected - actual != set():
            print(f"[ERROR] {len(expected-actual)} experiments are missing in {self.sum_table_name}:")
            for q in expected - actual:
                print(f"{q}")
            sys.exit(1)

    def print_stability_status(self, ana, verbose=False):
        print(f"stability stats for {self.proj.full_name} {self.exp_name}")
        cats, tally = ana.categorize_queries(self.qrs.values())
        cps, total = category_proportions(cats)

        table = [["category", "count", "percentage"]]

        for cat, (c, p) in sorted(cps.items()):
            table.append([cat, c, round(p, 2)])

        table.append(["total", total, 100])

        print(tabulate(table, headers="firstrow", tablefmt="github", floatfmt=".2f"))

        if not verbose:
            return

        if len(cats[Stability.UNSTABLE]) > 0:
            print("listing unstable queries...\n")

        for qs in cats[Stability.UNSTABLE]:
            qs.print_status()

    # def print_stability_status(self, ana):
    #     self.load_stability_stats(ana)
        # for c in cats:
        #     print(c.value, cats[c])
