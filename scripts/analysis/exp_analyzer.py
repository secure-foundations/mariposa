from analysis.categorizer import *
from tabulate import tabulate
from utils.math_utils import *

class ExpAnalyzer:
    def __init__(self, exp):
        assert exp.part.is_whole()
        self._exp = exp

    def __getattr__(self, item):
        return getattr(self._exp, item)

    def print_plain_status(self):
        qss = self.load_sum_table()
        for qs in qss:
            qs.print_status()
            print("")

    def load_stability_stats(self, ana):
        qss = self.load_sum_table()
        cats, tally = ana.categorize_queries(qss)
        cps, total = category_proportions(cats)
        assert total == len(qss) == len(tally)

        table = [["category", "count", "percentage"]]

        for cat, (c, p) in sorted(cps.items()):
            table.append([cat, c, round(p, 2)])

        print(tabulate(table, headers="firstrow", tablefmt="github"))

        if len(cats[Stability.UNSTABLE]) > 0:
            print("listing unstable queries...\n")

        for qs in cats[Stability.UNSTABLE]:
            qs.print_status()

    # def print_stability_status(self, ana):
    #     self.load_stability_stats(ana)
        # for c in cats:
        #     print(c.value, cats[c])
