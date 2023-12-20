from execute.solver_runner import RCode
from analysis.analyzer import *
from tabulate import tabulate
from utils.math_utils import *

# def dump_multi_status(project, solver, exp, ana):
#     rows = load_sum_table(project, solver, cfg=exp)
#     items = ana.categorize_queries(rows)
#     ps, _ = get_category_percentages(items)

#     print("project directory:", project.clean_dir)
#     print("solver used:", solver.path)
#     print("total queries:", len(rows))

#     pp_table = [["category", "count", "percentage"]]
#     for cat in [Stability.STABLE, Stability.INCONCLUSIVE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
#         pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])

#     print(tabulate(pp_table, tablefmt="github"))
#     print("")
#     print("listing unstable queries...")

#     for row in rows:
#         query = row[0]
#         if query not in items[Stability.UNSTABLE]:
#             continue
#         print("")
#         print("query:", row[0])
#         mutations, blob = row[1], row[2]
#         ana.dump_query_status(mutations, blob)

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
