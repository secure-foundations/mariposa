from execute.solver_runner import RCode
from analysis.analyzer import *
from tabulate import tabulate
from utils.math_utils import *
import numpy as np

EXPECTED_CODES = [RCode.UNSAT, RCode.UNKNOWN, RCode.TIMEOUT]

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

    def _print_query_plain_status(self, qstat):
        print(qstat.query_path)
        table = [["mutation"] + [str(rc) for rc in EXPECTED_CODES] 
                 + ["mean", "std"]]
        v_rcode, v_time = qstat.get_original_status()
        print(f"original: {RCode(v_rcode)} {v_time / 1000} s")

        for m in qstat.mutations:
            trow = [m]
            rcodes, times = qstat.get_mutation_status(m)
            rcs = RCode.empty_map()
            for rc in rcodes:
                rc = RCode(rc)
                assert rc in EXPECTED_CODES
                rcs[rc] += 1
            for rc in EXPECTED_CODES:
                trow.append(rcs[rc])

            times = times / 1000
            trow.append(round(np.mean(times), 2))
            trow.append(round(np.std(times), 2))
            table.append(trow)

        print(tabulate(table, headers="firstrow"))

    def print_plain_status(self):
        qss = self.load_sum_table()
        for qs in qss:
            self._print_query_plain_status(qs)
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

        for q in cats[Stability.UNSTABLE]:
            self._print_query_plain_status(q)

    # def print_stability_status(self, ana):
    #     self.load_stability_stats(ana)
    #     # for c in cats:
    #     #     print(c.value, cats[c])
