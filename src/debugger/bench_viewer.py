from typing import Dict
from debugger.demo_utils import DebuggerStatus, Reviewer2
from utils.analysis_utils import Categorizer
import numpy as np

class BenchViewer:
    def __init__(self, queries):
        sts = Categorizer()
        self.reviewers: Dict[str, Reviewer2] = dict()

        for query in queries:
            r = Reviewer2(query)
            sts.add_item(r.status, query)
            self.reviewers[query] = r

        sts.finalize()
        self.status = sts

        self.fixable = set()
        self.unfixable = set()

        self.__analyze_finished()

    def __analyze_finished(self):
        for q in self.status[DebuggerStatus.FINISHED]:
            r = self.reviewers[q]
            num_fixes = len(r.get_stabilized())
            if num_fixes > 0:
                self.fixable.add(q)
            else:
                self.unfixable.add(q)                

    def __getitem__(self, key):
        return self.reviewers[key]

    def analyze_min_ranks(self):
        min_ranks = []
        for q in self.fixable:
            r = self.reviewers[q]
            report = r.get_report()
            indices = report.freq.loc[report.freq["qname"].isin(report.stabilized["qname"])].index
            report.freq["rank"] = report.freq["trace_count"].rank(method='min', ascending=False)
            min_rank = report.freq.loc[indices]["rank"].min()
            min_ranks.append(min_rank)
        min_ranks = np.array(min_ranks)
        return min_ranks

# analyzable = len(fixable) + len(no_fixes)
# total = len(sts.tally)

# def fmt(x, y):
#     return f"({round(x / y * 100, 1)}%)"

# print("Analyzable", analyzable)
# print("\t-", "Fixable", len(fixable), fmt(len(fixable), total))
# print("\t\t-", "top-1", fmt(len(min_ranks[min_ranks == 1]), total))
# print("\t\t-", "top-3", fmt(len(min_ranks[min_ranks <= 3]), total))
# print("\t\t-", "top-10", fmt(len(min_ranks[min_ranks <= 10]), total))
# print("\t-", "No Fixes", len(no_fixes), fmt(len(no_fixes), total))
# print("No Analyzable", total - analyzable, fmt(total - analyzable, total))
# print("\t-", "No Proofs", len(sts[DebuggerStatus.NO_PROOF]), fmt(len(sts[DebuggerStatus.NO_PROOF]), total))
