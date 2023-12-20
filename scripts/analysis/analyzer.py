import numpy as np
from enum import Enum
from statsmodels.stats.proportion import proportions_ztest
from utils.sys_utils import *
from utils.math_utils import *
from execute.solver_runner import RCode
import json
# from tabulate import tabulate

ANALYZER_CONFIG_PATH = "configs/analyzers.json"

class Stability(str, Enum):
    # UNKNOWN = "unknown"
    UNSOLVABLE = "unsolvable"
    UNSTABLE = "unstable"
    INCONCLUSIVE = "inconclusive"
    STABLE = "stable"

    def __str__(self):
        return super().__str__()

    def empty_map():
        em = {c: set() for c in Stability}
        return em

def match_rcode(blob, rcode, timeout=np.inf):
    matches = blob[0] == rcode.value
    return np.sum(np.logical_and(matches, blob[1] < timeout))

class Analyzer:
    def __init__(self, name):
        objs = json.loads(open(ANALYZER_CONFIG_PATH).read())
        obj = objs["default"]
        obj.update(objs[name])

        self.confidence = float(obj["confidence"])
        timeout = int(obj["timeout"])
        self._timeout = timeout * 1000 if timeout != -1 else np.inf
        self.r_solvable = float(obj["r_solvable"])
        self.r_stable = float(obj["r_stable"])
        self.discount = float(obj["discount"])
        
        method = obj["method"]

        if method == "strict":
            self.categorize_group = self._categorize_strict
        elif method == "z_test":
            self.categorize_group = self._categorize_z_test
        elif method == "cutoff":
            self.categorize_group = self._categorize_cutoff

    def _categorize_cutoff(self, group_blob):
        size = len(group_blob[0])
        success = match_rcode(group_blob, RCode.UNSAT, self._timeout)
        sr = success / size

        if sr < self.r_solvable:
            return Stability.UNSOLVABLE

        if sr >= self.r_stable:
            return Stability.STABLE

        return Stability.UNSTABLE

    def _categorize_strict(self, group_blob):
        size = len(group_blob[0])
        unsat_indices = group_blob[0] == RCode.UNSAT.value
        success = match_rcode(group_blob, RCode.UNSAT, self._timeout)
        
        if success == 0:
            if match_rcode(group_blob, RCode.UNKNOWN, self._timeout) == size:
                return Stability.UNKNOWN
            return Stability.UNSOLVABLE

        if success == size:
            return Stability.STABLE

        if np.mean(group_blob[1][unsat_indices]) < self._timeout * self.discount:
            return Stability.UNSTABLE

        return Stability.STABLE

    def _categorize_z_test(self, group_blob):
        size =  group_blob.shape[1]

        unsat_indices = group_blob[0] == RCode.UNSAT.value
        if self._timeout == None:
            nto_indices = np.ones(size, dtype=bool)
        else:
            nto_indices = group_blob[1] < self._timeout
        valid_indices = np.logical_and(unsat_indices, nto_indices)
        success = np.sum(valid_indices)

        value = self.r_solvable/100
        _, p_value = proportions_ztest(count=success,
                                        nobs=size,
                                        value=value, 
                                        alternative='smaller',
                                        prop_var=value)
        if p_value <= self.confidence:
            return Stability.UNSOLVABLE

        value = self.r_stable/100
        _, p_value = proportions_ztest(count=success, 
                                        nobs=size,
                                        value=value,
                                        alternative='smaller',
                                        prop_var=value)

        if self._timeout == None:
            if p_value <= self.confidence:
                return Stability.UNSTABLE
        else:
            if p_value <= self.confidence and \
                np.mean(group_blob[1][valid_indices]) < self._timeout * self.discount:
                return Stability.UNSTABLE
    
        _, p_value = proportions_ztest(count=success, 
                                        nobs=size,
                                        value=value,
                                        alternative='larger',
                                        prop_var=value)

        if p_value <= self.confidence:
            return Stability.STABLE
        return Stability.INCONCLUSIVE

    def categorize_query(self, qs, muts=None):
        votes = dict()

        if muts is None:
            muts = qs.mutations

        for m in muts:
            mblob = qs.get_mutation_status(m)
            votes[m] = self.categorize_group(mblob)

        ress = set(votes.values())
        if ress == {Stability.INCONCLUSIVE}:
            return Stability.INCONCLUSIVE, votes
        ress -= {Stability.INCONCLUSIVE}
        if len(ress) == 1:
            return ress.pop(), votes
        # ress -= {Stability.UNKNOWN}

        return Stability.UNSTABLE, votes

    def categorize_queries(self, qss, muts=None):
        categories = Stability.empty_map()
        for qs in qss:
            res, votes = self.categorize_query(qs, muts)
            categories[res].add(qs)
        tally = set.union(*categories.values())
        return categories, tally

#     def dump_query_status(self, mutations, blob):
#         status, votes = self.categorize_query(blob)
#         table = [["overall", status, "x", "x", "x", "x", "x"]]
#         mut_size = blob.shape[2]

#         for i in range(len(mutations)):
#             count_unsat = match_rcode(blob[i], RCode.UNSAT)
#             unsat_item = f"{count_unsat}/{mut_size} {round(count_unsat / (mut_size) * 100, 1)}%"
#             count_timeout = match_rcode(blob[i], RCode.TIMEOUT)
#             timeout_item = f"{count_timeout}/{mut_size} {round(count_timeout / (mut_size) * 100, 1)}%"
#             count_unknown = match_rcode(blob[i], RCode.UNKNOWN)
#             unknown_item = f"{count_unknown}/{mut_size} {round(count_unknown / (mut_size) * 100, 1)}%"
#             times = blob[i][1] / 1000
#             item = [mutations[i], votes[i].value, unsat_item, timeout_item, unknown_item, f"{round(np.mean(times), 2)}", f"{round(np.std(times), 2)}"]
#             table.append(item)
#         print(tabulate(table, headers=["mutation", "status", "unsat", "timeout", "unknown", "mean(second)", "std(second)"], tablefmt="github"))
