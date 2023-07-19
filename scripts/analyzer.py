import numpy as np
from basic_utils import *
from enum import Enum
from rcode import RCode
from statsmodels.stats.proportion import proportions_ztest
from tabulate import tabulate

def is_ratio(x):
    return type(x) == float and 0 < x < 1

def percentage(a, b):
    return a * 100 / b

def get_category_percentages(categories):
    percentages = dict()
    total = sum([len(i) for i in categories.values()])
    for c, i in categories.items():
        percentages[c] = percentage(len(i), total)
    return percentages, total

class Stability(str, Enum):
    UNKNOWN = "unknown"
    UNSOLVABLE = "unsolvable"
    UNSTABLE = "unstable"
    # TIME_UNSTABLE = "time_unstable"
    INCONCLUSIVE = "inconclusive"
    STABLE = "stable"
    TALLY = "tally"

    def __str__(self) -> str:
        return super().__str__()

    def empty_map():
        em = {c: set() for c in Stability}
        return em

def count_within_timeout(blob, rcode, timeout=1e6):
    if timeout == None:
        return np.sum(blob[0] == rcode.value)
    success = blob[0] == rcode.value
    none_timeout = blob[1] < timeout
    success = np.sum(np.logical_and(success, none_timeout))
    return success

class Analyzer:
    def __init__(self, confidence, timeout, r_solvable, r_stable, discount, method):
        self.confidence = confidence
        self._timeout = timeout * 1000 if timeout != None else None
        self.r_solvable = r_solvable * 100
        self.r_stable = r_stable * 100
        self.discount = discount

        exit_with_on_fail(timeout == None or timeout > 0, "[ERROR] timeout (seconds) must be positive or None")
        exit_with_on_fail(is_ratio(confidence), "[ERROR] confidence must be a value between 0 and 1")
        exit_with_on_fail(is_ratio(r_solvable), "[ERROR] r-solvable must be a value between 0 and 1")
        exit_with_on_fail(is_ratio(r_stable), "[ERROR] r-stable must be a value between 0 and 1")
        exit_with_on_fail(is_ratio(discount), "[ERROR] discount must be a value between 0 and 1")

        if method == "strict":
            self.categorize_group = self._categorize_strict
        elif method == "z_test":
            self.categorize_group = self._categorize_z_test

    # def _categorize_group_regression(self, group_blob):
    #     pres = group_blob[0][0]
    #     ptime = group_blob[1][0]
    #     if pres != RCode.UNSAT.value or ptime > self._timeout:
    #         return Stability.UNSOLVABLE

    #     timeout = max(ptime * 1.5, ptime + 50000)
    #     success = count_within_timeout(group_blob, RCode.UNSAT, timeout)

    #     if success < len(group_blob[0]) * 0.8:
    #         return Stability.RES_UNSTABLE

    #     size = len(group_blob[0])
    #     if success != size:
    #         return Stability.RES_UNSTABLE
    #     return Stability.STABLE

    def _categorize_strict(self, group_blob):
        size = len(group_blob[0])
        success = count_within_timeout(group_blob, RCode.UNSAT, self._timeout)

        if success == 0:
            if count_within_timeout(group_blob, RCode.UNKNOWN, self._timeout) == size:
                return Stability.UNKNOWN
            return Stability.UNSOLVABLE

        if success == size:
            return Stability.STABLE

        # if m > self._timeout * self.discount:
        #     return Stability.STABLE
        return Stability.UNSTABLE

    def _categorize_z_test(self, group_blob):
        size =  group_blob.shape[1]

        unsat_indices = group_blob[0] == RCode.UNSAT.value
        if self._timeout == None:
            nto_indices = np.ones(size, dtype=bool)
        else:
            nto_indices = group_blob[1] < self._timeout
        valid_indices = np.logical_and(unsat_indices, nto_indices)
        success = np.sum(valid_indices)

        # success = count_within_timeout(group_blob, RCode.UNSAT, self._timeout)
        # if success == 0:
        #     if count_within_timeout(group_blob, RCode.UNKNOWN, self._timeout) == size:
        #         return Stability.UNKNOWN

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

    def categorize_query(self, group_blobs, perturbs=None):
        votes = dict()
        if perturbs is None:
            perturbs = [i for i in range(group_blobs.shape[0])]
        for i in perturbs:
            votes[i] = self.categorize_group(group_blobs[i])
        ress = set(votes.values())
        if ress == {Stability.INCONCLUSIVE}:
            return Stability.INCONCLUSIVE, votes
        ress -= {Stability.INCONCLUSIVE}
        if len(ress) == 1:
            return ress.pop(), votes
        return Stability.UNSTABLE, votes

    def categorize_queries(self, rows, perturbs=None, tally=False):
        categories = Stability.empty_map()
        for query_row in rows:
            plain_path = query_row[0]
            res = self.categorize_query(query_row[2], perturbs)[0]
            categories[res].add(plain_path)
        if tally:
            tally = set.union(*categories.values())
            categories[Stability.TALLY] = tally
        return categories 

    def dump_query_status(self, mutations, blob):
        status, votes = self.categorize_query(blob)

        table = [["overall", status, "x", "x", "x"]]
        mut_size = blob.shape[2]

        for i in range(len(mutations)):
            count_unsat = count_within_timeout(blob[i], RCode.UNSAT, timeout=self._timeout)
            unsat_item = f"{count_unsat}/{mut_size} {round(count_unsat / (mut_size) * 100, 1)}%"
            count_timeout = count_within_timeout(blob[i], RCode.TIMEOUT, timeout=self._timeout)
            timeout_item = f"{count_timeout}/{mut_size} {round(count_timeout / (mut_size) * 100, 1)}%"
            count_unknown = count_within_timeout(blob[i], RCode.UNKNOWN, timeout=self._timeout)
            unknown_item = f"{count_unknown}/{mut_size} {round(count_unknown / (mut_size) * 100, 1)}%"
            times = np.clip(blob[i][1], 0, self._timeout) / 1000
            item = [mutations[i], votes[i].value, unsat_item, timeout_item, unknown_item, f"{round(np.mean(times), 2)}", f"{round(np.std(times), 2)}"]
            table.append(item)
        print(tabulate(table, headers=["mutation", "status", "unsat", "timeout", "unknown", "mean(second)", "std(second)"], tablefmt="github"))

