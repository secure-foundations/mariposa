import numpy as np
from enum import Enum
from rcode import RCode
from statsmodels.stats.proportion import proportions_ztest

class Stability(str, Enum):
    UNKNOWN = "unknown"
    UNSOLVABLE = "unsolvable"
    UNSTABLE = "unstable"
    # TIME_UNSTABLE = "time_unstable"
    INCONCLUSIVE = "inconclusive"
    STABLE = "stable"

    def __str__(self) -> str:
        return super().__str__()

    def empty_map():
        em = {c: set() for c in Stability}
        return em

# miliseconds
# def indices_within_timeout(blob, timeout):
#     none_timeout = blob[1] < timeout 
#     return np.where(none_timeout)[0]

def count_within_timeout(blob, rcode, timeout=1e6):
    success = blob[0] == rcode.value
    none_timeout = blob[1] < timeout
    success = np.sum(np.logical_and(success, none_timeout))
    return success

class Analyzer:
    def __init__(self, method):
        self.confidence = 0.05
        self.timeout = 1e6

        self.unsolvable = 5
        self.res_stable = 95
        self.discount = 0.8

        if method == "regression":
            assert False
            # self.categorize_group = self._categorize_group_regression
        elif method == "strict":
            self.categorize_group = self._categorize_strict
        elif method == "z_test":
            self.categorize_group = self._categorize_z_test
        else:
            assert False

    def load(self, obj):
        assert isinstance(obj, dict)

        if "confidence" in obj:
            self.confidence = obj["confidence"]

        if "ana_timeout" in obj:
            self.timeout = obj["ana_timeout"] * 1000

        if "r-unsolvable" in obj:
            self.unsolvable = obj["r-unsolvable"]            

        if "r-stable" in obj:
            self.res_stable = obj["r-stable"]
            
        if "discount" in obj:
            self.discount = obj["discount"]

    # def _categorize_group_regression(self, group_blob):
    #     pres = group_blob[0][0]
    #     ptime = group_blob[1][0]
    #     if pres != RCode.UNSAT.value or ptime > self.timeout:
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
        success = count_within_timeout(group_blob, RCode.UNSAT, self.timeout)

        if success == 0:
            if count_within_timeout(group_blob, RCode.UNKNOWN, self.timeout) == size:
                return Stability.UNKNOWN
            return Stability.UNSOLVABLE

        if success == size:
            return Stability.STABLE

        # if m > self.timeout * self.discount:
        #     return Stability.STABLE
        return Stability.UNSTABLE

    def _categorize_z_test(self, group_blob):
        size =  group_blob.shape[1]

        unsat_indices = group_blob[0] == RCode.UNSAT.value
        nto_indices = group_blob[1] < self.timeout
        valid_indices = np.logical_and(unsat_indices, nto_indices)
        success = np.sum(valid_indices)

        # success = count_within_timeout(group_blob, RCode.UNSAT, self.timeout)
        # if success == 0:
        #     if count_within_timeout(group_blob, RCode.UNKNOWN, self.timeout) == size:
        #         return Stability.UNKNOWN

        value = self.unsolvable/100
        _, p_value = proportions_ztest(count=success,
                                        nobs=size,
                                        value=value, 
                                        alternative='smaller',
                                        prop_var=value)
        if p_value <= self.confidence:
            return Stability.UNSOLVABLE

        value = self.res_stable/100
        _, p_value = proportions_ztest(count=success, 
                                        nobs=size,
                                        value=value,
                                        alternative='smaller',
                                        prop_var=value)

        if p_value <= self.confidence and \
            np.mean(group_blob[1][valid_indices]) < self.timeout * self.discount:
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

    def categorize_queries(self, rows, perturbs=None):
        categories = Stability.empty_map()
        for query_row in rows:
            plain_path = query_row[0]
            res = self.categorize_query(query_row[2], perturbs)[0]
            categories[res].add(plain_path)
        return categories 
