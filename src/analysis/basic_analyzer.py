from typing import Dict
# from base.project import PM, QueryType as QType
from base.exper import Experiment, QueryExpResult
from query.analyzer import *
from utils.system_utils import *
from utils.analysis_utils import *
from utils.cache_utils import *

class BasicAnalyzer:
    def __init__(self, exp: Experiment, ana, enable_dummy=False):
        self.exp = exp
        self.ana = ana
        self.__qrs: Dict[str, QueryExpResult] = self.exp.load_sum_table(enable_dummy)
        self.__qr_keys = list(sorted(self.__qrs.keys()))
        self.__cats: Categorizer = ana.categorize_queries(self.__qrs.values())

    def __getitem__(self, base_name):
        return self.__qrs[base_name]

    def __contains__(self, base_name):
        return base_name in self.__qrs
    
    def base_names(self):
        return self.__qr_keys

    def print_plain_status(self):
        for qr in self.__qrs.values():
            qr.print_status()
            print("")

    def get_query_stability(self, base_name):
        return self.__cats.get_category(base_name)

    def get_overall(self):
        return self.__cats

    def print_status(self, verbosity=0):
        log_info(f"exp: {self.exp.exp_name}")
        log_info(f"proj: {self.exp.proj.full_name}")
        log_info(f"ana: {self.ana.name}")

        self.__cats.print_status(skip_empty=True)

        if verbosity == 0:
            return
        
        for cat, cs in self.__cats.items():
            if verbosity == 1 and cat != Stability.UNSTABLE:
                continue
            
            if verbosity == 2 and cat == Stability.STABLE:
                continue

            if len(cs) == 0:
                log_info(f"no {cat.value} queries found")
                continue

            log_info(f"listing {cat.value} queries...")

            for qs in cs:
                self[qs].enforce_timeout(self.ana._timeout)
                self[qs].print_status(verbosity)

    # def get_assert_counts(self, update=False):
    #     from tqdm import tqdm
    #     cache_path = f"asserts/{self.proj.full_name}"
    #     if has_cache(cache_path) and not update:
    #         counts = load_cache(cache_path)
    #     else:
    #         log_info(f"assert counts for {self.proj.full_name}")
    #         counts = dict()
    #         for query_path in tqdm(self.proj.list_queries()):
    #             base_name = os.path.basename(query_path)
    #             counts[base_name] = count_asserts(query_path)
    #         save_cache(cache_path, counts)
    #     return counts

    # def get_veri_times(self):
    #     data = []
    #     for qr in self.__qrs.values():
    #         data.append(qr.get_original_status()[1])
    #     return np.array(data) / 1000

# class GroupAnalyzer:
#     def __init__(self, group_name, ana):
#         self.ana = ana
#         self.group_name = group_name
#         self.orig: ExpAnalyzer = self.load_stability_status(QType.ORIG)
#         self.group = dict()
#         self.group_path = f"data/projects/{self.group_name}"

#     def load_stability_status(self, ptyp):
#         solver = "z3_4_12_2"
#         if self.group_name == "d_ironsht":
#             exp_name = "ironsht"        
#         elif ptyp == QType.ORIG:
#             exp_name = "baseline"
#             if self.group_name == "v_uf":
#                 exp_name = "synthetic"
#         elif ptyp == QType.CORE:
#             exp_name = "unsat_core"
#         elif ptyp == QType.EXTD:
#             exp_name = "unsat_core"
#         elif ptyp == QType.BLOT:
#             exp_name = "bloat"
#             if self.group_name == "d_ironsht":
#                 exp_name = "ironsht"
#         elif ptyp == QType.BLOT_CVC:
#             exp_name = "bloat"
#             solver = "cvc5_1_0_7"
#         elif ptyp == QType.SHKP:
#             exp_name = "shake"
#         elif ptyp == QType.SHKO:
#             exp_name = "oracle"
#         elif ptyp == QType.REVL:
#             exp_name = "opaque"
#         elif ptyp == QType.ORIG_CVC:
#             exp_name = "baseline_cvc"
#             solver = "cvc5_1_0_7"
#         elif ptyp == QType.NLE:
#             exp_name = "verus_nl"
#         else:
#             print(f"[ERROR] unknown project type {ptyp}")
#             assert False

#         proj = PM.load_project(self.group_name, ptyp, enable_dummy=True)
#         exp = ExpPart(exp_name, proj, solver)
#         exp = ExpAnalyzer(exp, self.ana, enable_dummy=True)

#         return exp
