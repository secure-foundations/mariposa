from typing import Dict
# from base.project import FACT, QueryType as QType
from base.exper import Experiment, QueryExpResult
from query.analyzer import *
from utils.query_utils import Mutation, emit_mutant_query
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

    def __getitem__(self, qid):
        return self.__qrs[qid]

    def __contains__(self, qid):
        return qid in self.__qrs

    @property
    def qids(self):
        return self.__qr_keys

    def print_plain_status(self):
        for qr in self.__qrs.values():
            qr.print_status()
            print("")

    def get_query_stability(self, qid):
        return self.__cats.get_category(qid)

    def get_overall(self):
        return self.__cats

    def print_status(self, verbosity=0):
        print(f"exp config:\t{self.exp.exp_name}")
        print(f"project dir:\t{self.exp.proj.sub_root}")
        print(f"solver path:\t{self.exp.solver.path}")
        print(f"analyzer:\t{self.ana.name}")

        print("")
        print_banner("Overall Report")
        self.__cats.print_status(skip_empty=True)
        print("")

        if verbosity == 0:
            return

        for cat, cs in self.__cats.items():
            if verbosity <= 1 and cat != Stability.UNSTABLE:
                continue
            
            if verbosity <= 2 and cat == Stability.UNSOLVABLE:
                continue

            if verbosity <= 3 and cat == Stability.STABLE:
                continue

            ccount = len(cs)

            if ccount == 0:
                continue

            for i, qs in enumerate(cs):
                print_banner(f"{cat.value} ({i+1}/{ccount})")
                self[qs].enforce_timeout(self.ana._timeout)
                self[qs].print_status(verbosity)
            print("")
        print_banner("Report End")

    def get_mutant_details(self, qr):
        rows = self.exp.get_mutants(qr.query_path)
        passed, failed = [], []

        for (m_path, rc, et) in rows:
            rc = RCode(rc)
            if self.ana.is_timeout(et):
                rc = RCode.TIMEOUT
            mutation, seed = Experiment.parse_mutant_path(m_path)

            if mutation == Mutation.QUAKE:
                # TODO: handle quake if needed
                continue

            if rc == RCode.UNSAT:
                passed += [(mutation, seed, None)]
            else:
                failed += [(mutation, seed, rc)]
        return passed, failed

    def get_unstable_query_mutants(self):
        res = []
        for qid in self.qids:
            qr = self[qid]

            if self.get_query_stability(qid) != Stability.UNSTABLE:
                continue

            s, f = self.get_mutant_details(qr)

            if len(s) == 0 or len(f) == 0:
                log_warn(f"only quake was effective, skipping {qid}")
                continue

            res.append((qr, s, f))
        return res

    def do_stuff(self):
        cats = Categorizer([c for c in UnstableReason])
        for qid in self.qids:
            qr = self[qid]
            if self.get_query_stability(qid) != Stability.UNSTABLE:
                continue
            # print(f"{qid} is unstable")
            qr.enforce_timeout(60 * 1000)
            cats.add_item(self.ana.sub_categorize_unstable(qr.blob).value, qid)
            # qr.print_status(verbosity=3)
            # break
        cats.finalize()
        cats.print_status()

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
