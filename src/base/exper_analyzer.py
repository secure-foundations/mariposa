from typing import Dict
# from base.project import FACT, QueryType as QType
from base.exper import Experiment, QueryExpResult
from base.project import get_qid
from base.query_analyzer import *
from base.defs import delegate
from utils.query_utils import Mutation
from utils.system_utils import *
from utils.analysis_utils import *
from utils.cache_utils import *

@delegate('qer', 'get_mean_time', 'get_original_status')
class QueryAnaResult:
    def __init__(self, qer: QueryExpResult, ss: Stability, ft: FailureType):
        self.qid = qer.qid
        self.query_path = qer.query_path
        self.qer: QueryExpResult = qer
        self.stability: Stability = ss
        self.failure_type: FailureType = ft

    def print_status(self, verbosity=0):
        print(f"\n{self.query_path}")
        if self.failure_type != FailureType.NONE:
            print(f"main failure type:\t{self.failure_type}")
        print("")
        # proc = find_verus_procedure_name(self.query_path)
        # if proc != None:
        #     print(f"procedure name:\t\t{proc}")
        self.qer.print_status(verbosity)

@delegate('exp', 'get_path', 'list_queries', 'get_log_dir')
class ExperAnalyzer:
    def __init__(self, exp: Experiment, ana: QueryAnalyzer, allow_missing_exper=False, group_qids=None):
        self.exp = exp
        self.ana: QueryAnalyzer = ana
        qers = self.exp.load_sum_table()

        path_exists_qids = set([get_qid(p) for p in self.list_queries()])

        log_check(path_exists_qids.issuperset(set(qers.keys())), 
                    "there are queries experimented, but no files exist for them")

        if not allow_missing_exper:
            log_check(path_exists_qids == set(qers.keys()), 
                        "there are queries with files, but no experiments done")

        if group_qids is None:
            group_qids = path_exists_qids
        else:
            group_qids = set(group_qids)

        log_check(group_qids.issuperset(path_exists_qids), 
                    "group qids should be a superset of analyzed queries")

        self.stability_categories: Categorizer = Categorizer()
        self.failure_types: Categorizer = Categorizer([c for c in FailureType])
        self.__qrs: Dict[str, QueryAnaResult] = dict()

        for qid in group_qids:
            if qid in qers:
                qer = qers[qid]
                ss = ana.categorize_query(qer)[0]
                ft = ana.get_failure_type(qer.blob)
            else:
                if qid in path_exists_qids:
                    ss = Stability.MISSING_E
                    ft = FailureType.MISSING
                else:
                    ss = Stability.MISSING_F
                    ft = FailureType.MISSING
                # make a dummy query result
                qer = QueryExpResult(self.get_path(qid))
            self.__qrs[qid] = QueryAnaResult(qer, ss, ft)
            self.stability_categories.add_item(ss, qid)
            self.failure_types.add_item(ft, qid)

        self.stability_categories.finalize()
        self.failure_types.finalize()

        self.__qr_keys = list(sorted(self.__qrs.keys()))

    def __getitem__(self, qid) -> QueryAnaResult:
        return self.__qrs[qid]

    def __contains__(self, qid):
        return qid in self.__qrs

    @property
    def qids(self):
        return self.__qr_keys

    def print_plain_status(self):
        cats = Categorizer()
        for qid in self.qids:
            qr = self[qid]
            rc, et = qr.get_original_status()
            cats.add_item(RCode(rc), qid)
        cats.finalize()
        cats.print_status()

    def print_status(self, category_verbosity=0, query_verbosity=0):
        print_banner("Overall Report")
        print("")

        self.exp.print_info()
        print(f"analyzer:\t{self.ana.name}\n")
        
        self.stability_categories.print_status(skip_empty=True)
        # self.failure_types.print_status(skip_empty=True)
        print("")

        if category_verbosity == 0:
            print_banner("Report End")
            return

        for cat, cs in self.stability_categories.items():
            if category_verbosity <= 1 and cat != Stability.UNSTABLE:
                continue

            if category_verbosity <= 2 and cat == Stability.UNSOLVABLE:
                continue

            if category_verbosity <= 3 and cat == Stability.STABLE:
                continue

            ccount = len(cs)

            if ccount == 0:
                continue

            for i, qid in enumerate(cs):
                print_banner(f"{cat.value} ({i+1}/{ccount})")
                self[qid].print_status(query_verbosity)

                if query_verbosity >= 2:
                    self.print_mutant_details(self[qid])
            print("")
        print_banner("Report End")

    def get_mutant_details(self, qr):
        rows = self.exp.get_mutants(qr.query_path)
        passed, failed = dict(), dict()
        for (m_path, rc, et) in rows:
            rc = RCode(rc)
            if et >= self.exp.timeout * 1000:
                rc = RCode.TIMEOUT
            et = round(et/1000, 2)

            mutation, seed = Experiment.parse_mutant_path(m_path)

            if mutation == Mutation.QUAKE:
                # TODO: handle quake if needed
                continue

            if rc == RCode.UNSAT:
                passed[m_path] = (mutation, seed, rc, et)
            else:
                failed[m_path] = (mutation, seed, rc, et)
        return passed, failed

    def print_mutant_details(self, qr):
        passed, failed = self.get_mutant_details(qr)
        print(f"Passed Mutants ({len(passed)}):")
        for m_path, (mutation, seed, rc, et) in passed.items():
            print(f"{m_path} - {rc} - {et}")
        print("")
        print(f"Failed Mutants ({len(failed)}):")
        for m_path, (mutation, seed, rc, et) in failed.items():
            print(f"{m_path} - {rc} - {et}")

    # def get_unstable_query_mutants(self):
    #     res = []
    #     for qid in self.qids:
    #         qr = self[qid]

    #         if self.get_stability(qid) != Stability.UNSTABLE:
    #             continue

    #         s, f = self.get_mutant_details(qr)

    #         if len(s) == 0 or len(f) == 0:
    #             log_warn(f"only quake was effective, skipping {qid}")
    #             continue

    #         res.append((qr, s, f))
    #     return res