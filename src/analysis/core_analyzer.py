from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT
from query.analyzer import QueryAnalyzer, Stability
from analysis.expr_analyzer import ExprAnalyzer
from enum import Enum
from utils.analysis_utils import *
from utils.query_utils import count_asserts
from utils.system_utils import print_banner

# class CoreQueryStatus:
#     def __init__(self, qid: str, base: Stability, core: Stability, extd: Stability):
#         self.qid = qid
#         self.base = base
#         self.core = core
#         self.extd = extd

class CoreAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        solver = FACT.get_solver_by_name("z3_4_12_5")

        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"))
        extd = group.get_project(PT.from_str("extd.z3"))

        base = FACT.load_experiment("quake", base, solver)
        core = FACT.load_experiment("default", core, solver)
        extd = FACT.build_experiment("default", extd, solver)

        self.base = ExprAnalyzer(base, ana)
        self.core = ExprAnalyzer(core, ana)
        self.extd = ExprAnalyzer(extd, ana, enable_dummy=True)

        self.__init_issue_status()
        self.issues.print_status()
        print("")

        # self.print_patched_incomplete_status()
        # self.try_fix_issues()
    self.get_unified_status()

    def __init_issue_status(self):
        issues = Categorizer()

        for qid in self.base.qids:
            bs = self.base.get_query_stability(qid)
            cs = self.core.get_query_stability(qid)
            es = self.extd.get_query_stability(qid)
            if bs == Stability.UNSOLVABLE:
                # not interesting if the base is unsolvable
                continue
            if cs == Stability.UNSTABLE or cs == Stability.STABLE:
                # the core is unstable, fine...
                # if the core is stable, great
                continue
            if es == Stability.STABLE:
                # not interesting if the extension is stable
                continue
            issues.add_item((bs.value, cs.value, es.value), qid)

        issues.finalize()
        self.issues = issues

    def try_fix_issues(self):
        print_banner("Missing Core Queries")
        no_file = self.get_no_file_core_qids()

        for q in no_file:
            i = self.base.exp.proj.get_ext_path(q)
            o = self.extd.exp.proj.get_ext_path(q)
            print("./src/query_wizard.py build-core", "-i", i, "-o", o)

        incomplete = self.get_incomplete_core_qids()

        print("")
        print_banner("Incomplete Core Queries")

        for q in incomplete:
            i = self.base.exp.proj.get_ext_path(q)
            c = self.core.exp.proj.get_ext_path(q)
            o = self.extd.exp.proj.get_ext_path(q)
            print("./src/query_wizard.py complete-core", "-i", i, "--core-query-path", c, "-o", o)

    def get_no_file_core_qids(self):
        no_file = []
        for (_, cs, es), qids in self.issues.items():
            if cs == Stability.MISSING_F and \
                es == Stability.MISSING_F:
                no_file.extend(qids)
        return no_file

    def get_incomplete_core_qids(self):
        incomplete = []
        for (bs, cs, es), qids in self.issues.items():
            if es != Stability.MISSING_F:
                continue
            if cs == Stability.UNSOLVABLE:
                incomplete.extend(qids)
        return incomplete

    def print_patched_incomplete_status(self):
        for qid in self.extd.qids:
            c = self.core.exp.proj.get_ext_path(qid)
            e = self.extd.exp.proj.get_ext_path(qid)
            cc = count_asserts(c)
            ec = count_asserts(e)

            if np.isnan(cc):
                continue

            if ec - cc > 20 and ec / cc > 1.5:
                print(cc, ec)
                print("./src/query_wizard.py complete-core", "-i", e, "--core-query-path", c, "-o", e)
                # print(qid, cc, ec)

    def get_unified_status(self):
        adjusted = Categorizer()
        unified = Categorizer()

        for qid in self.base.qids:
            bs = self.base.get_query_stability(qid)
            if bs == Stability.UNSOLVABLE:
                continue
            adjusted.add_item(bs, qid)
            cs = self.core.get_query_stability(qid)
            es = self.extd.get_query_stability(qid)

            if cs == Stability.MISSING_F or cs == Stability.UNSOLVABLE:
                unified.add_item(es, qid)
            else:
                unified.add_item(cs, qid)

        unified.finalize()
        adjusted.finalize()

        unified.print_status()
        print("")
        adjusted.print_status()