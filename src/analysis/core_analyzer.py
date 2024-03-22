from ast import Dict
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from query.analyzer import QueryAnalyzer, Stability as STB
from analysis.expr_analyzer import ExprAnalyzer
from utils.analysis_utils import *
from utils.query_utils import count_asserts
from utils.system_utils import print_banner

class CoreQueryStatus:
    def __init__(self, qid: str, 
                 base: STB, base_path,
                 core: STB, core_path,
                 extd: STB, extd_path):
        self.qid = qid

        self.base, self.base_path = base, base_path
        self.core, self.core_path = core, core_path
        self.extd, self.extd_path = extd, extd_path
        
        self.__init_patched_status()

    def get_issue(self):
        if self.base == STB.UNSOLVABLE:
            return None
        if self.core in { STB.UNSTABLE, STB.STABLE}:
            return None
        return self.base.value, self.core.value, self.extd.value

    def __init_patched_status(self):
        if self.core in {STB.STABLE, STB.UNSTABLE}:
            self.patch = self.core
            self.patch_path = self.core_path
            return

        if self.extd in {STB.STABLE, STB.UNSTABLE}:
            self.patch = self.extd
            self.patch_path = self.extd_path
            return
    
        self.patch = self.base
        self.patch_path = self.base_path

class CoreAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        solver = FACT.get_solver_by_name("z3_4_12_5")

        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"))
        extd = group.get_project(PT.from_str("extd.z3"))

        base = FACT.load_any_experiment(base)
        log_check(base.solver == solver, "base project is not using z3_4_12_5")
        core = FACT.load_any_experiment(core)
        log_check(core.solver == solver, "core project is not using z3_4_12_5")
        extd = FACT.build_experiment("default", extd, solver)

        self.base = ExprAnalyzer(base, ana)
        self.core = ExprAnalyzer(core, ana)
        self.extd = ExprAnalyzer(extd, ana, enable_dummy=True)

        self.qids: Dict[str, CoreQueryStatus] = dict()

        for qid in self.base.qids:
            bs = self.base.get_query_stability(qid)
            bp = self.base.exp.proj.get_ext_path(qid)
            cs = self.core.get_query_stability(qid)
            cp = self.core.exp.proj.get_ext_path(qid)
            es = self.extd.get_query_stability(qid)
            ep = self.extd.exp.proj.get_ext_path(qid)
            cqs = CoreQueryStatus(qid, bs, bp, cs, cp, es, ep)
            self.qids[qid] = cqs

        # self.__init_issue_status()
        # self.issues.print_status()
        # self.suggest_issue_fixes()
        # self.get_trace_candidate()

        base_adj, core_adj = self.get_adjusted_status()
        base_adj.print_status()
        core_adj.print_status()

        m = base_adj.get_migration_status(core_adj)
        for k, v in m.items():
            print(k)
            v.print_status()

        # print(NINJA_BUILD_RULES)
        # for qid, cq in self.qids.items():
        #     if cq.core == STB.STABLE:
        #         out_path = self.base.exp.proj.get_ext_path(qid, KnownExt.Z3_TRACE)
        #         # print(f"build {out_path}: trace-z3", cq.patch_path)
        #         print(f"~/axiom-profiler-2/target/release/smt-log-parser {out_path}")

    def __init_issue_status(self):
        issues = Categorizer()
        for qid, cq in self.qids.items():
            issue = cq.get_issue()
            if issue is None:
                continue
            issues.add_item(issue, qid)
        issues.finalize()
        self.issues = issues

    def suggest_issue_fixes(self):
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

        print("")
        print_banner("Patched Core Queries")

        for qid in self.extd.qids:
            c = self.core.exp.proj.get_ext_path(qid)
            e = self.extd.exp.proj.get_ext_path(qid)
            b = self.base.exp.proj.get_ext_path(qid)
            cc = count_asserts(c)
            ec = count_asserts(e)
            bc = count_asserts(b)

            if ec / bc > 0.1:
                print(bc, cc, ec)
                print("./src/query_wizard.py complete-core", "-i", e, "--core-query-path", c, "-o", e)

    def get_no_file_core_qids(self):
        no_file = []
        for (_, cs, es), qids in self.issues.items():
            if cs == STB.MISSING_F and \
                es == STB.MISSING_F:
                no_file.extend(qids)
        return no_file

    def get_incomplete_core_qids(self):
        incomplete = []
        for (_, cs, es), qids in self.issues.items():
            if es != STB.MISSING_F:
                continue
            if cs == STB.UNSOLVABLE:
                incomplete.extend(qids)
        return incomplete

    def get_adjusted_status(self):
        base_adj = Categorizer()
        core_adj = Categorizer()

        for qid, cq in self.qids.items():
            if cq.base == STB.UNSOLVABLE:
                continue
            base_adj.add_item(cq.base, qid)
            core_adj.add_item(cq.patch, qid)

        base_adj.finalize()
        core_adj.finalize()
        return base_adj, core_adj

    def get_trace_candidate(self):
        core_ok = 0
        for qid in self.qids:

            if qid in self.core and self.core[qid].get_fast_pass():
                core_ok += 1
            if qid in self.extd and self.extd[qid].get_fast_pass():
                core_ok += 1
        print(core_ok, len(self.qids))
