from ast import Dict
import os

from tabulate import tabulate
from base.defs import MARIPOSA, QUERY_WIZARD
from base.exper_analyzer import ExperAnalyzer, QueryAnaResult
from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT
from base.query_analyzer import QueryAnalyzer, Stability as STB, FailureType as UR
from utils.analysis_utils import *
from utils.query_utils import count_asserts, is_assertion_subset
from utils.system_utils import print_banner


class CoreQueryStatus:
    def __init__(
        self, qid: str, base: QueryAnaResult, core: QueryAnaResult, extd: QueryAnaResult
    ):
        self.qid = qid

        self.base, self.br, self.base_path = (
            base.stability,
            base.failure_type,
            base.query_path,
        )
        self.core, self.cr, self.core_path = (
            core.stability,
            core.failure_type,
            core.query_path,
        )
        self.extd, self.er, self.extd_path = (
            extd.stability,
            extd.failure_type,
            extd.query_path,
        )

        self.__init_patched_status()

    def get_issue(self):
        if self.base == STB.UNSOLVABLE:
            return None
        if self.core in {STB.UNSTABLE, STB.STABLE}:
            return None
        return self.base.value, self.core.value, self.extd.value

    def __init_patched_status(self):
        if self.core in {STB.STABLE, STB.UNSTABLE}:
            self.patch = self.core
            self.patch_path = self.core_path
            self.patch_reason = self.cr
            return

        if self.extd in {STB.STABLE, STB.UNSTABLE}:
            self.patch = self.extd
            self.patch_path = self.extd_path
            self.patch_reason = self.er
            return

        self.patch = self.base
        self.patch_path = self.base_path
        self.patch_reason = self.br

    def core_is_enabled(self):
        return self.patch_path != self.base_path

    # def sanity_check(self):
    #     if os.path.exists(self.core_path):
    #         log_check(is_assertion_subset(self.base_path, self.core_path), f"{self.core_path} is not a subset!")
    #     if os.path.exists(self.extd_path):
    #         log_check(is_assertion_subset(self.base_path, self.extd_path), f"{self.extd_path} is not a subset!")


class CoreAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        self.group = group

        base = group.get_project(PT.from_str("base.z3"))
        self.base: ExperAnalyzer = FACT.load_any_analysis(
            base, ana
        )
        core = group.get_project(PT.from_str("core.z3"), build=True)
        self.core: ExperAnalyzer = FACT.load_any_analysis(
            core, ana, group_qids=self.base.qids
        )
        extd = group.get_project(PT.from_str("extd.z3"), build=True)
        self.extd: ExperAnalyzer = FACT.load_any_analysis(
            extd, ana, group_qids=self.base.qids
        )

        self.qids: Dict[str, CoreQueryStatus] = dict()
        # self.base.print_status()
        # self.core.print_status()
        # self.extd.print_status()

        for qid in self.base.qids:
            bs = self.base[qid]
            cs = self.core[qid]
            es = self.extd[qid]
            cqs = CoreQueryStatus(qid, bs, cs, es)
            self.qids[qid] = cqs

        self.adjust_status()
        # self.build_pre_inst()

        # self.__init_issue_status()
        # self.issues.print_status()
        # self.suggest_issue_fixes()

    # def unify_core(self):

    def build_pre_inst(self):
        pins = self.group.get_project(PT.from_str("pins.z3"), build=True)
        woco = self.group.get_project(PT.from_str("woco.z3"), build=True)
        for qid in self.core_adj[STB.UNSTABLE]:
            qr = self.qids[qid]
            out_path = woco.get_path(qid)
            if qr.core_is_enabled():
                print(
                    MARIPOSA,
                    "-a",
                    "pre-inst-z3",
                    "-i",
                    qr.patch_path,
                    "-o",
                    pins.get_path(qid),
                )
            # else:
            # if os.path.exists(pins.get_path(f"temp_proj/{qid}.smt2")):
            #     continue
            # print(QUERY_WIZARD, "build-core",
            #   "-i", qr.patch_path,
            #   "-o", f"temp_proj/{qid}.smt2",
            #   "-s", "z3_4_12_5",
            #   "--timeout", "70",
            #   "--ids-available",
            #   "--restarts", "4")

    def print_status(self):
        print_banner("Report " + self.group.gid)
        print("")

        b = self.base_adj
        c = self.core_adj

        b.print_status(title="base")
        c.print_status(title="core")

        print("")
        print_banner("Instability Mitigated")

        mitigated = {"tally": [0, 0]}

        for qid in b[STB.UNSTABLE]:
            cqs = self.qids[qid]
            if cqs.br not in mitigated:
                mitigated[cqs.br] = [0, 0]
            if cqs.patch == STB.STABLE:
                mitigated[cqs.br][0] += 1
                mitigated["tally"][0] += 1
                # print(qid)
            mitigated[cqs.br][1] += 1
            mitigated["tally"][1] += 1

        table = [["reason", "count", "mitigated", "percentage"]]
        for k in list(UR) + ["tally"]:
            if k not in mitigated:
                continue
            unstable = mitigated[k][1]
            row = [k, unstable, mitigated[k][0]]
            if unstable == 0:
                row += ["-"]
            else:
                row += [f"{mitigated[k][0]*100/unstable:.2f}%"]
            table += [row]

        print(tabulate(table, headers="firstrow", tablefmt="github"))

        print("")
        print_banner("Stability Preserved")
        pres, total = 0, 0

        for qid in b[STB.STABLE]:
            if qid in c[STB.STABLE]:
                pres += 1
            total += 1
        if total != 0:
            print(f"preserved: {pres}/{total} ({pres*100/total:.2f}%)")
        else:
            print("no stable queries in the base set")
        print("")
        print_banner("Instability Introduced")

        intro = Categorizer()

        for qid in c[STB.UNSTABLE]:
            cqs = self.qids[qid]
            if cqs.base != STB.STABLE:
                continue
            intro.add_item(cqs.patch_reason, qid)
        intro.finalize()

        if intro.total == 0:
            print("no unstable queries introduced")
        else:
            intro.print_status()
        print("")

        print_banner("Report End")

    def get_assert_counts(self):
        from tqdm import tqdm

        assert_counts = []
        for qid in tqdm(self.qids):
            cqr = self.qids[qid]
            bc = count_asserts(cqr.base_path)
            if cqr.core_is_enabled():
                cc = count_asserts(cqr.core_path)
            else:
                cc = np.nan
            assert_counts += [[bc, cc]]
        return np.array(assert_counts)

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
            i = self.base.exp.proj.get_path(q)
            o = self.extd.exp.proj.get_path(q)
            print("./src/query_wizard.py build-core", "-i", i, "-o", o)

        incomplete = self.get_incomplete_core_qids()

        print("")
        print_banner("Incomplete Core Queries")

        for q in incomplete:
            i = self.base.exp.proj.get_path(q)
            c = self.core.exp.proj.get_path(q)
            o = self.extd.exp.proj.get_path(q)
            print(
                "./src/query_wizard.py complete-core",
                "-i",
                i,
                "--core-query-path",
                c,
                "-o",
                o,
            )

        print("")
        print_banner("Patched Core Queries")

        for qid in self.extd.qids:
            c = self.core.exp.proj.get_path(qid)
            e = self.extd.exp.proj.get_path(qid)
            b = self.base.exp.proj.get_path(qid)
            cc = count_asserts(c)
            ec = count_asserts(e)
            bc = count_asserts(b)

            if ec / bc > 0.1:
                print(bc, cc, ec)
                print(
                    "./src/query_wizard.py complete-core",
                    "-i",
                    e,
                    "--core-query-path",
                    c,
                    "-o",
                    e,
                )

        print("")

    def get_no_file_core_qids(self):
        no_file = []
        for (_, cs, es), qids in self.issues.items():
            if cs == STB.MISSING_F and es == STB.MISSING_F:
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

    def adjust_status(self):
        base_adj = Categorizer()
        core_adj = Categorizer()

        for qid, cq in self.qids.items():
            if cq.base == STB.UNSOLVABLE:
                continue
            base_adj.add_item(cq.base, qid)
            core_adj.add_item(cq.patch, qid)

        base_adj.finalize()
        core_adj.finalize()

        self.base_adj = base_adj
        self.core_adj = core_adj
