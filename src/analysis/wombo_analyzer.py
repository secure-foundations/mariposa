from ast import Dict
import os
import shutil
from base.defs import QUERY_WIZARD
from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from query.analyzer import QueryAnalyzer, Stability as STB, UnstableReason as UR
from analysis.expr_analyzer import ExperAnalyzer
from utils.analysis_utils import *
from utils.query_utils import count_asserts, is_assertion_subset
from utils.system_utils import print_banner, subprocess_run

def get_quantifier_count(path):
    if os.path.exists(path):
        o = subprocess_run(["rg", "-e" , ":qid ", "-c", path], check=True)[0]
        return int(o)
    return "-"

class WomboAnalyzer:
    def __init__(self, in_group: ProjectGroup):
        solver = FACT.get_solver_by_name("z3_4_12_5")
        # self.step_0(in_group)
        # self.step_1_0(in_group)
        # self.step_1_1(in_group)
        # self.step_2_0(in_group)
        # self.step_2_1(in_group)
        # self.step_3_0(in_group)
        # self.step_4_1(in_group)
        self.report()

    def report(self):
        ana = QueryAnalyzer("60nq")
        
        p0 = FACT.get_group("bench_unstable").get_project(PT.from_str("pins.z3"))

        g0 = FACT.get_group("bench_unstable_0")
        c0 = g0.get_project(PT.from_str("core.z3"))
        e0 = FACT.load_any_experiment(c0)
        e0 = ExperAnalyzer(e0, ana)

        g1 = FACT.get_group("bench_unstable_1")
        c1 = g1.get_project(PT.from_str("core.z3"))
        e1 = FACT.load_any_experiment(c1)
        e1 = ExperAnalyzer(e1, ana)

        g2 = FACT.get_group("bench_unstable_2")
        c2 = g2.get_project(PT.from_str("core.z3"))
        e2 = FACT.load_any_experiment(c2)
        e2 = ExperAnalyzer(e2, ana)

        cats = Categorizer()
        for qid in p0.qids:
            ss = e2.get_query_stability(qid)
            if ss != STB.MISSING_F:
                cats.add_item(ss, qid)
                continue
            ss = e1.get_query_stability(qid)
            if ss != STB.MISSING_F:
                cats.add_item(ss, qid)
                continue
            ss = e0.get_query_stability(qid)
            cats.add_item(ss, qid)

        cats.finalize()
        cats.print_status()
        
        for qid in cats[STB.UNSTABLE]:
            cc = get_quantifier_count(p0.get_ext_path(qid))
            c0c = get_quantifier_count(c0.get_ext_path(qid))
            c1c = get_quantifier_count(c1.get_ext_path(qid))
            c2c = get_quantifier_count(c2.get_ext_path(qid))
            print(f"{cc} {c0c} {c1c} {c2c}")

    def step_0(self, in_group: ProjectGroup):
        pins_p = in_group.get_project(PT.from_str("pins.z3"))

        out_group = FACT.get_group("bench_unstable_0")
        out_p = out_group.get_project(PT.from_str("base.z3"), build=True)
        for qid in pins_p.qids:
            i_path = pins_p.get_ext_path(qid)
            o_path = out_p.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 5 --restarts 5")

    def step_1_0(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_0")
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"), build=True)

        for qid in base.qids:
            i_path = base.get_ext_path(qid)
            o_path = core.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} build-core -i {i_path} -o {o_path} --ids-available --restarts 5 --solver z3_4_8_5")

    def step_1_1(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_0")
        core_p = group.get_project(PT.from_str("core.z3"), build=True)
        core = FACT.load_any_experiment(core_p)
        ana = QueryAnalyzer("60nq")
        core = ExperAnalyzer(core, ana)
        o_group = FACT.get_group("bench_unstable_1")
        o_p = o_group.get_project(PT.from_str("base.z3"), build=True)

        for qid in core.qids:
            s = core.get_query_stability(qid)
            if s == STB.STABLE:
                continue
            if s != STB.UNSTABLE:
                continue
            i_path = core_p.get_ext_path(qid)
            o_path = o_p.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 10 --restarts 10")
            # print(i_path, s)

    def step_2_0(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_1")
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"), build=True)

        for qid in base.qids:
            i_path = base.get_ext_path(qid)
            o_path = core.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} build-core -i {i_path} -o {o_path} --ids-available --restarts 5 --solver z3_4_8_5")

    def step_2_1(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_1")
        core_p = group.get_project(PT.from_str("core.z3"), build=True)
        core = FACT.load_any_experiment(core_p)
        ana = QueryAnalyzer("60nq")
        core = ExperAnalyzer(core, ana)
        o_group = FACT.get_group("bench_unstable_2")
        o_p = o_group.get_project(PT.from_str("base.z3"), build=True)

        for qid in core.qids:
            s = core.get_query_stability(qid)
            if s != STB.UNSTABLE:
                continue
            i_path = core_p.get_ext_path(qid)
            o_path = o_p.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 5 --restarts 10")

    def step_3_0(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_2")
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"), build=True)

        for qid in base.qids:
            i_path = base.get_ext_path(qid)
            o_path = core.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} build-core -i {i_path} -o {o_path} --ids-available --restarts 5 --solver z3_4_8_5")

    def step_4_1(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_2")
        core_p = group.get_project(PT.from_str("core.z3"), build=True)
        core = FACT.load_any_experiment(core_p)
        ana = QueryAnalyzer("60nq")
        core = ExperAnalyzer(core, ana)
        o_group = FACT.get_group("bench_unstable_3")
        o_p = o_group.get_project(PT.from_str("base.z3"), build=True)

        for qid in core.qids:
            s = core.get_query_stability(qid)
            if s != STB.UNSTABLE:
                continue
            i_path = core_p.get_ext_path(qid)
            o_path = o_p.get_ext_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 5 --restarts 10")