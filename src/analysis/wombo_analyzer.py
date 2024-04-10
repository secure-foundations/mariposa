import os
from base.defs import QUERY_WIZARD
from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT, get_qid
from base.query_analyzer import QueryAnalyzer, Stability as STB
from base.exper_analyzer import ExperAnalyzer
from utils.analysis_utils import *
from utils.system_utils import subprocess_run

def get_quantifier_count(path):
    if os.path.exists(path):
        o = subprocess_run(["rg", "-e" , ":qid ", "-c", path], check=True)[0]
        return int(o)
    return "-"

class WomboAnalyzer:
    def __init__(self, in_group: ProjectGroup):
        self.ana = QueryAnalyzer("60nq")
        # self.step_0(in_group)
        # self.step_1_0(in_group)
        # self.step_1_1(in_group)
        # self.step_2_1(in_group)
        # self.report()
        base_p = in_group.get_project(PT.from_str("woco.z3"))
        e0 = FACT.load_any_experiment(base_p)
        e0 = ExperAnalyzer(e0, self.ana)

        # for qid in base.qids:
            

    # def report(self):
        
    #     p0 = FACT.get_group("bench_unstable").get_project(PT.from_str("pins.z3"))
    #     p1 = FACT.get_group("bench_unstable").get_project(PT.from_str("woco.z3"))

    #     g0 = FACT.get_group("bench_unstable_0")
    #     c0 = g0.get_project(PT.from_str("core.z3"))
    #     e0 = FACT.load_any_experiment(c0)
    #     e0 = ExperAnalyzer(e0, ana)

    #     g1 = FACT.get_group("bench_unstable_1")
    #     c1 = g1.get_project(PT.from_str("core.z3"))
    #     e1 = FACT.load_any_experiment(c1)
    #     e1 = ExperAnalyzer(e1, ana)

    #     g2 = FACT.get_group("bench_unstable_2")
    #     c2 = g2.get_project(PT.from_str("core.z3"))
    #     e2 = FACT.load_any_experiment(c2)
    #     e2 = ExperAnalyzer(e2, ana)

    #     cats = Categorizer()
    #     for qid in p0.qids:
    #         ss = e2.get_query_stability(qid)
    #         if ss != STB.MISSING_F:
    #             cats.add_item(ss, qid)
    #             continue
    #         ss = e1.get_query_stability(qid)
    #         if ss != STB.MISSING_F:
    #             cats.add_item(ss, qid)
    #             continue
    #         ss = e0.get_query_stability(qid)
    #         cats.add_item(ss, qid)

    #     cats.finalize()
    #     cats.print_status()

    def step_1_0(self, group: ProjectGroup):
        in_p = group.get_project(PT.from_str("pins.z3"))
        g0 = FACT.get_group("bench_unstable_0")
        out_p = g0.get_project(PT.from_str("base.z3"), build=True)

        for qid in in_p.qids:
            i_path = in_p.get_path(qid)
            o_path = out_p.get_path(qid)
            if os.path.exists(o_path):
                continue
            # print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 10 --restarts 10")
            print(f"cp {i_path} {o_path}")

    def step_1_1(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_0")
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"), build=True)

        for qid in base.qids:
            i_path = base.get_path(qid)
            o_path = core.get_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} build-core -i {i_path} -o {o_path} --ids-available --restarts 5 --solver z3_4_8_5 --timeout 65")

    def step_1_2(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_0")
        base_p = group.get_project(PT.from_str("base.z3"))
        core_p = group.get_project(PT.from_str("core.z3"))
        extd_p = group.get_project(PT.from_str("extd.z3"), build=True)
        ana = QueryAnalyzer("60nq")
        core = ExperAnalyzer(FACT.load_any_experiment(core_p), ana)
        for qid in core.qids:
            s = core.get_query_stability(qid)
            if s != STB.UNSOLVABLE:
                continue
            i_path = base_p.get_path(qid)
            c_path = core_p.get_path(qid)
            o_path = extd_p.get_path(qid)
            if os.path.exists(o_path):
                continue
            print(QUERY_WIZARD, "complete-core", "-i", i_path, "--core-query-path", c_path, "-o", o_path)

    def step_2_0(self, group: ProjectGroup):
        g0 = FACT.get_group("bench_unstable_0")
        g1 = FACT.get_group("bench_unstable_1")
        in_p = g0.get_project(PT.from_str("core.z3"))
        out_p = g1.get_project(PT.from_str("base.z3"), build=True)
        for qid in in_p.qids:
            i_path = in_p.get_path(qid)
            o_path = out_p.get_path(qid)
            if os.path.exists(o_path):
                continue
            print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 45 --restarts 10")
            # print(f"cp {i_path} {o_path}")

    def step_2_1(self, group: ProjectGroup):
        group = FACT.get_group("bench_unstable_1")
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"), build=True)

        for qid in base.qids:
            i_path = base.get_path(qid)
            o_path = core.get_path(qid)
            if os.path.exists(o_path):
                continue
            # print(f"{QUERY_WIZARD} build-core -i {i_path} -o {o_path} --ids-available --restarts 5 --solver z3_4_12_5 --timeout 65")
            print(f"cp {i_path} {o_path}")

    #     group = FACT.get_group("bench_unstable_0")
    #     core_p = group.get_project(PT.from_str("core.z3"), build=True)
    #     core = FACT.load_any_experiment(core_p)
    #     ana = QueryAnalyzer("60nq")
    #     core = ExperAnalyzer(core, ana)
    #     o_group = FACT.get_group("bench_unstable_1")
    #     o_p = o_group.get_project(PT.from_str("base.z3"), build=True)

    #     for qid in core.qids:
    #         s = core.get_query_stability(qid)
    #         if s != STB.UNSTABLE:
    #             continue
    #         i_path = core_p.get_path(qid)
    #         o_path = o_p.get_path(qid)
    #         if os.path.exists(o_path):
    #             continue
    #         print(f"{QUERY_WIZARD} inst-z3 -i {i_path} -o {o_path} --timeout 5 --restarts 10")
    #         # print(i_path, s)

