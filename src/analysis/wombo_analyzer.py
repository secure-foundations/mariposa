from ast import Dict
import os
import shutil
from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from query.analyzer import QueryAnalyzer, Stability as STB, UnstableReason as UR
from analysis.expr_analyzer import ExperAnalyzer
from utils.analysis_utils import *
from utils.query_utils import count_asserts, is_assertion_subset
from utils.system_utils import print_banner

class WomboAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        solver = FACT.get_solver_by_name("z3_4_12_5")
        self.pins_p = group.get_project(PT.from_str("pins.z3"))
        self.woco_p = group.get_project(PT.from_str("woco.z3"))
        self.temp_p = group.get_project(PT.from_str("temp.z3"), build=True)

        pins = FACT.load_any_experiment(self.pins_p)
        log_check(pins.solver == solver, "base project is not using z3_4_12_5")
        # woco = FACT.load_any_experiment(self.woco_p)
        # log_check(woco.solver == solver, "core project is not using z3_4_12_5")

        self.pins = ExperAnalyzer(pins, ana)
        # self.woco = ExperAnalyzer(woco, ana)

        print(NINJA_BUILD_RULES)

        # for qid in self.core_adj[STB.UNSTABLE]:
        #     cqs = self.qids[qid]
        #     pins_path = self.pins_p.get_ext_path(qid)

        #     if cqs.core_is_enabled():
        #         print(f"build {pins_path}: pre-inst-z3 {cqs.patch_path}\n")

        for qid in self.pins.qids:
            woco_path = self.woco_p.get_ext_path(qid)
            temp_path = self.temp_p.get_ext_path(qid)
            print(f"build {temp_path}: wombo-combo {woco_path}\n")
            # ps = self.pins.get_query_stability(qid)
            # ws = self.woco.get_query_stability(qid)
            # if ws == STB.UNSOLVABLE or ws == STB.MISSING_F:
            #     shutil.copy(pins_path, woco_path)
