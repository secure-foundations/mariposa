from ast import Dict
import os
from analysis.core_analyzer import CoreAnalyzer
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from base.query_analyzer import QueryAnalyzer, Stability as STB, FailureType as UR
from base.exper_analyzer import ExperAnalyzer
from utils.analysis_utils import *
from utils.query_utils import count_asserts, is_assertion_subset
from utils.system_utils import print_banner
from utils.shake_utils  import *
import numpy as np
from tqdm import tqdm
import filecmp

def check_incomplete(oracle_path, depths):
    print(oracle_path)
    for line in open(oracle_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        assert m
        cid = str(m.group(1))
        if np.isnan(depths[cid]):
            print(line, end="")
    print("..")

def valid_max(scores):
    return max([s for s in scores if not np.isnan(s)])

class ShakeAnalyzer(CoreAnalyzer):
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        super().__init__(group, ana)
        self.p_shake = group.get_project(PT.from_str("shko.z3"), build=True)

        # shake = FACT.load_any_experiment(self.p_shake)
        # self.shake = ExperAnalyzer(shake, ana)
        self.create_shake_queries()

    def check_shake_perf(self):
        for qid, qcs in self.qids.items():
            shake_log = self.p_base.get_path(qid, KnownExt.SHK_LOG)
            # rc, tt = self.shake[qid].get_original_status()
            # shake_path = self.p_shake.get_path(qid)

            print("base:", qcs.base)
            print("patch:", qcs.patch)

            if qid not in self.shake:
                print("shko: TOS!!")
            else:
                print("shko:", self.shake.get_stability(qid))
                self.shake[qid].print_status(5)

            print("./src/query_wizard.py debug-shake", "-i %s --core-query-path %s --input-log-path %s" % (qcs.base_path, qcs.patch_path, shake_log))

            print("")

    def create_shake_queries(self):
        cats = Categorizer()

        for qid, qcs in self.qids.items():
            shake_log = self.p_base.get_path(qid, KnownExt.SHK_LOG)
            shake_path = self.p_shake.get_path(qid)

            scores = parse_shake_log(shake_log)

            max_base_score = valid_max(scores.values())
            oracle = valid_max([int(max_base_score / 3.1), 1])
            if qcs.core_is_enabled():
                core_cids = load_query_cids(qcs.patch_path)
                core_scores = [scores[cid] for cid in core_cids.keys()]
                if np.nan in core_scores:
                    cats.add_item("shake (maybe) incomplete", qid)
                oracle = valid_max(core_scores)
            else:
                cats.add_item("no core", qid)
            create_shake_query(qcs.base_path, shake_path, scores, oracle)

        cats.finalize()
        cats.print_status()
