from ast import Dict
import os
from analysis.core_analyzer import CoreAnalyzer
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from query.analyzer import QueryAnalyzer, Stability as STB, UnstableReason as UR
from analysis.expr_analyzer import ExprAnalyzer
from utils.analysis_utils import *
from utils.query_utils import count_asserts, is_assertion_subset
from utils.system_utils import print_banner
from utils.shake_utils  import *
import numpy as np

def check_incomplete(oracle_path, depths):
    print(oracle_path)
    for line in open(oracle_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        assert m
        cid = str(m.group(1))
        if depths[cid] == -1:
            print(line, end="")
    print("..")
    

class ShakeAnalyzer(CoreAnalyzer):
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        super().__init__(group, ana)
        self.shake_p = group.get_project(PT.from_str("shko.z3"), build=True)
        # in_complete = 0
        cats = Categorizer()
        ratios = []

        for qid, qcs in self.qids.items():
            shake_log = self.p_base.get_ext_path(
                qid, KnownExt.SHK_LOG)
            scores = parse_shake_log(shake_log)
            out_path = self.shake_p.get_ext_path(qid)

            if qcs.core_is_enabled():
                core_cids = load_query_cids(qcs.patch_path)
                core_scores = [scores[cid] for cid in core_cids]

                if min(core_scores) == -1:
                    cats.add_item("shake incomplete", qid)
                    # check_incomplete(qcs.patch_path, depths)
                else:
                    # ratios += [max(scores.values())/max(core_scores)]
                    cats.add_item("core enabled", qid)
                create_shake_query(qcs.base_path, out_path, scores, max(core_scores))
            else:
                create_shake_query(qcs.base_path, out_path, scores, int(max(scores.values()) / 3.1))
        # ratios = np.array(ratios)
        # print(np.mean(ratios))
        cats.finalize()
        cats.print_status()
