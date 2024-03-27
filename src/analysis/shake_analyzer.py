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

SHAKE_MAX = 18446744073709551615

def load_base_shake_depth(log_path):
    depth = dict()
    with open(log_path, "r") as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip().split(":")
            depth[line[1]] = int(line[0])

            if depth[line[1]] == SHAKE_MAX:
                depth[line[1]] = -1
    return depth            

import re

CID_PATTERN = re.compile(":named (mariposa_cid_(\d)+)")

def read_query_depth(query_path, depth):
    q_depths = []
    for line in open(query_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        assert m
        cid = str(m.group(1))
        q_depths.append(depth[cid])
    return q_depths

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
    
def create_shake_query(base_path, out_path, depths, max_depth):
    # print(base_path, out_path, max_depth)
    new_lines = []
    for line in open(base_path, "r"):
        if not line.startswith("(assert"):
            new_lines.append(line)
            continue
        m = re.search(CID_PATTERN, line)
        assert m
        cid = str(m.group(1))
        if depths[cid] < max_depth:
            new_lines.append(line)

    with open(out_path, "w") as f:
        f.writelines(new_lines)

class ShakeAnalyzer(CoreAnalyzer):
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        super().__init__(group, ana)
        # in_complete = 0
        cats = Categorizer()
        for qid, qcs in self.qids.items():
            shake_log = self.p_base.get_ext_path(
                qid, KnownExt.SHK_LOG)
            depths = load_base_shake_depth(shake_log)
            out_path = "gen/shake/" + qid + ".smt2"
            if qcs.core_is_enabled():
                core_depths = read_query_depth(qcs.patch_path, depths)
                if min(core_depths) == -1:
                    # print(qcs.patch)
                    # cats.add_item("shake incomplete", qid)
                    # check_incomplete(qcs.patch_path, depths)
                    pass
                else:
                    cats.add_item("core enabled", qid)
                    create_shake_query(qcs.patch_path, out_path, depths, max(core_depths))
                    # print(max(depths.values()), max(core_depths))
            else:
                cats.add_item("missing core", qid)                
        
        cats.finalize()
        cats.print_status()
