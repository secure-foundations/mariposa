import json
import os, sys
from tabulate import tabulate
from tqdm import tqdm
import pandas as pd
from z3 import set_param

from base.exper_analyzer import ExperAnalyzer
from debugger.edit_info import EditAction
from debugger.informed_editor import InformedEditor
from debugger.mutant_info import MutantInfo
from debugger3 import Debugger3
from utils.system_utils import log_info
from benchmark_consts import *
from debugger.file_builder import FileBuilder
from utils.analysis_utils import fmt_percent
from analysis.singleton_analyzer import SingletonAnalyzer

from debugger.proof_analyzer import ProofAnalyzer

from base.factory import FACT
SOLVER = FACT.get_solver("z3_4_13_0")
VERI_CFG = FACT.get_config("verify")
FILTER_CFG = FACT.get_config("verus_quick")
QA = FACT.get_analyzer("10sec")


def check_tested(dbg: Debugger3, ba: SingletonAnalyzer):
    tested = []
    root_quants = dbg.editor.get_singleton_actions(skip_infeasible=False)
    tested_qnames = set()

    for eid in ba.qids:
        ei = dbg.look_up_edit_with_id(eid)
        qname, action = ei.get_singleton_edit()
        rc, et = ba.get_query_result(eid)
        tested.append((qname, action.value, str(rc), et, ei.query_path))
        tested_qnames.add(qname)

    tested = sorted(tested, key=lambda x: x[0])
    print(tabulate(tested, headers=["Name", "Action", "Result", "Time", "Path"]))
    print()

    print("Not tested:")
    for qname in root_quants:
        if qname not in tested_qnames:
            print(qname)
    print()

def check_stabilized(dbg: Debugger3, fa: ExperAnalyzer):
    for eid in fa.get_stable_edit_ids():
        ei = dbg.look_up_edit_with_id(eid)
        qname, action = ei.get_singleton_edit()
        if qname == "prelude_fuel_defaults":
            continue 
        print(ei.query_path, qname, action.value)
    print()

query = sys.argv[1]
dbg = Debugger3(query)
assert dbg.editor is not None

p_singleton = FACT.get_project_by_path(dbg.singleton_dir)
e_singleton = FACT.try_get_exper(p_singleton, VERI_CFG, SOLVER)
ba = SingletonAnalyzer(e_singleton, QA)

p_filter = FACT.get_project_by_path(dbg.singleton_filtered_dir)
e_filter = FACT.try_get_exper(p_filter, FILTER_CFG, SOLVER)
fa = ExperAnalyzer(e_filter, QA)

df = pd.DataFrame(dbg.editor.get_report())
df.to_csv("report.csv")
# check_tested(dbg, ba)
# check_stabilized(dbg, fa)
