from tabulate import tabulate
from base.exper_analyzer import ExperAnalyzer
from debugger.edit_info import EditAction
from debugger.informed_editor import InformedEditor
from debugger.mutant_info import MutantInfo
from debugger3 import Debugger3
from utils.system_utils import log_info
from benchmark_consts import *
from debugger.file_builder import FileBuilder
from utils.analysis_utils import Categorizer, fmt_percent
from analysis.singleton_analyzer import SingletonAnalyzer
from base.factory import FACT
from utils.system_utils import list_smt2_files, log_info

SOLVER = FACT.get_solver("z3_4_13_0")
VERI_CFG = FACT.get_config("verify")

CFG_10 = FACT.get_config("verus_quick")
CFG_60 = FACT.get_config("default")

QA_10 = FACT.get_analyzer("10sec")
QA_60 = FACT.get_analyzer("60sec")

def shorten_qname(qname: str):
    if len(qname) > 80:
        return qname[:80] + "..."
    return qname

def get_params(dbg: Debugger3):
    if "/bench_unstable/" in dbg.given_query_path:
        qa = QA_60
        cfg = CFG_60
    else:
        qa = QA_10
        cfg = CFG_10
    return qa, cfg

def get_singleton_status(dbg: Debugger3):
    if dbg.get_status()["proofs"] == 0:
        return "no proof built"

    try:
        p_singleton = FACT.get_project_by_path(dbg.singleton_dir)
    except:
        return "singleton not created"

    if len(p_singleton.qids) == 0:
        return "singleton not created"

    e_singleton = FACT.try_get_exper(p_singleton, VERI_CFG, SOLVER)

    if e_singleton is None:
        return "singleton not ran"

    qa, _ = get_params(dbg)

    try:
        ba = SingletonAnalyzer(e_singleton, qa)
    except:
        return "singleton not ran (probably)"

    return ba

def get_filtered_status(dbg: Debugger3):
    qa, filter_cfg = get_params(dbg)

    try:
        p_filter = FACT.get_project_by_path(dbg.singleton_filtered_dir)
    except:
        return "singleton not filtered"

    e_filter = FACT.try_get_exper(p_filter, filter_cfg, SOLVER)

    if e_filter is None:
        return "filtered but not ran"

    try:
        fa = ExperAnalyzer(e_filter, qa)
    except:
        return "filtered but not ran (probably)"

    return fa

def get_split_status(dbg: Debugger3):
    qa, cfg = get_params(dbg)
    try:
        p = FACT.get_project_by_path(dbg.splitter_dir)
    except:
        return "splitter not created"
    
    e = FACT.try_get_exper(p, cfg, SOLVER)

    if e is None:
        return "splitter not ran"
    
    sa = ExperAnalyzer(e, qa)
    return sa

def check_tested(dbg: Debugger3, ba: SingletonAnalyzer):
    tested = dict()
    root_quants = dbg.editor.get_singleton_actions(skip_infeasible=False)
    tested_qnames = set()

    for eid in ba.qids:
        ei = dbg.look_up_edit_with_id(eid)
        qname, action = ei.get_singleton_edit()
        rc, et = ba.get_query_result(eid)
        tested[(qname, action.value)] = [str(rc), et, ei.query_path]
        tested_qnames.add(qname)

    untested = set(root_quants) - set(tested_qnames)
    return tested, untested

def check_stabilized(dbg: Debugger3, fa: ExperAnalyzer):
    stabilized = []
    for eid in fa.get_stable_edit_ids():
        ei = dbg.look_up_edit_with_id(eid)
        qname, action = ei.get_singleton_edit()
        if qname == "prelude_fuel_defaults":
            continue 
        stabilized.append((qname, action.value, ei.query_path))

    return stabilized

def get_debugger_statuses(queries):
    statuses = Categorizer()

    for query in queries:
        dbg = Debugger3(query)

        ba = get_singleton_status(dbg)

        if isinstance(ba, str):
            statuses.add_item(ba, query)
            continue

        fa = get_filtered_status(dbg)

        if isinstance(fa, str):
            statuses.add_item(fa, query)
            continue

        statuses.add_item("finished", query)

    statuses.finalize()
    return statuses