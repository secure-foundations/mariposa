import os
from tabulate import tabulate
from base.exper_analyzer import ExperAnalyzer
from debugger.edit_info import EditAction
from debugger.informed_editor import InformedEditor
from debugger.mutant_info import MutantInfo
from debugger3 import Debugger3
from utils.cache_utils import load_cache_or
from utils.system_utils import log_info
from benchmark_consts import *
from debugger.file_builder import FileBuilder
from utils.analysis_utils import Categorizer, fmt_percent
from analysis.singleton_analyzer import SingletonAnalyzer
from base.factory import FACT
from utils.system_utils import list_smt2_files, log_info
from enum import Enum
import pandas as pd
from pandas import DataFrame

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
    if "/bench_unstable" in dbg.given_query_path:
        qa = QA_60
        cfg = CFG_60
    else:
        qa = QA_10
        cfg = CFG_10
    return qa, cfg


class DebuggerStatus(Enum):
    NO_PROOF = "no proof built"
    SINGLETON_NOT_CREATED = "singleton not created"
    SINGLETON_NOT_RAN = "singleton not ran"
    SINGLETON_NOT_FILTERED = "singleton not filtered"
    FILTERED_NOT_RAN = "filtered but not ran"
    SPLITTER_NOT_CREATED = "splitter not created"
    SPLITTER_NOT_RAN = "splitter not ran"
    FINISHED = "finished"


def try_get_singleton_analyzer(dbg: Debugger3):
    if dbg.get_status()["proofs"] == 0:
        return DebuggerStatus.NO_PROOF

    try:
        p_singleton = FACT.get_project_by_path(dbg.singleton_dir)
    except:
        return DebuggerStatus.SINGLETON_NOT_CREATED

    if len(p_singleton.qids) == 0:
        return DebuggerStatus.SINGLETON_NOT_CREATED

    e_singleton = FACT.try_get_exper(p_singleton, VERI_CFG, SOLVER)

    if e_singleton is None:
        return DebuggerStatus.SINGLETON_NOT_RAN

    qa, _ = get_params(dbg)

    try:
        ba = SingletonAnalyzer(e_singleton, qa)
    except:
        return DebuggerStatus.SINGLETON_NOT_RAN

    return ba


def try_get_filter_analyzer(dbg: Debugger3):
    qa, filter_cfg = get_params(dbg)

    try:
        p_filter = FACT.get_project_by_path(dbg.singleton_filtered_dir)
    except:
        return DebuggerStatus.SINGLETON_NOT_FILTERED

    e_filter = FACT.try_get_exper(p_filter, filter_cfg, SOLVER)

    if e_filter is None:
        if len(p_filter.qids) == 0:
            return DebuggerStatus.SINGLETON_NOT_FILTERED
        return DebuggerStatus.FILTERED_NOT_RAN

    try:
        fa = ExperAnalyzer(e_filter, qa)
    except:
        return DebuggerStatus.FILTERED_NOT_RAN

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


def get_debugger_status(dbg: Debugger3):
    ba = try_get_singleton_analyzer(dbg)

    if isinstance(ba, DebuggerStatus):
        return ba

    fa = try_get_filter_analyzer(dbg)

    if isinstance(fa, DebuggerStatus):
        return fa

    return (ba, fa)


class Report:
    def __init__(self):
        self.tested = None
        self.stabilized = None
        self.freq = None
        self.skipped = None


class Reviewer2(Debugger3):
    def __init__(self, query_path: str):
        super().__init__(query_path)
        status = get_debugger_status(self)

        if isinstance(status, DebuggerStatus):
            self.status = status
            return

        self.status = DebuggerStatus.FINISHED
        self._ba, self._fa = status
        self._report_cache = self.name_hash + ".report"
        self.report = None 

    def get_command_to_run(self):
        if self.status == DebuggerStatus.SINGLETON_NOT_CREATED:
            return "./src/debugger3 --create-singleton -i " + self.given_query_path
        if self.status == DebuggerStatus.SINGLETON_NOT_RAN:
            return (
                "./src/exper_wizard.py manager -e verify --total-parts 12 -i "
                + self.singleton_dir
            )
        if self.status == DebuggerStatus.SINGLETON_NOT_FILTERED:
            return (
                "./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i "
                + self.singleton_dir
            )
        if self.status == DebuggerStatus.FILTERED_NOT_RAN:
            return "python3 src/carve_and_rerun.py " + self.singleton_filtered_dir

        assert False

    def get_tested(self):
        tested = []
        root_quants = self.editor.get_singleton_actions(skip_infeasible=False)
        tested_qnames = set()

        for eid in self._ba.qids:
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            rc, et = self._ba.get_query_result(eid)
            tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
            tested_qnames.add(qname)

        skipped = set(root_quants) - set(tested_qnames)
        tested = DataFrame(
            tested, columns=["qname", "action", "result", "time", "edit_path"]
        )
        return tested, skipped

    def get_stabilized(self):
        stabilized = []
        for eid in self._fa.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            if qname == "prelude_fuel_defaults":
                continue
            stabilized.append((qname, action.value, ei.query_path))
        stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
        return stabilized

    def build_report(self, clear=False) -> Report:
        if self.status != DebuggerStatus.FINISHED:
            return None

        def _build_report():
            r = Report()
            r.tested, r.skipped = self.get_tested()
            r.stabilized = self.get_stabilized()
            r.freq = self.editor.get_inst_report()
            return r

        r = load_cache_or(self._report_cache, _build_report, clear)
        self._report = r
        return r
