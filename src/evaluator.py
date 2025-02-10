#!/usr/bin/env python3

import os
import shutil
from tabulate import tabulate
from base.exper_analyzer import ExperAnalyzer
from debugger.debugger import Debugger3
from debugger.demo_utils import Report
from utils.cache_utils import load_cache_or
from utils.system_utils import log_check, log_info, log_warn
from typing import Dict
from benchmark_consts import *
from utils.analysis_utils import fmt_percent
from analysis.singleton_analyzer import SingletonAnalyzer
from base.factory import FACT
from utils.system_utils import list_smt2_files, log_info
from enum import Enum
from pandas import DataFrame
from utils.analysis_utils import Categorizer
import multiprocessing
import argparse

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
    SINGLETON_CREATION_UNATTEMPTED = "singleton creation unattempted"
    SINGLETON_CREATION_FAILED = "singleton creation failed"

    SINGLETON_NOT_RAN = "singleton not ran"
    SINGLETON_TESTED_EMPTY = "singleton tested empty"
    
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
        return DebuggerStatus.SINGLETON_CREATION_UNATTEMPTED

    registered, existing = dbg.get_singleton_status()

    if registered == 0:
        return DebuggerStatus.SINGLETON_CREATION_UNATTEMPTED

    e_singleton = FACT.try_get_exper(p_singleton, VERI_CFG, SOLVER)

    if e_singleton is None:
        if existing == 0:
            return DebuggerStatus.SINGLETON_CREATION_FAILED
        return DebuggerStatus.SINGLETON_NOT_RAN

    tested_count = e_singleton.get_sum_count()

    if tested_count == 0:
        return DebuggerStatus.SINGLETON_TESTED_EMPTY

    if tested_count < registered:
        log_warn(f"[eval] {dbg.name_hash} tested count {tested_count} < registered {registered}")

    log_check(tested_count <= registered, "[eval] tested count > registered!")

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


class Evaluator(Debugger3):
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
        if self.status == DebuggerStatus.SINGLETON_CREATION_UNATTEMPTED:
            return "./src/debugger3.py --create-singleton -i " + self.given_query_path
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
            assert len(r.tested) > 0
            r.stabilized = self.get_stabilized()
            r.freq = self.editor.get_inst_report()
            assert len(r.freq) > 0
            return r

        r = load_cache_or(self._report_cache, _build_report, clear)
        self._report = r
        return r

    def collect_garbage(self):
        if self.status != DebuggerStatus.FINISHED:
            log_warn(
                f"[eval] skipped GC on unfinished project {self.status} {self.given_query_path}"
            )
            return

        super().collect_garbage()

        report = self.build_report()

        seps = report.stabilized.edit_path.values

        for row in report.tested.itertuples():
            edit_path = row.edit_path
            if edit_path in seps:
                continue
            if row.result == "error":
                continue
            if os.path.exists(edit_path):
                log_info(f"removing {edit_path}")
                os.remove(edit_path)

    def get_dirs_to_sync(self):
        items = []
        items.append(self.sub_root)
        items.append(self.singleton_dir)
        items.append(self.singleton_filtered_dir)
        items.append("data/dbs/" + self.singleton_dir)
        items.append("data/dbs/" + self.singleton_filtered_dir)
        return items

class BenchViewer:
    def __init__(self, queries):
        sts = Categorizer()
        self.reviewers: Dict[str, Evaluator] = dict()
        pool = multiprocessing.Pool(4)

        reviewers = pool.map(Evaluator, queries)

        for r in reviewers:
            self.reviewers[r.given_query_path] = r
            sts.add_item(r.status, r.given_query_path)

        sts.finalize()
        self.status = sts

        self.fixable = set()
        self.unfixable = set()

        self.__analyze_finished()

    def __analyze_finished(self):
        for q in self.status[DebuggerStatus.FINISHED]:
            r = self.reviewers[q]
            num_fixes = len(r.get_stabilized())
            if num_fixes > 0:
                self.fixable.add(q)
            else:
                self.unfixable.add(q)

    def __getitem__(self, key):
        return self.reviewers[key]

    def get_min_ranks(self):
        min_ranks = []
        for q in self.fixable:
            r = self.reviewers[q]
            report = r.get_report()
            indices = report.freq.loc[
                report.freq["qname"].isin(report.stabilized["qname"])
            ].index
            report.freq["rank"] = report.freq["trace_count"].rank(
                method="min", ascending=False
            )
            min_rank = report.freq.loc[indices]["rank"].min()
            min_ranks.append(min_rank)
        min_ranks = np.array(min_ranks)
        return min_ranks


# analyzable = len(fixable) + len(no_fixes)
# total = len(sts.tally)

# def fmt(x, y):
#     return f"({round(x / y * 100, 1)}%)"

# print("Analyzable", analyzable)
# print("\t-", "Fixable", len(fixable), fmt(len(fixable), total))
# print("\t\t-", "top-1", fmt(len(min_ranks[min_ranks == 1]), total))
# print("\t\t-", "top-3", fmt(len(min_ranks[min_ranks <= 3]), total))
# print("\t\t-", "top-10", fmt(len(min_ranks[min_ranks <= 10]), total))
# print("\t-", "No Fixes", len(no_fixes), fmt(len(no_fixes), total))
# print("No Analyzable", total - analyzable, fmt(total - analyzable, total))
# print("\t-", "No Proofs", len(sts[DebuggerStatus.NO_PROOF]), fmt(len(sts[DebuggerStatus.NO_PROOF]), total))

def main():
    parser = argparse.ArgumentParser(description="Mariposa Evaluator. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "--collect-garbage",
        default=False,
        action="store_true",
    )
    args = parser.parse_args()
    eva = Evaluator(args.input_query_path)
    print(eva.status)

    if args.collect_garbage:
        eva.collect_garbage()
        return

if __name__ == "__main__":
    main()

