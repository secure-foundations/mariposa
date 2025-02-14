#!/usr/bin/env python3

import os
import shutil
from tabulate import tabulate
from tqdm import tqdm
from base.exper_analyzer import ExperAnalyzer
from debugger.debugger import Debugger3
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import choose_action
from utils.cache_utils import clear_cache, has_cache, load_cache, load_cache_or
from utils.system_utils import log_check, log_error, log_info, log_warn
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
    SINGLETON_FINISHED = "finished"


class DbgProjectType(Enum):
    SINGLETON = "singleton"
    SINGLETON_FILTERED = "singleton.filtered"
    DOUBLETON = "doubleton"
    DOUBLETON_FILTERED = "doubleton.filtered"


DPT = DbgProjectType

# def get_split_status(dbg: Debugger3):
#     qa, cfg = get_params(dbg)
#     try:
#         p = FACT.get_project_by_path(dbg.splitter_dir)
#     except:
#         return "splitter not created"

#     e = FACT.try_get_exper(p, cfg, SOLVER)

#     if e is None:
#         return "splitter not ran"

#     sa = ExperAnalyzer(e, qa)
#     return sa


class Evaluator(Debugger3):
    def __init__(self, query_path: str, verbose=False, clear_report_cache=False):
        super().__init__(query_path, verbose=verbose)
        self.singleton_name = "singleton_" + self.name_hash
        self.doubleton_name = "doubleton_" + self.name_hash

        self._report_cache = self.name_hash + ".report"
        self._report = None

        if clear_report_cache:
            clear_cache(self._report_cache)

        if has_cache(self._report_cache):
            self.status = DebuggerStatus.SINGLETON_FINISHED
            self._report = load_cache(self._report_cache)
            return

        status = self.get_debugger_status()
        if isinstance(status, DebuggerStatus):
            self.status = status
            return

        self.status = DebuggerStatus.SINGLETON_FINISHED

    def get_debugger_status(self):
        ba = self.try_get_singleton_analyzer()

        if isinstance(ba, DebuggerStatus):
            return ba
        
        self._ba = ba

        fa = self.try_get_filter_analyzer()

        if isinstance(fa, DebuggerStatus):
            return fa

        self._fa = fa

    def __get_exp_params(self):
        if "/bench_unstable" in self.given_query_path:
            qa = QA_60
            cfg = CFG_60
        else:
            qa = QA_10
            cfg = CFG_10
        return qa, cfg

    def try_get_singleton_analyzer(self):
        if self.get_status()["proofs"] == 0:
            return DebuggerStatus.NO_PROOF

        target_dir = self.get_proj_dir(DPT.SINGLETON)

        try:
            p_singleton = FACT.get_project_by_path(target_dir)
        except:
            return DebuggerStatus.SINGLETON_CREATION_UNATTEMPTED

        registered, existing = self.get_singleton_counts()

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
            log_warn(
                f"[eval] {self.name_hash} tested count {tested_count} < registered {registered}"
            )

        log_check(tested_count <= registered, "[eval] tested count > registered!")

        qa, _ = self.__get_exp_params()

        try:
            ba = SingletonAnalyzer(e_singleton, qa)
        except:
            return DebuggerStatus.SINGLETON_NOT_RAN

        return ba

    def try_get_filter_analyzer(self):
        qa, filter_cfg = self.__get_exp_params()

        try:
            p_filter = FACT.get_project_by_path(
                self.get_proj_dir(DPT.SINGLETON_FILTERED)
            )
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

    # def get_command_to_run(self):
    #     if self.status == DebuggerStatus.SINGLETON_CREATION_UNATTEMPTED:
    #         return "./src/debugger3.py --create-singleton -i " + self.given_query_path
    #     if self.status == DebuggerStatus.SINGLETON_NOT_RAN:
    #         return (
    #             "./src/exper_wizard.py manager -e verify --total-parts 12 -i "
    #             + self.singleton_dir
    #         )
    #     if self.status == DebuggerStatus.SINGLETON_NOT_FILTERED:
    #         return (
    #             "./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i "
    #             + self.singleton_dir
    #         )
    #     if self.status == DebuggerStatus.FILTERED_NOT_RAN:
    #         return "python3 src/carve_and_rerun.py " + self.filtered_dir

    #     assert False

    def __build_tested(self):
        tested = []
        root_quants = self.editor.list_root_qnames(skip_ignored=False)
        tested_qnames = set()

        for eid in self._ba.qids:
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            rc, et = self._ba.get_query_result(eid)
            tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
            tested_qnames.add(qname)

        skipped = set(root_quants) - tested_qnames

        tested = DataFrame(
            tested, columns=["qname", "action", "result", "time", "edit_path"]
        )
        return tested, skipped

    def __build_stabilized(self):
        stabilized = []
        for eid in self._fa.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            if qname == "prelude_fuel_defaults":
                continue
            stabilized.append((qname, action.value, ei.query_path))
        stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
        return stabilized

    @property
    def report(self):
        if self._report is None:
            self.build_report()
        return self._report

    def build_report(self, clear=False) -> Report:
        if self.status != DebuggerStatus.SINGLETON_FINISHED:
            return None

        if self._report is not None and not clear:
            return self._report

        def _build_report():
            r = Report()
            r.tested, r.skipped = self.__build_tested()
            assert len(r.tested) > 0
            r.stabilized = self.__build_stabilized()
            r.freq = self.editor.get_inst_report()
            assert len(r.freq) > 0
            return r

        self._report = load_cache_or(self._report_cache, _build_report, clear)
        return self._report

    def collect_garbage(self):
        if self.status != DebuggerStatus.SINGLETON_FINISHED:
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
                # if not os.path.exists(edit_path):
                #     base = os.path.basename(edit_path)
                #     base = base.replace(".smt2", "")
                #     ei = self.look_up_edit_with_id(base)
                #     self.editor.edit_by_info(ei)
                #     assert os.path.exists(edit_path)
                continue
            if row.result == "error":
                continue
            if os.path.exists(edit_path):
                log_info(f"removing {edit_path}")
                os.remove(edit_path)

    def get_dirs_to_sync(self):
        pass

    def get_proj_name(self, pt: DbgProjectType):
        if pt == DbgProjectType.SINGLETON:
            return self.singleton_name
        if pt == DbgProjectType.DOUBLETON:
            return self.doubleton_name
        if pt == DbgProjectType.SINGLETON_FILTERED:
            return self.singleton_name + ".filtered"
        if pt == DbgProjectType.DOUBLETON_FILTERED:
            return self.doubleton_name + ".filtered"
        assert False

    def register_singleton(self):
        singleton_edits = self.editor.get_singleton_actions()
        dest_dir = self.get_proj_dir(DbgProjectType.SINGLETON)

        for edit in singleton_edits:
            self.register_edit(edit, dest_dir)

        self.save_edits_meta()
        return singleton_edits

    def create_singleton(self):
        singleton_edits = self.register_singleton()

        dest_dir = self.get_proj_dir(DbgProjectType.SINGLETON)
        proj_name = self.get_proj_name(DbgProjectType.SINGLETON)

        file_size = os.path.getsize(self.orig_path) / 1024
        total_size = file_size * len(singleton_edits) / 1024 / 1024

        if total_size > 20:
            log_error(f"[edit] {dest_dir} aborted, {total_size:.2f}G may be used!")
            return

        log_info(f"[edit] estimated size: {total_size:.2f}G")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        for action in tqdm(singleton_edits):
            ei = EditInfo(dest_dir, action)
            assert self.contains_edit_info(ei)
            if ei.query_exists():
                log_info(f"[edit] {ei.get_id()} already exists")
                continue
            self.create_edit_query(ei)

        log_info(
            f"[edit] [proj] {proj_name} has {len(list_smt2_files(dest_dir))} queries"
        )
        return dest_dir

    def get_singleton_counts(self):
        existing = list_smt2_files(self.get_proj_dir(DPT.SINGLETON))

        if existing is None:
            existing = []

        singleton_count = 0

        for ei in self.edit_infos.values():
            if ei.is_singleton():
                singleton_count += 1

        return singleton_count, len(existing)

    def get_proj_dir(self, pt: DbgProjectType):
        name = self.get_proj_name(pt)
        return f"data/projs/{name}/base.z3"

    def get_db_dir(self, pt: DbgProjectType):
        name = self.get_proj_name(pt)
        return f"data/dbs/{name}/base.z3"

    def create_doubleton(self):
        dest_dir = self.get_proj_dir(DPT.DOUBLETON)
        log_info(f"[edit] creating doubleton project {dest_dir}")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        ratios = self.get_trace_graph_ratios()
        mi = self.get_trace_info()
        trace_graph = mi.get_trace_graph()

        roots = dict()
        singleton_scores = dict()
        TOP_N = 50

        for root in list(self.editor.list_qnames(root_only=True)):
            if root not in ratios:
                continue

            actions = self.editor.get_quant_actions(root)

            if (
                actions == {EditAction.SKOLEMIZE}
                or actions == {EditAction.NONE}
                or actions == {EditAction.ERROR}
            ):
                continue

            roots[root] = set(self.editor.trace_stats.get_group_stat(root).keys())
            singleton_scores[root] = trace_graph.aggregate_scores(ratios[root])

        singleton_ranked = [
            (k, v)
            for k, v in sorted(singleton_scores.items(), key=lambda item: item[1], reverse=True)
        ]
        ranked = [x[0] for x in singleton_ranked]

        scores = dict()

        for i, root1 in enumerate(tqdm(ranked[:TOP_N])):
            ratio1 = ratios[root1]
            group1 = roots[root1]
            cur_best, selected = 0, None

            for root2 in ranked[TOP_N+1:2*TOP_N+1]:
                ratio2 = ratios[root2]  
                group2 = roots[root2]
                merged = {}
                for k in ratio1.keys():
                    merged[k] = max(ratio1[k], ratio2.get(k, 0))
                for k in ratio2.keys():
                    merged[k] = max(ratio2[k], ratio1.get(k, 0))
                for k in list(merged.keys()):
                    if merged[k] == 0:
                        merged.pop(k)
                starts = group1 | group2
                res = trace_graph.compute_sub_ratios(starts=starts, bootstrap=merged)
                score = trace_graph.aggregate_scores(res)
                if score > cur_best:
                    cur_best = score
                    selected = root2

            scores[(root1, selected)] = cur_best

        scores = [(k, v) for k, v in scores.items() if v > 0]
        sorted_scores = sorted(scores, key=lambda x: x[1], reverse=True)
        sorted_scores = sorted_scores[:TOP_N]

        for (qname1, qname2), score in sorted_scores:
            action1 = choose_action(self.editor.get_quant_actions(qname1))
            action2 = choose_action(self.editor.get_quant_actions(qname2))
            edit = {qname1: action1, qname2: action2}
            ei = self.register_edit(edit, dest_dir)
            self.create_edit_query(ei)

        self.save_edits_meta()

class BenchViewer:
    def __init__(self, queries):
        status = Categorizer()

        self.__name_hashes = dict()
        self.__reviewers: Dict[str, Evaluator] = dict()
        pool = multiprocessing.Pool(8)

        reviewers = pool.map(Evaluator, queries)

        for r in reviewers:
            self.__reviewers[r.given_query_path] = r
            self.__name_hashes[r.name_hash] = r.given_query_path
            status.add_item(r.status, r.given_query_path)

        status.finalize()
        self.status = status

        self.fixable = set()
        self.unfixable = set()

        for q in self.status[DebuggerStatus.SINGLETON_FINISHED]:
            r = self.__reviewers[q]
            num_fixes = len(r.report.stabilized)
            if num_fixes > 0:
                self.fixable.add(q)
            else:
                self.unfixable.add(q)

    def __getitem__(self, key) -> Evaluator:
        if key in self.__name_hashes:
            key = self.__name_hashes[key]
        return self.__reviewers[key]

    def __iter__(self):
        return iter(self.__reviewers)

    def items(self):
        return self.__reviewers.items()

    def keys(self):
        return self.__reviewers.keys()


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
    parser.add_argument(
        "--print-report",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--clear-report-cache",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--create-doubleton",
        default=False,
        action="store_true",
        help="create the doubleton project",
    )
    parser.add_argument(
        "--create-singleton",
        default=False,
        action="store_true",
        help="create the doubleton project",
    )


    args = parser.parse_args()
    eva = Evaluator(args.input_query_path, clear_report_cache=args.clear_report_cache)
    print(eva.status)

    if args.collect_garbage:
        eva.collect_garbage()

    if args.print_report:
        r = eva.build_report()

        if r is None:
            print("No report available.")
            return

        # r.print_tested()
        r.print_stabilized()

    if args.create_doubleton:
        assert not args.create_singleton 
        eva.create_doubleton()
        
    if args.create_singleton:
        eva.create_singleton()


if __name__ == "__main__":
    main()
