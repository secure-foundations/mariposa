#!/usr/bin/env python3

import os
import shutil
from tabulate import tabulate
from tqdm import tqdm
from debugger.debugger import Debugger3, resolve_input_path
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import choose_action
from utils.cache_utils import (
    clear_cache,
    has_cache,
    load_cache,
    load_cache_or,
    save_cache,
)
from typing import Dict
from benchmark_consts import *
from utils.analysis_utils import fmt_percent
from base.factory import FACT
from utils.system_utils import get_name_hash, list_smt2_files, log_error, log_info, log_warn
from enum import Enum
from pandas import DataFrame
from utils.analysis_utils import Categorizer
import multiprocessing
import argparse
from eval_carver import Carver, CarverStatus


def shorten_qname(qname: str):
    if len(qname) > 80:
        return qname[:80] + "..."
    return qname


class DbgMode(Enum):
    SINGLETON = "singleton"
    DOUBLETON = "doubleton"

    # @property
    # def cache_name(self):
    #     if self.pt == DPT.SINGLETON:
    #         return self.name_hash + ".report"
    #     elif self.pt == DPT.DOUBLETON:
    #         return self.name_hash + ".2.report"
    #     assert False


# def try_analyze_tested(self, pt: DPT):
#     if pt in self.__exps:
#         return self.__exps[pt]

#     target_dir = self.get_proj_dir(pt)
#     registered, existing = self.get_edit_counts(pt)

#     if registered == 0:
#         assert existing == 0
#         return DbgStatus.CREATION_UNATTEMPTED

#     if existing == 0:
#         return DbgStatus.CREATION_FAILED

#     proj = FACT.get_project_by_path(target_dir)
#     exp = FACT.try_get_exper(proj, VERI_CFG, SOLVER)

#     if exp is None:
#         return DbgStatus.UNTESTED

#     tested_count = exp.get_sum_count()

#     if tested_count == 0:
#         return DbgStatus.TESTED_EMPTY

#     if tested_count < registered:
#         log_warn(
#             f"[eval] {self.name_hash} tested count {tested_count} < registered {registered}"
#         )

#     log_check(
#         tested_count <= registered,
#         f"[eval] {target_dir} tested count {tested_count} > registered!",
#     )

#     qa, _ = self.__get_exp_params()

#     try:
#         tested = SingletonAnalyzer(exp, qa)
#     except:
#         return DbgStatus.UNTESTED

#     self.__exps[pt] = tested
#     return tested


class Evaluator(Debugger3):
    def __init__(
        self,
        query_path: str,
        verbose=False,
    ):
        super().__init__(query_path, verbose=verbose)

        if not hasattr(self, "proj_name"):
            self.proj_name = "singleton_" + self.name_hash
            self._report_cache = self.name_hash + ".report"

        self._carver = None

        if self.get_status()["proofs"] == 0:
            self.status = CarverStatus.NO_PROOF
            return

        self._report = None

        if has_cache(self._report_cache):
            self.status = CarverStatus.FINISHED
            self._report = load_cache(self._report_cache)
            return

        self._carver = Carver(self.proj_name)
        self.status = self._carver.status

    def _build_tested(self):
        tested = []
        root_quants = self.editor.list_root_qnames(skip_ignored=False)
        tested_qnames = set()

        for eid in self.carver.tested.qids:
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            rc, et = self.carver.tested.get_query_result(eid)
            tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
            tested_qnames.add(qname)

        skipped = set(root_quants) - tested_qnames

        tested = DataFrame(
            tested, columns=["qname", "action", "result", "time", "edit_path"]
        )
        return tested, skipped

    def _build_stabilized(self):
        stabilized = []
        for eid in self.carver.filtered.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            if qname == "prelude_fuel_defaults":
                continue
            stabilized.append((qname, action.value, ei.query_path))
        stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
        return stabilized

    @property
    def carver(self) -> Carver:
        if self._carver is None:
            self._carver = Carver(self.proj_name)
        return self._carver

    @property
    def report(self) -> Report:
        if self.status != CarverStatus.FINISHED:
            return None

        if self._report is None:
            r = Report()
            r.tested, r.skipped = self._build_tested()
            if len(r.tested) == 0:
                log_error(f"[eval] {self.proj_name} has no tested report")
                assert False
            r.stabilized = self._build_stabilized()
            r.freq = self.editor.get_inst_report()
            if len(r.freq) == 0:
                log_error(f"[eval] {self.proj_name} has no freq report")
                assert False
            self._report = r
            save_cache(self._report_cache, r)
        return self._report

    def register_singleton(self):
        singleton_edits = self.editor.get_singleton_actions()
        dest_dir = self.carver.test_dir()

        for edit in singleton_edits:
            self.register_edit(edit, dest_dir)

        self.save_edits_meta()
        return singleton_edits

    def create_project(self):
        singleton_edits = self.register_singleton()
        dest_dir = self.carver.test_dir()

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
            f"[edit] [proj] {self.proj_name} has {len(list_smt2_files(dest_dir))} queries"
        )
        return dest_dir

    def collect_garbage(self):
        super().collect_garbage()

        if self.status != CarverStatus.FINISHED:
            log_warn(
                f"[eval] skipped GC on unfinished project {self.status} {self.given_query_path}"
            )
            return

        seps = self.report.stabilized.edit_path.values

        for row in self.report.tested.itertuples():
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

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_singleton()

    def get_edit_counts(self):
        existing = list_smt2_files(self.carver.test_dir())

        if existing is None:
            existing = []

        registered_count = 0

        for ei in self.edit_infos.values():
            if not self.is_registered_edit(ei):
                continue
            registered_count += 1

        return registered_count, len(existing)

    def get_dirs_to_sync(self):
        return [
            self.sub_root,
        ] + self.carver.get_dirs()

    def reset_project(self):
        self.carver.clear_all()


class DoubletonEvaluator(Evaluator):
    def __init__(
        self,
        query_path: str,
        verbose=False,
    ):
        # this is just dumb
        query_path = resolve_input_path(query_path, verbose)
        self.name_hash = get_name_hash(query_path)

        self.proj_name = "doubleton_" + self.name_hash
        self._report_cache = self.name_hash + ".2.report"

        super().__init__(
            query_path,
            verbose=verbose,
        )

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_doubleton()

    def create_project(self):
        dest_dir = self.carver.test_dir
        log_info(f"[doubleton] creating doubleton project {dest_dir}")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        ratios = self.get_trace_graph_ratios()
        mi = self.get_trace_info()
        trace_graph = mi.get_trace_graph()

        roots = dict()
        singleton_scores = dict()
        TOP_N = 100

        for root in list(self.editor.list_qnames(root_only=True)):
            if root not in ratios:
                continue

            actions = self.editor.get_quant_actions(root)
            # print(actions)

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
            for k, v in sorted(
                singleton_scores.items(), key=lambda item: item[1], reverse=True
            )
        ]
        ranked = [x[0] for x in singleton_ranked]

        scores = dict()

        for i, root1 in enumerate(tqdm(ranked[:TOP_N])):
            ratio1 = ratios[root1]
            group1 = roots[root1]

            for root2 in ranked[i + 1 : i + 1 + TOP_N]:
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
                # if score > cur_best:
                #     cur_best = score
                #     selected = root2
                scores[(root1, root2)] = score

        scores = [(k, v) for k, v in scores.items() if v > 0]
        sorted_scores = sorted(scores, key=lambda x: x[1], reverse=True)
        sorted_scores = sorted_scores[:TOP_N]

        for (qname1, qname2), score in sorted_scores:
            action1 = choose_action(self.editor.get_quant_actions(qname1))
            action2 = choose_action(self.editor.get_quant_actions(qname2))
            edit = {qname1: action1, qname2: action2}
            # print(edit)
            ei = self.register_edit(edit, dest_dir)
            self.create_edit_query(ei)

        self.save_edits_meta()

    def _build_tested(self):
        tested = []

        for eid in self.carver.tested.qids:
            ei = self.look_up_edit_with_id(eid)
            (q1, a1), (q2, a2) = ei.get_doubleton_edit()
            rc, et =self.carver.tested.get_query_result(eid)
            tested.append(
                (q1, a1.value, q2, a2.value, str(rc), et / 1000, ei.query_path)
            )

        skipped = set()

        tested = DataFrame(
            tested,
            columns=[
                "qname1",
                "action1",
                "qname2",
                "action2",
                "result",
                "time",
                "edit_path",
            ],
        )
        return tested, skipped

    def _build_stabilized(self):
        stabilized = []
        for eid in self.carver.filtered.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            (q1, a1), (q2, a2) = ei.get_doubleton_edit()
            stabilized.append((q1, a1.value, q2, a2.value, ei.query_path))
        stabilized = DataFrame(
            stabilized, columns=["qname1", "action1", "qname2", "action2", "edit_path"]
        )
        return stabilized


class BenchViewer:
    def __init__(self, queries, mode: DbgMode):
        self.status = Categorizer()

        self.__name_hashes = dict()
        self.__reviewers: Dict[str, Evaluator] = dict()
        pool = multiprocessing.Pool(8)

        if mode == DbgMode.SINGLETON:
            reviewers = pool.map(Evaluator, queries)
        elif mode == DbgMode.DOUBLETON:
            reviewers = pool.map(DoubletonEvaluator, queries)
        else:
            assert False

        for r in reviewers:
            self.__reviewers[r.given_query_path] = r
            self.__name_hashes[r.name_hash] = r.given_query_path
            self.status.add_item(r.status, r.given_query_path)

        self.status.finalize()

        self.fixable = set()
        self.unfixable = set()

        for q in self.status[CarverStatus.FINISHED]:
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
        "--mode",
        default="singleton",
        choices=["singleton", "doubleton"],
        help="the mode to operate on",
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
        "--reset",
        default=False,
        action="store_true",
        help="reset the project",
    )
    parser.add_argument(
        "--create",
        default=False,
        action="store_true",
        help="create the project",
    )

    args = parser.parse_args()
    mode = DbgMode(args.mode)

    if mode == DbgMode.SINGLETON:
        eva = Evaluator(
            args.input_query_path,
            verbose=True,
        )
    elif mode == DbgMode.DOUBLETON:
        eva = DoubletonEvaluator(
            args.input_query_path,
            verbose=True,
        )
    else:
        assert False

    if args.collect_garbage:
        eva.collect_garbage()

    if args.print_report:
        r = eva.report

        if r is None:
            print("No report available.")
            return

        # r.print_tested()
        r.print_stabilized()

    if args.reset:
        eva.reset_project()

    if args.create:
        eva.create_project()


if __name__ == "__main__":
    main()
