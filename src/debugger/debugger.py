#!/usr/bin/env python3

import os
from pandas import DataFrame
from tabulate import tabulate
from tqdm import tqdm
from calculate_average_rank import calculate_rank
from debugger.debugger_options import DebugOptions, resolve_input_path
from debugger.edit_tracker import EditTracker
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import choose_action
from utils.cache_utils import (
    clear_cache,
    has_cache,
    load_cache,
    save_cache,
)
from base.factory import FACT
from utils.system_utils import (
    get_name_hash,
    list_smt2_files,
    log_error,
    log_info,
    log_warn,
)
from enum import Enum
import argparse
from debugger.strainer import Strainer, StrainerStatus
from debugger.debugger_options import DebugOptions, resolve_input_path


def shorten_qname(qname: str):
    if len(qname) > 80:
        return qname[:80] + "..."
    return qname


class DbgMode(Enum):
    SINGLETON = "singleton"
    DOUBLETON = "doubleton"
    FAST_FAIL = "fast_fail"


class Debugger(EditTracker):
    def __init__(
        self,
        query_path: str,
        options=DebugOptions(),
    ):
        query_path = resolve_input_path(query_path, options.verbose)

        super().__init__(
            query_path,
            options,
        )

        if not hasattr(self, "proj_name"):
            self.proj_name = "singleton_" + self.name_hash
            self._report_cache = self.name_hash + ".report"

        self._strainer = None
        self._report = None

        if self.get_status()["proofs"] == 0:
            self.status = StrainerStatus.NO_PROOF
            return

        if has_cache(self._report_cache):
            self.status = StrainerStatus.FINISHED
            self._report = load_cache(self._report_cache)
            return

        self._strainer = Strainer(self.proj_name)
        self.status = self._strainer.status

    def _build_tested(self):
        tested = []
        root_quants = self.editor.list_root_qnames(skip_ignored=False)
        tested_qnames = set()

        for eid in self.strainer.tested.qids:
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            rc, et = self.strainer.tested.get_query_result(eid)
            tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
            tested_qnames.add(qname)

        skipped = set(root_quants) - tested_qnames

        tested = DataFrame(
            tested, columns=["qname", "action", "result", "time", "edit_path"]
        )
        return tested, skipped

    def _build_stabilized(self):
        stabilized = []
        for eid in self.strainer.filtered.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            qname, action = ei.get_singleton_edit()
            if qname == "prelude_fuel_defaults":
                continue
            stabilized.append((qname, action.value, ei.query_path))
        stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
        return stabilized

    @property
    def strainer(self) -> Strainer:
        if self._strainer is None:
            self._strainer = Strainer(self.proj_name)
        return self._strainer

    @property
    def report(self) -> Report:
        if self.status != StrainerStatus.FINISHED:
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
        dest_dir = self.strainer.test_dir()

        for edit in singleton_edits:
            self.register_edit(edit, dest_dir)

        self.save_edits_meta()
        return singleton_edits

    def create_project(self):
        singleton_edits = self.register_singleton()
        dest_dir = self.strainer.test_dir()

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

        if self.status != StrainerStatus.FINISHED:
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
        existing = list_smt2_files(self.strainer.test_dir())

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
        ] + self.strainer.get_dirs()

    def reset_project(self):
        self.strainer.clear_all()

    def clear_report_cache(self):
        clear_cache(self._report_cache)


class DoubletonDebugger(Debugger):
    def __init__(
        self,
        query_path: str,
        options=DebugOptions(),
    ):
        # this is just dumb
        query_path = resolve_input_path(query_path, options.verbose)
        self.name_hash = get_name_hash(query_path)

        self.proj_name = "doubleton_" + self.name_hash
        self._report_cache = self.name_hash + ".2.report"

        super().__init__(
            query_path,
            options,
        )

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_doubleton()

    def create_project(self):
        dest_dir = self.strainer.test_dir
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

        for eid in self.strainer.tested.qids:
            ei = self.look_up_edit_with_id(eid)
            (q1, a1), (q2, a2) = ei.get_doubleton_edit()
            rc, et = self.strainer.tested.get_query_result(eid)
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
        for eid in self.strainer.filtered.get_stable_edit_ids():
            ei = self.look_up_edit_with_id(eid)
            (q1, a1), (q2, a2) = ei.get_doubleton_edit()
            stabilized.append((q1, a1.value, q2, a2.value, ei.query_path))
        stabilized = DataFrame(
            stabilized, columns=["qname1", "action1", "qname2", "action2", "edit_path"]
        )
        return stabilized


class FastFailDebugger(Debugger):
    def __init__(
        self,
        query_path: str,
        options=DebugOptions(),
    ):
        # this is just dumb
        query_path = resolve_input_path(query_path, options.verbose)
        self.name_hash = get_name_hash(query_path)

        self.proj_name = "fast_fail_" + self.name_hash
        self._report_cache = self.name_hash + ".ff.report"

        super().__init__(query_path, options)

    def create_project(self):
        name_hash = "cache/" + self.name_hash + ".report"
        rank = calculate_rank(name_hash, ranking_heuristic="proof_count")
        dst_dir = self.strainer.test_dir

        if not os.path.exists(dst_dir):
            os.makedirs(dst_dir)

        for row in rank[:10].iterrows():
            qname = row[1].qname
            action = choose_action(self.editor.get_quant_actions(qname))
            ei = self.register_edit({qname: action}, dst_dir)
            ei.edit_dir = dst_dir
            self.create_edit_query(ei)

        self.save_edits_meta()
