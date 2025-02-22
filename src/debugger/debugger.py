#!/usr/bin/env python3

import os
from pandas import DataFrame
from tqdm import tqdm
from z3 import set_param
from calculate_average_rank import calculate_rank
from debugger.debugger_options import DbgMode, DebugOptions, resolve_input_path
from debugger.edit_tracker import EditTracker
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import InformedEditor, choose_action
from debugger.mutant_info import TraceFailure
from utils.cache_utils import (
    clear_cache,
    has_cache,
    load_cache_or,
)
from utils.system_utils import (
    list_smt2_files,
    log_error,
    log_info,
    log_warn,
)
from debugger.strainer import Strainer, StrainerStatus

set_param("proof", True)


def shorten_qname(qname: str):
    if len(qname) > 80:
        return qname[:80] + "..."
    return qname


def get_debugger(
    query_path: str,
    options=DebugOptions(),
):
    query_path = resolve_input_path(query_path, options.verbose)

    tracker = EditTracker(
        query_path,
        options,
    )

    mode = options.mode

    if mode == DbgMode.AUTO:
        trace = tracker.get_candidate_trace()
        reason = trace.get_failed_reason()

        if reason == TraceFailure.TIMEOUT:
            mode = DbgMode.TIMEOUT
        elif reason == TraceFailure.FAST_UNKNOWN:
            mode = DbgMode.FAST_FAIL
        elif reason == TraceFailure.NOT_FAIL:
            log_warn(
                f"[init] {tracker.name_hash} trace did not fail, fallback to fast_fail"
            )
            mode = DbgMode.FAST_FAIL
        elif reason == TraceFailure.SLOW_UNKNOWN:
            log_warn(
                f"[init] {tracker.name_hash} trace slow unknown, fallback to timeout"
            )
            mode = DbgMode.TIMEOUT
        else:
            log_error(f"[init] {tracker.name_hash} unknown trace failure {reason}")
            assert False

        if options.verbose:
            log_info(f"[init] {tracker.name_hash} auto selected {mode}")

    if mode == DbgMode.SINGLETON:
        return SingletonDebugger(tracker)
    if mode == DbgMode.DOUBLETON:
        return DoubletonDebugger(tracker)
    if mode == DbgMode.FAST_FAIL:
        return FastFailDebugger(tracker)
    if mode == DbgMode.TIMEOUT:
        return TimeoutDebugger(tracker)
    if mode == DbgMode.FAST2:
        return Fast2Debugger(tracker)

    log_error(f"[init] unknown debugger mode {mode}")
    assert False


# class BaseDebugger:
#     def __init__(
#         self,
#         tracker: EditTracker,
#     ):
#         self.name_hash = tracker.name_hash
#         self.mode = DbgMode.SINGLETON

#         if not hasattr(self, "proj_name"):
#             self.proj_name = "singleton_" + self.name_hash
#             self._report_cache = self.name_hash + ".report"

#         self.tracker = tracker
#         self._strainer = None
#         self._report = None

#         if not self.tracker.proof_available():
#             self.status = StrainerStatus.NO_PROOF
#             return

#         if has_cache(self._report_cache):
#             self.status = StrainerStatus.FINISHED
#             assert self.report is not None
#             return

#         self._strainer = Strainer(self.proj_name, is_verus=tracker.options.is_verus)
#         self.status = self._strainer.status

#         if self.status == StrainerStatus.FINISHED:
#             # build report if it's finished
#             assert self.report is not None

#     @property
#     def editor(self) -> InformedEditor:
#         return self.tracker.editor

#     def _build_tested_report(self):
#         tested = []
#         root_quants = self.editor.list_root_qnames(skip_ignored=False)
#         tested_qnames = set()

#         for eid in self.strainer.tested.qids:
#             ei = self.tracker.look_up_edit_with_id(eid)
#             qname, action = ei.get_singleton_edit()
#             rc, et = self.strainer.tested.get_query_result(eid)
#             tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
#             tested_qnames.add(qname)

#         skipped = set(root_quants) - tested_qnames

#         tested = DataFrame(
#             tested, columns=["qname", "action", "result", "time", "edit_path"]
#         )
#         return tested, skipped

#     def _build_stabilized_report(self):
#         stabilized = []
#         for eid in self.strainer.filtered.get_stable_edit_ids():
#             ei = self.tracker.look_up_edit_with_id(eid)
#             qname, action = ei.get_singleton_edit()
#             if qname == "prelude_fuel_defaults":
#                 continue
#             stabilized.append((qname, action.value, ei.query_path))
#         stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
#         return stabilized

#     def build_report(self, clear=False) -> Report:
#         if self.status != StrainerStatus.FINISHED:
#             return None

#         if not clear and self._report is not None:
#             return self._report

#         def _build_report():
#             r = Report()
#             r.tested, r.skipped = self._build_tested_report()

#             if len(r.tested) == 0:
#                 log_error(f"[dbg] {self.proj_name} has no tested report")
#                 assert False

#             r.stabilized = self._build_stabilized_report()
#             r.freq = self.editor.get_inst_report()

#             # this is a hack so that we can use Pool
#             self.tracker.dispose_editor()
#             self._editor = None

#             if len(r.freq) == 0:
#                 log_error(f"[dbg] {self.proj_name} has no freq report")
#                 assert False

#             return r

#         r = load_cache_or(self._report_cache, _build_report, clear)
#         self._report = r

#         return r

#     @property
#     def report(self) -> Report:
#         if self.status != StrainerStatus.FINISHED:
#             return None
#         return self.build_report()

#     @property
#     def strainer(self) -> Strainer:
#         if self._strainer is None:
#             self._strainer = Strainer(self.proj_name)
#         return self._strainer

#     @property
#     def given_query_path(self):
#         return self.tracker.given_query_path

#     def register_singleton(self):
#         singleton_edits = self.editor.get_singleton_actions()
#         dest_dir = self.strainer.test_dir

#         for edit in singleton_edits:
#             self.tracker.register_edit(edit, dest_dir)

#         self.tracker.save_edits_meta()
#         return singleton_edits

#     def create_project(self):
#         singleton_edits = self.register_singleton()
#         dest_dir = self.strainer.test_dir

#         file_size = os.path.getsize(self.tracker.orig_path) / 1024
#         total_size = file_size * len(singleton_edits) / 1024 / 1024

#         if total_size > 20:
#             log_error(f"[edit] {dest_dir} aborted, {total_size:.2f}G may be used!")
#             return

#         log_info(f"[edit] estimated size: {total_size:.2f}G")

#         if not os.path.exists(dest_dir):
#             os.makedirs(dest_dir)

#         for action in tqdm(singleton_edits):
#             ei = EditInfo(dest_dir, action)
#             assert self.tracker.contains_edit_info(ei)
#             if ei.query_exists():
#                 log_info(f"[edit] {ei.get_id()} already exists")
#                 continue
#             self.tracker.create_edit_query(ei)

#         log_info(
#             f"[edit] [proj] {self.proj_name} has {len(list_smt2_files(dest_dir))} queries"
#         )
#         return dest_dir

#     def collect_garbage(self):
#         self.tracker.collect_garbage()

#         if self.status != StrainerStatus.FINISHED:
#             log_warn(
#                 f"[dbg] skipped GC on unfinished project {self.status} {self.given_query_path}"
#             )
#             return

#         seps = self.report.stabilized.edit_path.values

#         for row in self.report.tested.itertuples():
#             edit_path = row.edit_path
#             if edit_path in seps:
#                 # if not os.path.exists(edit_path):
#                 #     base = os.path.basename(edit_path)
#                 #     base = base.replace(".smt2", "")
#                 #     ei = self._tracker.look_up_edit_with_id(base)
#                 #     self.editor.edit_by_info(ei)
#                 #     assert os.path.exists(edit_path)
#                 continue
#             if row.result == "error":
#                 continue
#             if os.path.exists(edit_path):
#                 log_info(f"removing {edit_path}")
#                 os.remove(edit_path)

#     def is_registered_edit(self, ei: EditInfo):
#         return ei.is_singleton()

#     def get_edit_counts(self):
#         existing = list_smt2_files(self.strainer.test_dir)

#         if existing is None:
#             existing = []

#         registered_count = 0

#         for ei in self.edit_infos.values():
#             if not self.is_registered_edit(ei):
#                 continue
#             registered_count += 1

#         return registered_count, len(existing)

#     def get_sync_dirs(self):
#         return [
#             self.tracker.sub_root,
#         ] + self.strainer.get_dirs()

#     def reset_project(self):
#         self.strainer.clear_all()
#         self.clear_report_cache()

#     def clear_report_cache(self):
#         clear_cache(self._report_cache)


class SingletonDebugger:
    def __init__(
        self,
        tracker: EditTracker,
    ):
        self.name_hash = tracker.name_hash
        self.mode = DbgMode.SINGLETON

        if not hasattr(self, "proj_name"):
            self.proj_name = "singleton_" + self.name_hash
            self._report_cache = self.name_hash + ".report"

        self.tracker = tracker
        self._strainer = None
        self._report = None

        if not self.tracker.proof_available():
            self.status = StrainerStatus.NO_PROOF
            return

        if has_cache(self._report_cache):
            self.status = StrainerStatus.FINISHED
            assert self.report is not None
            return

        self._strainer = Strainer(self.proj_name, is_verus=tracker.options.is_verus)
        self.status = self._strainer.status

        if self.status == StrainerStatus.FINISHED:
            # build report if it's finished
            assert self.report is not None

    @property
    def editor(self) -> InformedEditor:
        return self.tracker.editor

    def _build_tested_report(self):
        tested = []
        root_quants = self.editor.list_root_qnames(skip_ignored=False)
        tested_qnames = set()

        for eid in self.strainer.tested.qids:
            ei = self.tracker.look_up_edit_with_id(eid)

            if ei is None:
                log_warn(f"[reprot] tested {self.name_hash} eid {eid} not found")
                continue

            qname, action = ei.get_singleton_edit()
            rc, et = self.strainer.tested.get_query_result(eid)
            tested.append((qname, action.value, str(rc), et / 1000, ei.query_path))
            tested_qnames.add(qname)

        skipped = set(root_quants) - tested_qnames

        tested = DataFrame(
            tested, columns=["qname", "action", "result", "time", "edit_path"]
        )
        return tested, skipped

    def _build_stabilized_report(self):
        stabilized = []
        for eid in self.strainer.filtered.get_stable_edit_ids():
            ei = self.tracker.look_up_edit_with_id(eid)

            if ei is None:
                log_error(f"[edit] stabilized {self.name_hash} eid {eid} not found")
                assert False

            qname, action = ei.get_singleton_edit()

            if qname == "prelude_fuel_defaults":
                continue

            stabilized.append((qname, action.value, ei.query_path))
        stabilized = DataFrame(stabilized, columns=["qname", "action", "edit_path"])
        return stabilized

    def build_report(self, clear=False) -> Report:
        if self.status != StrainerStatus.FINISHED:
            return None

        if not clear and self._report is not None:
            return self._report

        def _build_report():
            r = Report()
            r.tested, r.skipped = self._build_tested_report()

            if len(r.tested) == 0:
                log_error(f"[dbg] {self.proj_name} has no tested report")
                assert False

            r.stabilized = self._build_stabilized_report()
            r.freq = self.editor.get_inst_report()

            # this is a hack so that we can use Pool
            self.tracker.dispose_editor()
            self._editor = None

            if len(r.freq) == 0:
                log_error(f"[dbg] {self.proj_name} has no freq report")
                assert False

            return r

        r = load_cache_or(self._report_cache, _build_report, clear)
        self._report = r

        return r

    @property
    def report(self) -> Report:
        if self.status != StrainerStatus.FINISHED:
            return None
        return self.build_report()

    @property
    def strainer(self) -> Strainer:
        if self._strainer is None:
            self._strainer = Strainer(self.proj_name)
        return self._strainer

    @property
    def given_query_path(self):
        return self.tracker.given_query_path

    def register_singleton(self):
        singleton_edits = self.editor.get_singleton_actions()
        dest_dir = self.strainer.test_dir

        for edit in singleton_edits:
            self.tracker.register_edit(edit, dest_dir)

        self.tracker.save_edits_meta()
        return singleton_edits

    def create_project(self):
        singleton_edits = self.register_singleton()
        dest_dir = self.strainer.test_dir

        file_size = os.path.getsize(self.tracker.orig_path) / 1024
        total_size = file_size * len(singleton_edits) / 1024 / 1024

        if total_size > 20:
            log_error(f"[edit] {dest_dir} aborted, {total_size:.2f}G may be used!")
            return

        log_info(f"[edit] estimated size: {total_size:.2f}G")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        for action in tqdm(singleton_edits):
            ei = EditInfo(dest_dir, action)
            assert self.tracker.contains_edit_info(ei)
            if ei.query_exists():
                log_info(f"[edit] {ei.get_id()} already exists")
                continue
            self.tracker.create_edit_query(ei)

        log_info(
            f"[edit] [proj] {self.proj_name} has {len(list_smt2_files(dest_dir))} queries"
        )
        return dest_dir

    def collect_garbage(self):
        self.tracker.collect_garbage()

        if self.status != StrainerStatus.FINISHED:
            log_warn(
                f"[dbg] skipped GC on unfinished project {self.status} {self.given_query_path}"
            )
            return

        seps = self.report.stabilized.edit_path.values

        for row in self.report.tested.itertuples():
            edit_path = row.edit_path
            if edit_path in seps:
                # if not os.path.exists(edit_path):
                #     base = os.path.basename(edit_path)
                #     base = base.replace(".smt2", "")
                #     ei = self._tracker.look_up_edit_with_id(base)
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
        existing = list_smt2_files(self.strainer.test_dir)

        if existing is None:
            existing = []

        registered_count = 0

        for ei in self.edit_infos.values():
            if not self.is_registered_edit(ei):
                continue
            registered_count += 1

        return registered_count, len(existing)

    def get_sync_dirs(self):
        return [
            self.tracker.sub_root,
        ] + self.strainer.get_dirs()

    def reset_project(self):
        self.strainer.clear_all()
        self.clear_report_cache()

    def clear_report_cache(self):
        clear_cache(self._report_cache)


class DoubletonDebugger(SingletonDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        self.proj_name = "doubleton_" + tracker.name_hash
        self._report_cache = tracker.name_hash + ".2.report"
        super().__init__(tracker)
        self.mode = DbgMode.DOUBLETON

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_doubleton()

    def create_project(self):
        dest_dir = self.strainer.test_dir
        log_info(f"[doubleton] creating doubleton project {dest_dir}")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        ratios = self.tracker.get_trace_graph_ratios()
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
            ei = self.tracker.register_edit(edit, dest_dir)
            self.tracker.create_edit_query(ei)

        self.tracker.save_edits_meta()

    def _build_tested_report(self):
        tested = []

        for eid in self.strainer.tested.qids:
            ei = self.tracker.look_up_edit_with_id(eid)
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

    def _build_stabilized_report(self):
        stabilized = []
        for eid in self.strainer.filtered.get_stable_edit_ids():
            ei = self.tracker.look_up_edit_with_id(eid)
            (q1, a1), (q2, a2) = ei.get_doubleton_edit()
            stabilized.append((q1, a1.value, q2, a2.value, ei.query_path))
        stabilized = DataFrame(
            stabilized, columns=["qname1", "action1", "qname2", "action2", "edit_path"]
        )
        return stabilized


class FastFailDebugger(SingletonDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        self.proj_name = "fast_fail_" + tracker.name_hash
        self._report_cache = tracker.name_hash + ".ff.report"
        super().__init__(tracker)
        self.mode = DbgMode.FAST_FAIL

    def create_project(self):
        name_hash = "cache/" + self.name_hash + ".report"
        rank = calculate_rank(name_hash, ranking_heuristic="proof_count")
        dst_dir = self.strainer.test_dir

        if not os.path.exists(dst_dir):
            os.makedirs(dst_dir)

        emitted_count = 0

        for row in rank.iterrows():
            if emitted_count >= 10:
                break

            qname = row[1].qname
            action = choose_action(self.editor.get_quant_actions(qname))
            ei = self.tracker.register_edit({qname: action}, dst_dir)
            ei.edit_dir = dst_dir

            if self.tracker.create_edit_query(ei):
                emitted_count += 1

        self.tracker.save_edits_meta()


class TimeoutDebugger(SingletonDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        # this is just dumb
        self.proj_name = "timeout_" + tracker.name_hash
        self._report_cache = tracker.name_hash + ".to.report"
        super().__init__(tracker)
        self.mode = DbgMode.TIMEOUT

    def rank_edits(self):
        trace_graph = self.tracker.get_trace_graph()
        ratios = self.tracker.get_trace_graph_ratios()
        scores = dict()

        for qname, ratio in ratios.items():
            actions = self.editor.get_quant_actions(qname)
            if actions == {EditAction.NONE}:
                continue
            if actions == {EditAction.SKOLEMIZE}:
                continue
            if EditAction.ERROR in actions:
                if len(actions) != 1:
                    log_warn(
                        f"[edit] {self.name_hash} {qname} has error and other actions? {actions}"
                    )
                continue
            scores[qname] = trace_graph.aggregate_scores(ratio)

        scores = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        return scores

    def create_project(self):
        ranked = self.rank_edits()
        dst_dir = self.strainer.test_dir

        if not os.path.exists(dst_dir):
            os.makedirs(dst_dir)

        emitted_count = 0
        for qname, _ in ranked:
            if emitted_count >= 10:
                break

            action = choose_action(self.editor.get_quant_actions(qname))
            actions = {qname: action}
            ei = self.tracker.register_edit(actions, dst_dir)
            ei.edit_dir = dst_dir

            if self.tracker.create_edit_query(ei):
                emitted_count += 1

        self.tracker.save_edits_meta()


class Fast2Debugger(SingletonDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        self._report_cache = tracker.name_hash + ".ff2.report"

        super().__init__(tracker)
        self.mode = DbgMode.FAST2

    @property
    def proj_name(self):
        return "ff2_" + self.name_hash

    def rank_edits(self):
        trace_graph = self.tracker.get_trace_graph()
        ratios = self.tracker.get_trace_graph_ratios()
        scores = dict()

        for qname, ratio in ratios.items():
            actions = self.editor.get_quant_actions(qname)

            if EditAction.ERROR in actions:
                if len(actions) != 1:
                    log_warn(
                        f"[edit] {self.name_hash} {qname} has error and other actions? {actions}"
                    )
                continue

            if (
                EditAction.INST_REPLACE not in actions
                and EditAction.INST_KEEP not in actions
            ):
                continue
            scores[qname] = trace_graph.aggregate_scores(ratio)

        scores = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        return scores

    def create_project(self):
        ranked = self.rank_edits()
        dst_dir = self.strainer.test_dir

        if not os.path.exists(dst_dir):
            os.makedirs(dst_dir)

        emitted_count = 0

        for qname, _ in ranked:
            if emitted_count >= 10:
                break

            actions = {qname: EditAction.INST_KEEP}
            ei = self.tracker.register_edit(actions, dst_dir)
            ei.edit_dir = dst_dir

            if self.tracker.create_edit_query(ei):
                emitted_count += 1

        self.tracker.save_edits_meta()
