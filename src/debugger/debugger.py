import os
from pandas import DataFrame
from tqdm import tqdm
from debugger.debugger_base import BaseDebugger
from z3 import set_param
from calculate_average_rank import calculate_rank
from debugger.debugger_options import DbgMode, DebugOptions, resolve_input_path
from debugger.edit_tracker import EditTracker
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import InformedEditor, choose_action
from debugger.mutant_info import TraceFailure
from utils.system_utils import (
    list_smt2_files,
    log_error,
    log_info,
    log_warn,
)
from debugger.strainer import Strainer, StrainerStatus
from utils.analysis_utils import sort_by_values

set_param("proof", True)


def shorten_qname(qname: str):
    if len(qname) > 80:
        return qname[:80] + "..."
    return qname


def get_debugger(
    query_path: str,
    options=DebugOptions(),
):
    query_path = resolve_input_path(query_path, options)

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

    options.mode = mode

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
    if mode == DbgMode.SKOLEM:
        return SkolemDebugger(tracker)

    log_error(f"[init] unknown debugger mode {mode}")
    assert False


class SingletonDebugger(BaseDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        # assert tracker.options.mode == DbgMode.SINGLETON
        super().__init__(tracker)

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

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_singleton()


class DoubletonDebugger(BaseDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        assert tracker.options.mode == DbgMode.DOUBLETON
        super().__init__(tracker)

    def is_registered_edit(self, ei: EditInfo):
        return ei.is_doubleton()

    def create_project(self):
        dest_dir = self.strainer.test_dir
        log_info(f"[doubleton] creating doubleton project {dest_dir}")

        if not os.path.exists(dest_dir):
            os.makedirs(dest_dir)

        ratios = self.tracker.get_trace_graph_ratios()
        mi = self.tracker.get_trace_info()
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
        sorted_scores = sorted_scores[:10]

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
        assert tracker.options.mode == DbgMode.FAST_FAIL
        super().__init__(tracker)

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
        assert tracker.options.mode == DbgMode.TIMEOUT
        super().__init__(tracker)

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
        assert tracker.options.mode == DbgMode.FAST2
        super().__init__(tracker)

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


class SkolemDebugger(SingletonDebugger):
    def __init__(
        self,
        tracker: EditTracker,
    ):
        assert tracker.options.mode == DbgMode.SKOLEM
        super().__init__(tracker)
        skolem_query = self.tracker.given_query_path
        items = skolem_query.split("/")[-1].split(".")
        assert items[-1] == "smt2"
        self.pre_skolem_name_hash = items[0]

        pre_skolem_dbg = get_debugger(self.pre_skolem_name_hash)
        proof = pre_skolem_dbg.editor.proof

        consequences = proof.get_skolem_consequences()

        assert len(consequences) > 0

        creating_insts = dict()
        impacting_quants = dict()
        
        # print(consequences)

        for skv in consequences:
            creating_insts[skv] = sum(consequences[skv].values())
            impacting_quants[skv] = len(consequences[skv])

        chosen = sort_by_values(creating_insts)[0][0]
        
        for qname in impacting_quants[chosen]:
            print(qname)

        # editor = dbg.editor
        # ei = EditInfo(SKOLEM_DIR, {chosen: EditAction.SKOLEMIZE})
        # edit_hash = ei.get_id()
        # editor.edit_by_qname(chosen, EditAction.SKOLEMIZE)
        # success = editor.save(SKOLEM_DIR + f"/{dbg.name_hash}.{edit_hash}.smt2")