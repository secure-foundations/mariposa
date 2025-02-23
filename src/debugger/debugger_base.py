import os
from pandas import DataFrame
from debugger.debugger_options import DbgMode
from debugger.edit_tracker import EditTracker
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import InformedEditor
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
from debugger.strainer import Strainer, DebugStatus


class BaseDebugger:
    def __init__(
        self,
        tracker: EditTracker,
    ):
        mode = tracker.options.mode

        self.mode = mode
        self.name_hash = tracker.name_hash
        self.proj_name = mode.project_prefix() + tracker.name_hash
        self._report_cache = self.name_hash + mode.get_report_suffix()

        self.tracker = tracker
        self._strainer = None
        self._report = None

        if not self.tracker.proof_available():
            self.status = DebugStatus.NO_PROOF
            return

        if has_cache(self._report_cache):
            self.status = DebugStatus.FINISHED_RAW
            # load report if it's cached
            assert self.report is not None
            return

        self._strainer: Strainer = Strainer(
            self.proj_name, is_verus=tracker.options.is_verus
        )
        self.status = self._strainer.status

        if self.status.is_finished():
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
        if not self.status.is_finished():
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

        if len(r.stabilized) == 0:
            self.status = DebugStatus.FIX_NOT_FOUND
        else:
            self.status = DebugStatus.FIX_FOUND

        return r

    @property
    def report(self) -> Report:
        return self.build_report()

    @property
    def strainer(self) -> Strainer:
        if self._strainer is None:
            self._strainer = Strainer(self.proj_name)
        return self._strainer

    @property
    def given_query_path(self):
        return self.tracker.given_query_path

    def create_project(self):
        raise NotImplementedError

    def collect_garbage(self):
        self.tracker.collect_garbage()

        if not self.status.is_finished():
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
        raise NotImplementedError

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
