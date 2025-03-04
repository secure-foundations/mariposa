import os
from pandas import DataFrame
from functools import cached_property
import numpy as np
from debugger.options import DbgMode
from debugger.edit_tracker import EditTracker
from debugger.demo_utils import Report
from debugger.edit_info import EditAction, EditInfo
from debugger.informed_editor import InformedEditor
from debugger.mutant_info import TraceFailure
from debugger.query_loader import QueryLoader
from utils.cache_utils import (
    clear_cache,
    has_cache,
    load_cache_or,
)
from utils.system_utils import (
    list_smt2_files,
    log_check,
    log_error,
    log_info,
    log_warn,
)
from debugger.strainer import Strainer, DebugStatus


class QueryStats:
    def __init__(self):
        self.trace_inst_count = np.nan
        self.proof_inst_count = np.nan
        self.all_qnames = None
        self.kept_qnames = None


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
        self._report = None

        if not self.tracker.proof_available():
            self.status = DebugStatus.NO_PROOF
            return

        if has_cache(self._report_cache):
            self.status = DebugStatus.FINISHED_RAW
            # load report if it's cached
            assert self.report is not None
            return
        self.status = self.strainer.status

        if self.status.is_finished():
            # build report if it's finished
            assert self.report is not None

    @property
    def editor(self) -> InformedEditor:
        return self.tracker.editor

    # this is a hack to work around Pool...
    def dispose_editor(self):
        self.tracker.dispose_editor()
        self._editor = None

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
            self.dispose_editor()

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

    @cached_property
    def strainer(self) -> Strainer:
        return Strainer(self.proj_name)

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

    def _build_query_stats(self) -> QueryStats:
        qstats = QueryStats()

        loader = QueryLoader(self.tracker.orig_path)
        qstats.all_qnames = set(loader.list_qnames(root_only=False))

        if self.status.is_finished():
            qstats.kept_qnames = qstats.all_qnames - self.editor.ignored
        else:
            qstats.kept_qnames = qstats.all_qnames - set(
                loader.list_qnames(root_only=True)
            )
        loader = None
        if self.status == DebugStatus.NO_PROOF:
            log_warn(f"[dbg] {self.name_hash} has no proof, inst count is set to nan")
            qstats.proof_inst_count = np.nan
            qstats.trace_inst_count = np.nan
            return qstats

        if not self.status.is_finished():
            # TODO: should decouple the inst report from the full report
            report = self.editor.get_inst_report()
        else:
            report = self.report.freq

        qstats.proof_inst_count = sum(report.proof_count.values)
        qstats.trace_inst_count = sum(report.trace_count.values)

        # dispose editor ... otherwise Pool dies
        self.dispose_editor()
        return qstats

    def build_query_stats(self, clear=False) -> QueryStats:
        cache_name = self.name_hash + ".qstats"
        return load_cache_or(cache_name, self._build_query_stats, clear)

    @cached_property
    def query_stats(self) -> QueryStats:
        # this will not force clear cache
        return self.build_query_stats()

    def get_basic_command(self):
        verus_flag = "--verus" if self.tracker.options.is_verus else "--not-verus"
        return f"./src/debugger3.py --mode {self.mode.value} -i {self.name_hash} {verus_flag}"

    def get_create_command(self):
        return f"{self.get_basic_flags()} --create-project"

    def get_reset_command(self):
        return f"{self.get_basic_flags()} --reset-project"

    def tell_me_what_to_do(self, local):
        if self.status.is_finished():
            return f"# {self.name_hash} finished"

        if self.status == DebugStatus.NOT_TESTED:
            log_check(
                len(list_smt2_files(self.strainer.filter_dir)) != 0,
                f"{self.name_hash} has no filtered queries",
            )
            server_opt = "--local" if local else "--cluster"
            return f"./src/make_spaghet.py {server_opt} -i {self.strainer.filter_dir}"

        if self.status == DebugStatus.UNFILTERED:
            log_check(
                len(list_smt2_files(self.strainer.test_dir)) != 0,
                f"{self.name_hash} has no test queries",
            )
            return f"./src/make_spaghet.py {server_opt} -i {self.strainer.test_dir}"

        if self.status == DebugStatus.ERROR:
            return self.get_reset_command()
