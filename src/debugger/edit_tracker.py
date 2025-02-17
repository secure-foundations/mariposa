import json
import os
from typing import Dict

from base.defs import DEBUG_ROOT, MARIPOSA
from debugger.debugger_options import DebugOptions
from debugger.edit_info import EditAction, EditInfo
from debugger.mutant_builder import MutantBuilder
from debugger.mutant_info import MutantInfo
from debugger.proof_analyzer import ProofAnalyzer
from debugger.informed_editor import InformedEditor
from utils.cache_utils import load_cache_or
from utils.query_utils import find_verus_procedure_name
from utils.system_utils import *


class EditTracker:
    def __init__(
        self,
        query_path,
        options: DebugOptions,
    ):
        self.given_query_path = query_path
        self.name_hash = get_name_hash(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.name_hash}"

        if options.verbose:
            log_info(f"[init] dbg root: {self.sub_root}/")

        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.query_meta = f"{self.sub_root}/meta.json"

        self.chosen_proof_path = None
        self.chosen_trace_path = None
        self.__clear_proof_cache = False

        self.edit_infos: Dict[int, EditInfo] = dict()
        self.edits_meta = f"{self.sub_root}/edits.json"
        self.edit_dir = f"{self.sub_root}/edits/"

        if not os.path.exists(self.sub_root):
            create_dir(self.edit_dir)

        self.__init_edits()
        self.__init_meta()

        self._builder = MutantBuilder(
            query_path,
            self.sub_root,
            options,
        )

        self.set_proof()
        self.set_trace()

        self._editor = None

    def set_proof(self):
        if self.chosen_proof_path is not None and os.path.exists(
            self.chosen_proof_path
        ):
            return
        if len(self._builder.proofs) == 0:
            log_warn("[proof] no proof available")
            return
        self.chosen_proof_path = self._builder.proofs[0].proof_path
        self.__save_query_meta()

    def set_trace(self):
        if self.chosen_trace_path is not None and os.path.exists(
            self.chosen_trace_path
        ):
            return
        if trace := self._builder.get_candidate_trace():
            self.chosen_trace_path = trace.trace_path
            log_info(f"[trace] chosen: {self.chosen_trace_path}")
        self.__save_query_meta()

    def reroll_trace(self):
        self._builder.build_traces()

    def reset_all(self):
        if os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

    def __init_edits(self):
        self.edit_infos = dict()

        if not os.path.exists(self.edits_meta):
            return

        infos = json.load(open(self.edits_meta, "r"))

        for ei in infos:
            if not os.path.isdir(ei["edit_dir"]):
                continue
            ei = EditInfo.from_dict(ei)
            self.edit_infos[ei.get_id()] = ei

    def __init_meta(self):
        if not os.path.exists(self.query_meta):
            self.__save_query_meta()
            log_info(f"[init] basic meta data written to {self.query_meta}")
        else:
            self.meta_data = json.load(open(self.query_meta, "r"))
            self.chosen_proof_path = self.meta_data["chosen_proof"]
            self.chosen_trace_path = self.meta_data["chosen_trace"]

    def __save_query_meta(self):
        verus_proc = find_verus_procedure_name(self.given_query_path)
        self.meta_data = {
            "given_query": self.given_query_path,
            "verus_proc": verus_proc,
            "sub_root": self.sub_root,
            "chosen_proof": self.chosen_proof_path,
            "chosen_trace": self.chosen_trace_path,
        }
        json.dump(
            self.meta_data,
            open(self.query_meta, "w+"),
        )

    def collect_garbage(self):
        if not self.chosen_trace_path:
            self.set_trace()
        self._builder.collect_garbage(self.chosen_trace_path)

    def reset_proof_cache(self):
        if len(self._builder.proofs) == 0:
            return
        self.__clear_proof_cache = True
        self.editor is not None

    def proof_available(self):
        return len(self._builder.proofs) != 0

    @property
    def editor(self) -> InformedEditor:
        if self._editor is not None:
            return self._editor
        assert len(self._builder.proofs) != 0
        assert self.chosen_proof_path is not None
        log_debug(f"[edit] proof path: {self.chosen_proof_path}")
        log_debug(f"[edit] trace path: {self.chosen_trace_path}")
        if self.__clear_proof_cache:
            log_info("[edit] clearing proof cache")
        proof = ProofAnalyzer.from_proof_file(
            self.chosen_proof_path, clear=self.__clear_proof_cache
        )
        trace = self._builder.get_trace_mutant_info(self.chosen_trace_path)
        assert trace.has_trace()
        self._editor = InformedEditor(
            self.orig_path,
            proof,
            trace,
        )
        return self._editor

    def save_edits_meta(self):
        infos = [ei.to_dict() for ei in self.edit_infos.values()]

        with open(self.edits_meta, "w+") as f:
            json.dump(infos, f)

    def clear_edits(self):
        if os.path.exists(self.edit_dir):
            count = len(os.listdir(self.edit_dir))
            if count > 10:
                confirm_input(f"clear {count} edits?")
            os.system(f"rm {self.edit_dir}*")
        self.edit_infos = dict()
        self.save_edits_meta()
        log_info("[edit] cleared")

    def test_edit(self, edit):
        ei = self.register_edit_info(edit)
        if ei.has_data():
            return ei
        ei.run_query()
        self.edit_infos[ei.get_id()] = ei
        return ei

    def test_edit_with_id(self, edit_id) -> EditInfo:
        assert edit_id in self.edit_infos
        ei = self.edit_infos[edit_id]
        if not ei.query_exists():
            self.editor.save_edit(ei)
        if not ei.has_data():
            ei.run_query()
        return ei

    def look_up_edit_with_id(self, eid) -> EditInfo:
        return self.edit_infos[eid]

    def contains_edit_info(self, ei: EditInfo):
        return ei.get_id() in self.edit_infos

    def get_edited_qnames(self, eids):
        res = set()
        for eid in eids:
            res |= self.edit_infos[eid].actions.keys()
        return res

    def register_edit(self, actions, output_dir=None) -> EditInfo:
        assert isinstance(actions, dict)

        if not output_dir:
            output_dir = self.edit_dir

        ei = EditInfo(output_dir, actions)
        eid = ei.get_id()

        if eid in self.edit_infos:
            return self.edit_infos[eid]

        self.edit_infos[eid] = ei

        return ei

    def look_up_edit(self, edit):
        res = []

        for ei in self.edit_infos:
            if set(ei.edit.keys()) & edit.keys() != set():
                res.append(ei)

        return res

    def create_edit_query(self, ei: EditInfo):
        eid = ei.get_id()
        assert eid in self.edit_infos

        if not ei.query_exists():
            return self.editor.edit_by_info(ei)
        log_debug(f"[edit] {ei.get_id()} already exists")
        return True

    def get_status(self):
        return {
            "verus_proc": self.meta_data["verus_proc"],
            "sub_root": self.meta_data["sub_root"],
            "traces": len(self._builder.traces),
            "cores": len(self._builder.cores),
            "proofs": len(self._builder.proofs),
        }

    def print_status(self):
        status = self.get_status()

        print("given query:", self.given_query_path)
        print("verus proc:", status["verus_proc"])

        for trace in self._builder.traces:
            print("trace:", trace.trace_path, trace.trace_rcode, trace.trace_time)

        if self.chosen_proof_path:
            print("chosen proof:", self.chosen_proof_path)
            print("chosen trace:", self.chosen_trace_path)

    def get_trace_info(self) -> MutantInfo:
        # log_warn(f"[trace] no failed trace available for {self.name_hash}")
        return self._builder.get_trace_mutant_info(self.chosen_trace_path)

    def get_trace_graph(self, clear=False):
        mi = self.get_trace_info()
        return mi.get_trace_graph(clear)

    def get_trace_graph_ratios(self, clear=False):
        def _compute_ratios():
            return self.editor.get_sub_ratios(clear)

        name = self.name_hash + ".ratios"
        return load_cache_or(name, _compute_ratios, clear)
