import json
import os
from typing import Dict
from tqdm import tqdm
from tabulate import tabulate

from base.defs import DEBUG_ROOT, MARIPOSA
from debugger.edit_info import EditAction, EditInfo
from debugger.file_builder import FileBuilder
from debugger.mutant_info import MutantInfo
from debugger.pool_utils import run_with_pool
from debugger.proof_analyzer import ProofAnalyzer
from debugger.informed_editor import InformedEditor
from utils.cache_utils import load_cache_or
from utils.query_utils import find_verus_procedure_name
from utils.system_utils import *


def _run_edit(ei: EditInfo):
    ei.run_query()
    return ei


def resolve_input_path(input_path):
    if len(input_path) == 10:
        input_path = f"dbg/{input_path}"
    if input_path.startswith("dbg/") or input_path.startswith("./dbg/"):
        assert not input_path.endswith(".smt2")
        meta = json.load(open(f"{input_path}/meta.json", "r"))
        input_path = meta["given_query"]
        log_info(f"[init] resolved to {input_path}")
    if not os.path.exists(input_path):
        log_warn(f"[init] query path {input_path} not found")
        sys.exit(1)
    return input_path


class Debugger3:
    def __init__(
        self,
        query_path,
        ids_available=False,
        retry_failed=False,
        clear_all=False,
        clear_edits=False,
        clear_traces=False,
        clear_cores=False,
        clear_proofs=False,
        skip_core=False,
    ):
        query_path = resolve_input_path(query_path)
        self.given_query_path = query_path
        self.name_hash = get_name_hash(query_path)
        self.base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.name_hash}"

        log_info(f"[init] dbg root: {self.sub_root}/")

        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.query_meta = f"{self.sub_root}/meta.json"

        self.chosen_proof_path = None
        self.chosen_trace_path = None

        self.__clear_proof_cache = False

        if clear_all:
            self.__clear_proof_cache = True

        self.__edit_infos: Dict[int, EditInfo] = dict()
        self.edits_meta = f"{self.sub_root}/edits.json"
        self.edit_dir = f"{self.sub_root}/edits/"

        self.singleton_name = "singleton_" + self.name_hash

        self.singleton_dir = f"data/projs/{self.singleton_name}/base.z3"
        self.filtered_dir = f"data/projs/{self.singleton_name}.filtered/base.z3"
        self.singleton_db_dir = f"data/dbs/{self.singleton_name}/base.z3"
        self.filtered_db_dir = f"data/dbs/{self.singleton_name}.filtered/base.z3"

        self.splitter_name = "splitter_" + self.name_hash
        self.splitter_dir = f"data/projs/{self.splitter_name}/base.z3"

        self.__init_dirs(clear_all)
        self.__init_edits(clear_edits)
        self.__init_meta()

        self._builder = FileBuilder(
            query_path,
            self.sub_root,
            ids_available=ids_available,
            retry_failed=retry_failed,
            clear_traces=clear_traces,
            clear_cores=clear_cores,
            clear_proofs=clear_proofs,
            skip_core=skip_core,
        )

        if self.chosen_proof_path is None:
            self.set_proof()

        self._editor = None

    def set_proof(self):
        if len(self._builder.proofs) == 0:
            log_warn("[proof] no proof available")
            return
        self.chosen_proof_path = self._builder.proofs[0].proof_path
        self.chosen_trace_path = self._builder.get_candidate_trace().trace_path
        self.__save_query_meta()

    def __init_dirs(self, reset):
        if reset and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

        create_dir(self.edit_dir)

        if not reset:
            return

        log_info(f"[init] removing singleton project {self.singleton_name}")

        for d in [
            self.singleton_dir,
            self.filtered_dir,
            self.singleton_db_dir,
            self.filtered_db_dir,
        ]:
            if os.path.exists(d):
                os.system(f"rm -rf {d}")

    def __init_edits(self, clear_edits):
        self.__edit_infos = dict()

        if clear_edits:
            self.clear_edits()
            return

        if not os.path.exists(self.edits_meta):
            return

        infos = json.load(open(self.edits_meta, "r"))

        for ei in infos:
            if not os.path.isdir(ei["edit_dir"]):
                continue
            ei = EditInfo.from_dict(ei)
            self.__edit_infos[ei.get_id()] = ei

        # self.save_edits_meta()

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
            self.chosen_trace_path = self._builder.get_candidate_trace().trace_path
        self._builder.collect_garbage(self.chosen_trace_path)

    def reset_proof_cache(self):
        if len(self._builder.proofs) == 0:
            return
        self.__clear_proof_cache = True
        self.editor is not None

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
        infos = [ei.to_dict() for ei in self.__edit_infos.values()]

        with open(self.edits_meta, "w+") as f:
            json.dump(infos, f)

    def clear_edits(self):
        if os.path.exists(self.edit_dir):
            count = len(os.listdir(self.edit_dir))
            if count > 10:
                confirm_input(f"clear {count} edits?")
            os.system(f"rm {self.edit_dir}*")
        self.__edit_infos = dict()
        self.save_edits_meta()
        log_info("[edit] cleared")

    def get_singleton_edits(self):
        feasible_edits = self.editor.get_singleton_actions()
        extended_edits = []

        for qid, action in feasible_edits.items():
            if action == EditAction.INST_REPLACE:
                extended_edits.append({qid: EditAction.INST_KEEP})
            extended_edits.append({qid: action})

        return extended_edits

    def register_singleton(self):
        extended_edits = self.get_singleton_edits()

        for edit in extended_edits:
            self.register_edit(edit, self.singleton_dir)

        self.save_edits_meta()
        return extended_edits

    def create_singleton(self):
        if len(self.__edit_infos) == 0:
            self.register_singleton()

        file_size = os.path.getsize(self.orig_path) / 1024
        total_size = file_size * len(self.__edit_infos) / 1024 / 1024

        if total_size > 15:
            log_error(
                f"[edit] {self.singleton_dir} aborted, {total_size:.2f}G may be used!"
            )
            return

        log_info(f"[edit] estimated size: {total_size:.2f}G")

        extended_edits = self.get_singleton_edits()

        if not os.path.exists(self.singleton_dir):
            os.makedirs(self.singleton_dir)

        for action in tqdm(extended_edits):
            ei = EditInfo(self.singleton_dir, action)
            assert ei.get_id() in self.__edit_infos
            if ei.query_exists():
                log_info(f"[edit] {ei.get_id()} already exists")
                continue
            self.create_edit_query(ei)

        log_info(
            f"[edit] [proj] {self.singleton_name} has {len(list_smt2_files(self.singleton_dir))} queries"
        )
        return self.singleton_dir

    def get_singleton_status(self):
        existing = list_smt2_files(self.singleton_dir)
        if existing is None:
            existing = []
        return len(self.__edit_infos), len(existing)

    def check_singleton(self):
        existing = list_smt2_files(self.singleton_dir)
        # for query in existing:
        #     basename = os.path.basename(query)
        #     eid = basename.split(".smt2")[0]
        #     if eid in self.__edit_infos:
        #         continue
        #     log_error(f"[edit] {self.singleton_dir}/{eid}.smt2 is not registered!")

    def test_edit(self, edit):
        ei = self.register_edit_info(edit)
        if ei.has_data():
            return ei
        ei.run_query()
        self.__edit_infos[ei.get_id()] = ei
        return ei

    def test_edit_with_id(self, edit_id) -> EditInfo:
        assert edit_id in self.__edit_infos
        ei = self.__edit_infos[edit_id]
        if not ei.query_exists():
            self.editor.save_edit(ei)
        if not ei.has_data():
            ei.run_query()
        return ei

    def look_up_edit_with_id(self, eid) -> EditInfo:
        return self.__edit_infos[eid]

    def get_edited_qnames(self, eids):
        res = set()
        for eid in eids:
            res |= self.__edit_infos[eid].actions.keys()
        return res

    def register_edit(self, actions, output_dir=None) -> EditInfo:
        if isinstance(actions, set):
            actions = {qid: self.editor.get_quant_action(qid) for qid in actions}
        else:
            assert isinstance(actions, dict)

        if not output_dir:
            output_dir = self.edit_dir

        ei = EditInfo(output_dir, actions)
        eid = ei.get_id()

        if eid in self.__edit_infos:
            return self.__edit_infos[eid]

        self.__edit_infos[eid] = ei

        return ei

    def look_up_edit(self, edit):
        res = []

        for ei in self.__edit_infos:
            if set(ei.edit.keys()) & edit.keys() != set():
                res.append(ei)

        return res

    def create_edit_query(self, ei: EditInfo):
        eid = ei.get_id()
        assert eid in self.__edit_infos

        if not ei.query_exists():
            self.editor.edit_by_info(ei)
        else:
            log_debug(f"[edit] {ei.get_id()} already exists")

    # def _try_edits(self, targets, run_query):
    #     args = []

    #     for edit in tqdm(targets):
    #         ei = self.register_edit_info(edit)
    #         if ei.has_data():
    #             continue
    #         args.append(ei)

    #     if not run_query:
    #         log_info(f"[edit] skipped running, queries saved in {self.edit_dir}")
    #         return

    #     run_res = run_with_pool(_run_edit, args)

    #     for ei in run_res:
    #         assert ei.has_data()
    #         self.__edit_infos[ei.get_id()] = ei

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
        assert self.chosen_trace_path is not None
        return self._builder.get_trace_mutant_info(self.chosen_trace_path)

    def get_trace_graph(self, clear=False):
        mi = self.get_trace_info()
        return mi.get_trace_graph(clear)

    def get_trace_graph_ratios(self, clear=False):
        def _compute_ratios():
            return self.editor.get_sub_ratios(True)
        name = self.name_hash + ".ratios"
        return load_cache_or(name, _compute_ratios, clear)
