#!/usr/bin/env python3

import argparse
import json
import os
from z3 import set_param
from typing import Dict, List
from tqdm import tqdm
from tabulate import tabulate

from base.defs import DEBUG_ROOT, MARIPOSA
from base.solver import RCode
from debugger.edit_info import EditAction, EditInfo
from debugger.file_builder import FileBuilder
from debugger.pool_utils import run_with_pool
from debugger.proof_analyzer import ProofAnalyzer
from debugger.informed_editor import InformedEditor
from utils.query_utils import find_verus_procedure_name
from utils.system_utils import *


def _run_edit(ei: EditInfo):
    ei.run_query()
    return ei


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
        clear_proof_cache=False,
        skip_core=False,
        overwrite_reports=False,
    ):
        if not os.path.exists(query_path):
            log_warn(f"[init] query path {query_path} not found")
            return

        self.given_query_path = query_path
        self.name_hash = get_name_hash(query_path)
        self.base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.name_hash}"

        log_info(f"[init] query path: {query_path}")
        log_info(f"[init] dbg root: {self.sub_root}")

        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.query_meta = f"{self.sub_root}/meta.json"

        self.chosen_proof_path = None
        self.chosen_trace_path = None

        if clear_all:
            self.__clear_proof_cache = True
        else:
            self.__clear_proof_cache = clear_proof_cache

        self.__edit_infos: Dict[int, EditInfo] = dict()
        self.edits_meta = f"{self.sub_root}/edits.json"
        self.edit_dir = f"{self.sub_root}/edits/"

        self.singleton_project = "singleton_" + self.name_hash
        self.singleton_dir = f"data/projs/{self.singleton_project}/base.z3"
        self.singleton_filtered_dir = self.singleton_dir.replace(
            "/base.z3", ".filtered/base.z3"
        )

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

        # print(self.chosen_proof_path)
        # print(self.chosen_trace_path)
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

        log_info(f"[init] removing singleton project {self.singleton_project}")
        remove_dir("data/projs/" + self.singleton_project)
        remove_dir("data/projs/" + self.singleton_project + ".filtered")
        remove_dir("data/dbs/" + self.singleton_project)
        remove_dir("data/dbs/" + self.singleton_project + ".filtered")

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

        self.save_edits_meta()

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
        self._builder.collect_garbage(self.chosen_trace_path)

    @property
    def editor(self) -> InformedEditor:
        if self._editor is not None:
            return self._editor
        log_debug(f"[edit] proof path: {self.chosen_proof_path}")
        log_debug(f"[edit] trace path: {self.chosen_trace_path}")
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

    def create_singleton_project(self):
        singleton_dir = f"data/projs/{self.singleton_project}/base.z3"
        filter_dir = f"data/projs/{self.singleton_project}.filtered/base.z3"

        create_dir(singleton_dir)
        create_dir(filter_dir)

        if list_smt2_files(singleton_dir) == [] or True:
            feasible_edits = self.editor.get_singleton_actions()
            for qid, action in tqdm(feasible_edits.items()):
                self.register_edit_info({qid: action}, singleton_dir)
                if action == EditAction.INST_REPLACE:
                    # this is also feasible
                    self.register_edit_info({qid: EditAction.INST_KEEP}, singleton_dir)
            self.save_edits_meta()
            log_info(f"[edit] {self.singleton_project} created")
        else:
            log_warn(f"[proj] {self.singleton_project} already exists")

        query_count = len(list_smt2_files(singleton_dir))
        log_info(f"[edit] [proj] {self.singleton_project} has {query_count} queries")

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

    def register_edit_info(self, actions, output_dir=None):
        if isinstance(actions, set):
            actions = {qid: self.editor.get_quant_action(qid) for qid in actions}
        else:
            assert isinstance(actions, dict)

        if not output_dir:
            output_dir = self.edit_dir

        create_dir(output_dir)

        ei = EditInfo(output_dir, actions)
        eid = ei.get_id()

        if not ei.query_exists():
            self.editor.edit_by_info(ei)

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

    def _try_edits(self, targets, run_query):
        args = []

        for edit in tqdm(targets):
            ei = self.register_edit_info(edit)
            if ei.has_data():
                continue
            args.append(ei)

        if not run_query:
            log_info(f"[edit] skipped running, queries saved in {self.edit_dir}")
            return

        run_res = run_with_pool(_run_edit, args)

        for ei in run_res:
            assert ei.has_data()
            self.__edit_infos[ei.get_id()] = ei

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


def main():
    set_param(proof=True)
    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "--skip-core",
        default=False,
        action="store_true",
        help="skip building cores",
    )
    parser.add_argument(
        "--retry-failed",
        default=False,
        action="store_true",
        help="retry failed experiments",
    )
    parser.add_argument(
        "--clear-all",
        default=False,
        action="store_true",
        help="clear all existing data",
    )
    parser.add_argument(
        "--clear-traces",
        default=False,
        action="store_true",
        help="clear existing traces",
    )
    parser.add_argument(
        "--clear-cores",
        default=False,
        action="store_true",
        help="clear existing cores",
    )
    parser.add_argument(
        "--clear-edits",
        default=False,
        action="store_true",
        help="clear existing edits",
    )
    parser.add_argument(
        "--clear-proofs",
        default=False,
        action="store_true",
        help="clear existing proofs",
    )
    parser.add_argument(
        "--overwrite-reports",
        default=False,
        action="store_true",
        help="overwrite the existing report(s)",
    )
    parser.add_argument(
        "--create-singleton",
        default=False,
        action="store_true",
        help="create singleton edit project",
    )
    parser.add_argument(
        "--analyze-singleton",
        default=False,
        action="store_true",
        help="analyze singleton edit project",
    )
    # parser.add_argument(
    #     "--eval-rankings",
    #     default=False,
    #     action="store_true",
    #     help="evaluate different rankings",
    # )
    parser.add_argument(
        "--print-status",
        default=False,
        action="store_true",
        help="print the current status",
    )
    parser.add_argument(
        "--reroll",
        default=False,
        action="store_true",
        help="(maybe) change the proof and trace",
    )
    parser.add_argument(
        "--clear-proof-cache",
        default=False,
        action="store_true",
        help="clear the proof analyzer CACHE",
    )
    parser.add_argument(
        "--collect-garbage",
        default=False,
        action="store_true",
        help="collect garbage",
    )
    args = parser.parse_args()

    dbg = Debugger3(
        args.input_query_path,
        retry_failed=args.retry_failed,
        clear_all=args.clear_all,
        clear_edits=args.clear_edits,
        clear_traces=args.clear_traces,
        clear_cores=args.clear_cores,
        clear_proofs=args.clear_proofs,
        clear_proof_cache=args.clear_proof_cache,
        skip_core=args.skip_core,
        overwrite_reports=args.overwrite_reports,
    )

    if args.print_status:
        dbg.print_status()
        return

    if args.create_singleton:
        dbg.create_singleton_project()
        return

    if args.analyze_singleton:
        dbg.analyze_singleton_project()
        return

    if args.reroll:
        dbg.set_proof()
        return

    if args.collect_garbage:
        dbg.collect_garbage()
        return

    dbg.print_status()

if __name__ == "__main__":
    main()
