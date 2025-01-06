#!/usr/bin/env python3

import argparse
import json
import binascii, random
import pandas as pd
import os
from z3 import set_param
from tqdm import tqdm
from base.defs import DEBUG_ROOT
from base.solver import RCode
from debugger.pool_utils import run_with_pool

# from debugger.trace_analyzer import InstDiffer, shorten_qid
from debugger.edit_info import EditInfo, EditAction
# from query_editor import QueryEditor
from typing import Dict, List
from utils.query_utils import (
    Mutation,
    find_verus_procedure_name,
)
from utils.system_utils import (
    confirm_input,
    create_dir,
    get_name_hash,
    list_files_ext,
    log_check,
    log_info,
    log_warn,
    remove_dir,
    subprocess_run,
)
from tabulate import tabulate
from debugger.mutant_info import *


MUTANT_COUNT = 30

TRACE_TOTAL_TIME_LIMIT_SEC = 480
CORE_TOTAL_TIME_LIMIT_SEC = 120
PROOF_TOTAL_TIME_LIMIT_SEC = 120


def _build_fail_trace(mi: MutantInfo):
    mi.build_trace()
    et = round(mi.trace_time / 1000, 2)
    rc = mi.trace_rcode
    if rc != RCode.UNSAT or et > TRACE_TIME_LIMIT_SEC:
        log_info(f"[trace-fail] {mi.trace_path}, {rc}, {et}")
        return mi
    mi.discard = True
    log_warn(f"[trace-fail] discarded: {mi.trace_path}, {rc}, {et}")
    return None


def _build_any_trace(mi: MutantInfo):
    mi.build_trace()
    et = round(mi.trace_time / 1000, 2)
    log_info(f"[trace-any] {mi.trace_path}, {mi.trace_rcode}, {et}")
    return mi


def _build_core(mi: MutantInfo):
    if mi.build_core_query():
        log_info(f"[core]: {mi.core_path}")
        return mi
    log_warn(f"[core] failure: {mi.core_path}")
    return None


def _build_proof(mi: MutantInfo):
    if mi.build_proof():
        return mi
    return None


def _run_edit(ei: EditInfo):
    ei.run_query()
    return ei


class Debugger3:
    def __init__(
        self,
        query_path,
        retry_failed=False,
        clear_all=False,
        clear_edits=False,
        clear_traces=False,
        clear_cores=False,
        clear_proofs=False,
        skip_core=False,
        ids_available=False,
        overwrite_reports=False,
    ):
        if not os.path.exists(query_path):
            log_warn(f"[init] query path {query_path} not found")
            return

        self.name_hash = get_name_hash(query_path)
        self.base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.name_hash}"

        log_info(f"[init] analyzing {query_path} in {self.sub_root}")

        self.query_meta = f"{self.sub_root}/meta.json"
        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.lbl_path = f"{self.sub_root}/lbl.smt2"

        self.trace_dir = f"{self.sub_root}/{TRACES}"
        self.muts_dir = f"{self.sub_root}/{MUTANTS}"
        self.cores_dir = f"{self.sub_root}/{CORES}"
        self.proofs_dir = f"{self.sub_root}/proofs"
        self.meta_dir = f"{self.sub_root}/meta"
        self.edit_dir = f"{self.sub_root}/edits"

        # self.basic_report_path = f"{self.sub_root}/report.csv"

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []

        self.__edit_infos: Dict[int, EditInfo] = dict()

        # self.singleton_edit_project = "singleton_" + self.name_hash

        self.__init_dirs(clear_all)
        self.__init_query_files(query_path, ids_available)
        self.__init_mutant_infos(clear_traces, clear_cores, clear_proofs)
        self.__init_edits(clear_edits)

        if len(self.traces) != 0 and len(self.proofs) == 0 and not retry_failed:
            log_warn(
                "[init] previous debugging attempt has failed, run with --retry-failed if needed!"
            )
            return

        self.__build_traces()
        self.__build_cores(skip_core)
        self.__build_proofs(skip_core)

        # self.pis = [p.proof_info for p in self.proofs]
        # self.tmi = self.get_candidate_trace()

        # self.differ = InstDiffer(self.orig_path, self.pis[0], self.tmi)
        # self.editor = QueryEditor(self.orig_path, self.pis[0])
        # self.save_report(overwrite=overwrite_reports)
        # self.load_report()

    def __del__(self):
        infos = [ei.to_dict() for ei in self.__edit_infos.values()]
        json.dump(infos, open(self.edits_meta, "w+"))

    def __init_dirs(self, reset):
        if reset and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

        if reset:
            log_info(f"[init] removing singleton project {self.singleton_edit_project}")
            remove_dir("data/projs/" + self.singleton_edit_project)
            remove_dir("data/projs/" + self.singleton_edit_project + ".filtered")
            remove_dir("data/dbs/" + self.singleton_edit_project)
            remove_dir("data/dbs/" + self.singleton_edit_project + ".filtered")

        for dir in [
            self.sub_root,
            self.muts_dir,
            self.trace_dir,
            self.cores_dir,
            self.proofs_dir,
        ]:
            create_dir(dir)

    def __init_query_files(self, query_path, ids_available):
        if not os.path.exists(self.orig_path):
            if ids_available:
                subprocess_run(["cp", query_path, self.orig_path])
            else:
                subprocess_run(
                    [
                        MARIPOSA,
                        "--action=add-qids",
                        "-i",
                        query_path,
                        "-o",
                        self.orig_path,
                    ],
                    check=True,
                )
                log_check(
                    os.path.exists(self.orig_path), f"failed to create {self.orig_path}"
                )

        if not os.path.exists(self.lbl_path):
            subprocess_run(
                [
                    MARIPOSA,
                    "--action=label-core",
                    "-i",
                    self.orig_path,
                    "-o",
                    self.lbl_path,
                    "--reassign-ids",
                ],
                check=True,
            )
            log_check(
                os.path.exists(self.lbl_path), f"failed to create {self.lbl_path}"
            )

        if not os.path.exists(self.query_meta):
            verus_proc = find_verus_procedure_name(self.orig_path)
            json.dump(
                {
                    "given_query": query_path,
                    "verus_proc": verus_proc,
                    "sub_root": self.sub_root,
                },
                open(self.query_meta, "w+"),
            )
            log_info(f"[init] basic meta data written to {self.query_meta}")

    def __init_mutant_infos(self, clear_traces, clear_cores, clear_proofs):
        if not os.path.exists(self.meta_dir):
            os.makedirs(self.meta_dir)
            return

        for mut_meta in list_files_ext(self.meta_dir, ".json"):
            d = json.load(open(mut_meta, "r"))
            mi = MutantInfo.from_dict(d)

            if mi.has_trace():
                if clear_traces:
                    mi.discard = True
                else:
                    self.traces.append(mi)

            if mi.has_core():
                if clear_cores:
                    mi.discard = True
                else:
                    self.cores.append(mi)

            if mi.has_proof():
                if clear_proofs:
                    mi.discard = True
                else:
                    self.proofs.append(mi)

    def __init_edits(self, clear_edits):
        self.__edit_infos = dict()

        if clear_edits:
            return self.clear_edits()

        if not os.path.exists(self.edits_meta):
            return

        infos = json.load(open(self.edits_meta, "r"))

        for ei in infos:
            ei = EditInfo.from_dict(ei)
            self.__edit_infos[ei.get_id()] = ei

    def clear_edits(self):
        if os.path.exists(self.edit_dir):
            count = len(os.listdir(self.edit_dir))
            if count > 10:
                confirm_input(f"clear {count} edits?")
            os.system(f"rm {self.edit_dir}/*")

        self.__edit_infos = dict()
        log_info("[edit] cleared")

    def __create_tasks(self, mutations: List[Mutation]):
        args = []

        for m in mutations:
            for _ in range(MUTANT_COUNT):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                args.append(MutantInfo(self.sub_root, m, s))

        random.shuffle(args)
        return args

    def __build_traces(self):
        count = len(self.traces)

        if count >= TRACE_GOAL_COUNT:
            return

        log_info(f"[init] currently {count} traces")

        for f in [_build_any_trace, _build_fail_trace]:
            args = self.__create_tasks(
                [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]
            )

            mis = run_with_pool(
                f, args, goal=TRACE_GOAL_COUNT, time_bound=TRACE_TOTAL_TIME_LIMIT_SEC
            )
            self.traces += mis

    def __build_cores(self, skip_core):
        count = len(self.cores)

        if count >= CORE_GOAL_COUNT or skip_core:
            return

        log_info(f"[init] currently {count} cores")

        goal = CORE_GOAL_COUNT - count

        args = self.__create_tasks([Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED])

        res = run_with_pool(
            _build_core, args, goal=goal, time_bound=CORE_TOTAL_TIME_LIMIT_SEC
        )

        self.cores += res

    def __build_proofs(self, skip_core):
        count = len(self.proofs)

        if count >= PROOF_GOAL_COUNT:
            return

        log_info(f"[init] currently {count} proofs")

        goal = PROOF_GOAL_COUNT - count
        res = []

        if len(self.cores) != 0 and not skip_core:
            skip = set([(mi.mutation, mi.seed) for mi in self.proofs])
            args = [mi for mi in self.cores if (mi.mutation, mi.seed) not in skip]
            log_info(
                f"[proof] from core (!) skipping {len(self.cores) - len(args)} cores"
            )
            res = run_with_pool(
                _build_proof,
                args,
                goal=goal,
                time_bound=PROOF_TOTAL_TIME_LIMIT_SEC,
            )

        log_info(f"[proof] from core (!) yields {len(res)} proofs")

        if len(res) < goal:
            log_info(f"[proof] from scratch, currently {len(res)} proofs")
            args = self.__create_tasks([Mutation.SHUFFLE, Mutation.RESEED])
            res += run_with_pool(
                _build_proof, args, goal=goal, time_bound=PROOF_TOTAL_TIME_LIMIT_SEC
            )

        log_check(len(res) != 0, "no proof found")
        self.proofs += res

    def get_fast_unknown_trace(self):
        uk_mis = [mi for mi in self.traces if mi.trace_rcode == RCode.UNKNOWN]
        if len(uk_mis) == 0:
            return None
        return min(uk_mis, key=lambda tmi: tmi.trace_time)

    def get_large_trace(self):
        for tmi in self.traces:
            if tmi.get_trace_size() > 1000000:
                return tmi
        return None

    def get_slow_trace(self):
        tomis = [
            tmi for tmi in self.traces if tmi.trace_time >= TRACE_TIME_LIMIT_SEC * 1000
        ]
        if len(tomis) == 0:
            return None
        return max(tomis, key=lambda tmi: tmi.trace_time)

    def get_candidate_trace(self):
        r = self.get_slow_trace()

        if r is not None:
            return r

        r = self.get_fast_unknown_trace()

        if r is not None:
            return r

        random.seed(43)
        return random.choice(self.traces)

    def print_status(self):
        table = []
        for v in self.traces:
            table.append([v.mutation, v.seed, v.trace_time, v.trace_rcode])
        log_info(f"listing {len(table)} trace mutants:")
        print(tabulate(table, headers=["mutation", "seed", "time", "result"]))

        table = []
        for v in self.cores:
            table.append([v.mutation, v.seed])
        log_info(f"listing {len(table)} core mutants:")
        print(tabulate(table, headers=["mutation", "seed"]))

        table = []
        for v in self.proofs:
            table.append([v.mutation, v.seed])
        log_info(f"listing {len(table)} proof mutants:")
        print(tabulate(table, headers=["mutation", "seed"]))

        log_info(f"orig path: {self.orig_path}")

        # log_info("report path: ")
        # log_info(self.report_path)

    def _save_edit(self, ei: EditInfo):
        assert isinstance(ei, EditInfo)
        self.editor.do_edits(ei.edit)
        self.editor.save(ei.path)

    def test_edit(self, edit):
        ei = self.register_edit_info(edit)
        if ei.has_data():
            # log_warn("[edit] specified edit already exists")
            return ei
        if not ei.query_exists():
            self._save_edit(ei)
        ei.run_query()
        self.__edit_infos[ei.get_id()] = ei
        return ei

    def test_edit_with_id(self, edit_id) -> EditInfo:
        assert edit_id in self.__edit_infos
        ei = self.__edit_infos[edit_id]
        if not ei.query_exists():
            self._save_edit(ei)
        if not ei.has_data():
            ei.run_query()
        return ei

    def get_edit_path(self, edit):
        return f"{self.edit_dir}/{edit.get_id()}.smt2"

    def register_edit_info(self, edit):
        if isinstance(edit, set):
            edit = {qid: self.differ.actions[qid] for qid in edit}
        else:
            assert isinstance(edit, dict)
        ei = EditInfo("", edit)
        path = self.get_edit_path(ei)
        ei.path = path
        eid = ei.get_id()

        if eid in self.__edit_infos:
            return self.__edit_infos[eid]
        else:
            self.__edit_infos[eid] = ei

        return ei

    def look_up_edit(self, edit):
        res = []

        for ei in self.__edit_infos:
            if set(ei.edit.keys()) & edit.keys() != set():
                res.append(ei)

        return res

    def try_aggressive_edit(self):
        valid = dict()
        for qid, action in self.differ.actions.items():
            if action == EditAction.ERASE:
                valid[qid] = action
        self.test_edit(valid)

    def _try_edits(self, targets, run_query):
        args = []

        for edit in tqdm(targets):
            ei = self.register_edit_info(edit)
            if ei.has_data():
                continue
            if not ei.query_exists():
                self._save_edit(ei)
            args.append(ei)

        if not run_query:
            log_info(f"[edit] skipped running, queries saved in {self.edit_dir}")
            return

        run_res = run_with_pool(_run_edit, args)

        for ei in run_res:
            assert ei.has_data()
            self.__edit_infos[ei.get_id()] = ei

    def try_random_edits(self, size=1):
        NUM_TRIES = 30
        edits = []

        for _ in range(NUM_TRIES):
            edit = set(random.sample(self.differ.actions.keys(), size))
            edits.append({qid: self.differ.actions[qid] for qid in edit})

        self._try_edits(edits, run_query=True)

    def try_less_random_edits(self, size=2):
        NUM_TRIES = 30
        edits = []

        for _ in range(NUM_TRIES):
            edit = set(random.sample(self.differ.actions.keys(), size))
            if all(self.differ.actions[qid] != EditAction.INSTANTIATE for qid in edit):
                continue
            edits.append({qid: self.differ.actions[qid] for qid in edit})

        self._try_edits(edits, run_query=True)

    # def register_singleton_edits(self):
    #     for qid in self.differ.actions:
    #         self.register_edit_info({qid})
    #     log_info(f"[edit] {len(self.__edit_infos)} edits registered")

    # def create_singleton_edit_project(self):
    #     name = self.singleton_edit_project
    #     qids = self.differ.actions.keys()
    #     self._try_edits([{qid} for qid in qids], run_query=False)

    #     assert os.path.exists(self.edit_dir)
    #     log_info(f"[proj] edit dir: {self.edit_dir} {len(qids)} files")

    #     if os.path.exists(f"data/projs/{name}"):
    #         log_info(f"[proj] {name} already exists")
    #     else:
    #         os.system(
    #             f"./src/proj_wizard.py create -i {self.edit_dir} --new-project-name {name}"
    #         )
    #         os.system(
    #             f"./src/exper_wizard.py manager -e verify --total-parts 30 -s z3_4_13_0 -i data/projs/{name}/base.z3"
    #         )

    #     filtered_dir = f"data/projs/{name}.filtered/base.z3"

    #     if os.path.exists(filtered_dir):
    #         log_info(f"[proj] {name}.filtered already exists")
    #     else:
    #         os.system(
    #             f"./src/analysis_wizard.py filter_edits -e verify -s z3_4_13_0 -i data/projs/{name}/base.z3"
    #         )
    #         if len(os.listdir(filtered_dir)) == 0:
    #             return log_warn(f"[proj] {name} has no filtered queries")
    #         os.system(
    #             f"./src/exper_wizard.py manager -e default --total-parts 30 -s z3_4_13_0 -i {filtered_dir}"
    #         )

    # def analyze_singleton_project(self):
    #     name = self.singleton_edit_project
    #     filtered_dir = f"data/projs/{name}.filtered/base.z3"
    #     edit_ids = []

    #     if not os.path.exists(filtered_dir):
    #         log_warn(f"[proj] {name} has no filtered queries")
    #         return edit_ids

    #     for config in ["default", "verus_quick"]:
    #         stdout, stderr, _ = subprocess_run(
    #             [
    #                 "./src/analysis_wizard.py",
    #                 "stable",
    #                 "-e",
    #                 config,
    #                 "-s",
    #                 "z3_4_13_0",
    #                 "-i",
    #                 filtered_dir,
    #             ],
    #             debug=True,
    #         )

    #         # TODO: this is a hacky... I should have used the same exp config...
    #         if stderr:
    #             log_warn("skip due to encountered: " + stderr)
    #             continue

    #         for line in stdout.split("\n"):
    #             if line.startswith("edit_id:"):
    #                 edit_id = line.split(": ")[1].strip()
    #                 edit_ids.append(edit_id)

    #         return edit_ids

    # def evaluate_rankings(self):
    #     valid_edit_count = 0

    #     table = []

    #     versions = ["v0", "v1", "v2", "v3", "v4", "v5"]
    #     scores = [0] * 12

    #     eids = self.analyze_singleton_project()
    #     self.register_singleton_edits()

    #     for eid in eids:
    #         ei = self.test_edit_with_id(eid)
    #         qid, action = ei.get_singleton_edit()

    #         if qid == "prelude_fuel_defaults":
    #             continue

    #         ranks = self.get_rankings(qid)
    #         valid_edit_count += 1

    #         # self.differ.debug_quantifier(qid)

    #         for i in range(6):
    #             if ranks[i] < 10:
    #                 scores[2 * i] += 1
    #                 scores[2 * i + 1] = 1

    #         table += [[shorten_qid(qid), ei.get_id(), action.value, ei.time] + ranks]

    #     log_info(
    #         f"found {valid_edit_count} stabilizing edits (excluding prelude_fuel_defaults)"
    #     )

    #     print(
    #         tabulate(
    #             table,
    #             headers=[
    #                 "qid",
    #                 "eid",
    #                 "action",
    #                 "time",
    #                 *versions,
    #             ],
    #         )
    #     )

    #     return [valid_edit_count] + scores


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
        "--eval-rankings",
        default=False,
        action="store_true",
        help="evaluate different rankings",
    )
    parser.add_argument(
        "--print-status",
        default=False,
        action="store_true",
        help="print the current status",
    )

    args = parser.parse_args()

    dbg = Debugger3(
        args.input_query_path,
        clear_all=args.clear_all,
        clear_edits=args.clear_edits,
        clear_traces=args.clear_traces,
        clear_cores=args.clear_cores,
        clear_proofs=args.clear_proofs,
        retry_failed=args.retry_failed,
        skip_core=args.skip_core,
        overwrite_reports=args.overwrite_reports,
    )

    if args.create_singleton:
        dbg.create_singleton_edit_project()
        return

    if args.eval_rankings:
        dbg.evaluate_rankings()
        return

    dbg.print_status()

if __name__ == "__main__":
    main()
