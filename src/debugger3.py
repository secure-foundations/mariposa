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
from debugger.edit_manager import EditManager
from debugger.pool_utils import run_with_pool
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
        log_debug(f"[trace-fail] {mi.trace_path}, {rc}, {et}")
        return mi
    mi.discard = True
    log_debug(f"[trace-fail] discarded: {mi.trace_path}, {rc}, {et}")
    return None


def _build_any_trace(mi: MutantInfo):
    mi.build_trace()
    et = round(mi.trace_time / 1000, 2)
    log_debug(f"[trace-any] {mi.trace_path}, {mi.trace_rcode}, {et}")
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

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []

        self.__init_dirs(clear_all)
        self.__init_query_files(query_path, ids_available)
        self.__init_mutant_infos(clear_traces, clear_cores, clear_proofs)

        if len(self.traces) != 0 and len(self.proofs) == 0 and not retry_failed:
            log_warn(
                "[init] previous debugging attempt has failed, run with --retry-failed if needed!"
            )
            return

        self.__build_traces()
        self.__build_cores(skip_core)
        self.__build_proofs(skip_core)

        proof = self.proofs[0]
        trace = self.get_candidate_trace()

        log_info(f"[init] [edit] proof: {proof.proof_path}")
        log_info(f"[init] [edit] trace: {trace.trace_path} ({trace.trace_rcode}, {trace.trace_time})")
        assert trace.has_trace()
        proof = proof.get_proof_analyzer()
        self.editor = EditManager(self.name_hash, proof, trace, clear_edits=clear_edits)

    def __init_dirs(self, reset):
        if reset and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

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
        log_info(f"orig path: {self.orig_path}")
        table = []
        for v in self.traces:
            table.append([v.trace_path, v.trace_time, v.trace_rcode])
        log_info(f"listing {len(table)} traces:")
        print(tabulate(table, headers=["path", "time", "result"]))

        log_info(f"listing {len(self.cores)} cores:")
        for v in self.cores:
            print(v.core_path)

        table = []
        log_info(f"listing {len(self.proofs)} proofs:")

        for v in self.proofs:
            print(v.proof_path)


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
        dbg.editor.create_singleton_edit_project()
        return

    if args.analyze_singleton:
        dbg.editor.analyze_singleton_edit_project()
        return

    dbg.print_status()

if __name__ == "__main__":
    main()
