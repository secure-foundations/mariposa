import json
import binascii, random
import pandas as pd
import os
from tqdm import tqdm
from base.solver import RCode
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
    list_files,
    list_files_ext,
    list_smt2_files,
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
        mi.save()
        return mi
    log_debug(f"[trace-fail] discarded: {mi.trace_path}, {rc}, {et}")
    return None


def _build_any_trace(mi: MutantInfo):
    mi.build_trace()
    et = round(mi.trace_time / 1000, 2)
    log_debug(f"[trace-any] {mi.trace_path}, {mi.trace_rcode}, {et}")
    mi.save()
    return mi


def _build_core(mi: MutantInfo):
    if mi.build_core_query():
        log_info(f"[core]: {mi.core_path}")
        mi.save()
        return mi
    log_warn(f"[core] failure: {mi.core_path}")
    return None


def _build_proof(mi: MutantInfo):
    if mi.build_proof():
        mi.save()
        return mi
    return None


class FileBuilder:
    def __init__(
        self,
        query_path,
        sub_root,
        ids_available=False,
        retry_failed=False,
        clear_traces=False,
        clear_cores=False,
        clear_proofs=False,
        skip_core=False,
    ):
        # log_info(f"analyzing {query_path} in {self.sub_root}")
        self.sub_root = sub_root
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

        self.__init_dirs()
        self.__init_query_files(query_path, ids_available)
        self.__init_mutant_infos(clear_traces, clear_cores, clear_proofs)

        if (
            (len(self.traces) != 0 or len(self.cores) != 0)
            and len(self.proofs) == 0
            and not retry_failed
        ):
            log_warn(
                "[init] previous debugging attempt has failed, run with --retry-failed if needed!"
            )
            return

        self.__build_traces()
        self.__build_cores(skip_core)
        self.__build_proofs(skip_core)

    def __init_dirs(self):
        for dir in [
            self.muts_dir,
            self.trace_dir,
            self.cores_dir,
            self.proofs_dir,
        ]:
            create_dir(dir)

    def collect_garbage(self, keep_only_target=None):
        print(keep_only_target)
        for trace_file in list_files(self.trace_dir):
            if trace_file == keep_only_target:
                continue
    
            found, should_remove = False, False
            if keep_only_target is not None:
                should_remove = True

            for mi in self.traces:
                if mi.trace_path == trace_file:
                    found = True
                    break

            if not found or should_remove:
                log_info(f"[garbage] removing {trace_file}")
                os.remove(trace_file)

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

    def __init_mutant_infos(self, clear_traces, clear_cores, clear_proofs):
        if not os.path.exists(self.meta_dir):
            os.makedirs(self.meta_dir)
            return

        for mut_meta in list_files_ext(self.meta_dir, ".json"):
            try:
                d = json.load(open(mut_meta, "r"))
            except:
                os.system(f"rm {mut_meta}")
                log_warn(f"[init] failed to load {mut_meta}")
                continue
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

        if count >= CORE_GOAL_COUNT or skip_core or len(self.proofs) >= PROOF_GOAL_COUNT:
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
        if r := self.get_slow_trace():
            return r

        if r := self.get_fast_unknown_trace():
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

    def get_trace_mutant_info(self, trace_path):
        for mi in self.traces:
            if mi.trace_path == trace_path:
                return mi
        return None
