import json
import binascii, random
import pandas as pd
import os
from base.defs import DEBUG_ROOT
from base.solver import RCode
from debugger.debugger_options import DebugOptions
from debugger.pool_utils import run_with_pool
from typing import Dict, List
from utils.query_utils import (
    Mutation,
    add_qids_to_query,
)
from utils.system_utils import (
    create_dir,
    get_name_hash,
    list_files,
    list_files_ext,
    list_smt2_files,
    log_check,
    log_info,
    log_warn,
    subprocess_run,
)
from tabulate import tabulate
from debugger.mutant_info import *


def _build_fail_trace(mi: MutantInfo):
    mi.build_trace()
    et = round(mi.trace_time / 1000, 2)
    rc = mi.trace_rcode
    if rc != RCode.UNSAT or et > mi.options.per_trace_time_sec:
        log_debug(f"[trace-fail] {mi.trace_path}, {rc}, {et}")
        mi.save()
        return mi
    mi.clear()
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


class MutantBuilder:
    def __init__(
        self,
        query_path,
        options: DebugOptions,
    ):
        self.given_query_path = query_path
        self.name_hash = get_name_hash(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.name_hash}"

        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.lbl_path = f"{self.sub_root}/lbl.smt2"

        self.trace_dir = f"{self.sub_root}/{TRACES}"
        self.muts_dir = f"{self.sub_root}/{MUTANTS}"
        self.cores_dir = f"{self.sub_root}/{CORES}"
        self.proofs_dir = f"{self.sub_root}/proofs"
        self.meta_dir = f"{self.sub_root}/meta"

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []
        self.options: DebugOptions = options

        self.__init_dirs()
        self.__init_query_files(query_path)
        self.__init_mutant_infos()

        if not options.build_proof:
            return

        if (
            (len(self.traces) != 0 or len(self.cores) != 0)
            and len(self.proofs) == 0
            and not options.retry_failed
        ):
            log_warn(
                "[init] previous debugging attempt has failed, run with --retry-failed if needed!"
            )
            return

        self.build_all()

    def build_all(self):
        self.build_traces()
        self.build_cores()
        self.build_proofs()

    def __init_dirs(self):
        for dir in [
            self.muts_dir,
            self.trace_dir,
            self.cores_dir,
            self.proofs_dir,
        ]:
            create_dir(dir)

    def collect_garbage(self, keep_only_target=None):
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

        if list_smt2_files(self.muts_dir) != []:
            os.system(f"rm {self.muts_dir}/*")

    def __init_query_files(self, query_path):
        if not os.path.exists(self.orig_path):
            if self.options.ids_available:
                subprocess_run(["cp", query_path, self.orig_path])
            else:
                add_qids_to_query(query_path, self.orig_path)
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

    def __init_mutant_infos(self):
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
            mi = MutantInfo.from_dict(d, self.options)

            if mi.has_trace():
                self.traces.append(mi)
            if mi.has_core():
                self.cores.append(mi)
            if mi.has_proof():
                self.proofs.append(mi)

    def clear_mutants(self, clear_traces, clear_cores, clear_proofs):
        if clear_traces:
            for mi in self.traces:
                mi.clear()

        if clear_cores:
            for mi in self.cores:
                mi.clear()

        if clear_proofs:
            for mi in self.proofs:
                mi.clear()

    def __create_tasks(self, mutations: List[Mutation]):
        args = []

        for m in mutations:
            for _ in range(self.options.mutant_count):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                args.append(MutantInfo(self.sub_root, m, s, self.options))

        random.shuffle(args)
        return args

    def build_traces(self):
        count = len(self.traces)

        if count >= self.options.trace_target_count:
            return

        log_info(f"[init] currently {count} traces")

        args = self.__create_tasks(
            [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]
        )

        # so that we have at least one trace
        _build_any_trace(args[0])

        mis = run_with_pool(
            _build_fail_trace,
            args[1:],
            goal=self.options.trace_target_count - count,
            time_bound=self.options.total_trace_time_sec,
        )
        self.traces += mis

    def build_cores(self):
        count = len(self.cores)

        if (
            (count >= self.options.core_target_count)
            or self.options.skip_core
            or (len(self.proofs) >= self.options.proof_goal_count)
        ):
            return

        log_info(f"[init] currently {count} cores")

        goal = self.options.core_target_count - count

        args = self.__create_tasks([Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED])

        res = run_with_pool(
            _build_core, args, goal=goal, time_bound=self.options.total_core_time_sec
        )

        self.cores += res

    def build_proofs(self):
        count = len(self.proofs)

        if count >= self.options.proof_goal_count:
            return

        log_info(f"[init] currently {count} proofs")

        goal = self.options.proof_goal_count - count
        res = []

        if len(self.cores) != 0 and not self.options.skip_core:
            skip = set([(mi.mutation, mi.seed) for mi in self.proofs])
            args = [mi for mi in self.cores if (mi.mutation, mi.seed) not in skip]
            log_info(
                f"[proof] from core (!) skipping {len(self.cores) - len(args)} cores"
            )
            res = run_with_pool(
                _build_proof,
                args,
                goal=goal,
                time_bound=self.options.total_proof_time_sec,
            )

        log_info(f"[proof] from core (!) yields {len(res)} proofs")

        if len(res) < goal:
            log_info(f"[proof] from scratch, currently {len(res)} proofs")
            args = self.__create_tasks([Mutation.SHUFFLE, Mutation.RESEED])
            res += run_with_pool(
                _build_proof, args, goal=goal, time_bound=self.options.total_proof_time_sec
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
            tmi for tmi in self.traces if tmi.trace_time >= self.options.per_trace_time_sec * 1000
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
        if self.traces == []:
            return None
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

    def get_trace_mutant_info(self, trace_path) -> MutantInfo:
        for mi in self.traces:
            if mi.trace_path == trace_path:
                return mi
        return None
