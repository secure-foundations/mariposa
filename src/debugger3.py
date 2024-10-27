#!/usr/bin/env python3

import argparse
import binascii, random
import sqlite3
import pickle
import subprocess
import time
from z3 import set_param
from base.solver import RCode
from query_editor import BasicQueryWriter, QueryEditor
from debugger.trace_analyzer import TraceAnalyzer
from proof_builder import ProofInfo, ProofBuilder
from utils.database_utils import table_exists
import multiprocessing
import os, sys
from typing import Dict, List
from base.defs import DEBUG_ROOT, MARIPOSA
from base.solver import output_as_rcode
from utils.query_utils import (
    Mutation,
    emit_mutant_query,
    find_verus_procedure_name,
    parse_trace,
)
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from tabulate import tabulate

PROC_COUNT = 4
MUTANT_COUNT = 8

TRACE_TIME_LIMIT_SEC = 10
CORE_TIME_LIMIT_SEC = 60

TRACE_TOTAL_TIME_LIMIT_SEC = 120
CORE_TOTAL_TIME_LIMIT_SEC = 120
PROOF_TOTAL_TIME_LIMIT_SEC = 120

TRACE_GOAL_COUNT = 4
PROOF_GOAL_COUNT = 2
CORE_GOAL_COUNT = 2

TRACES = "traces"
MUTANTS = "mutants"
INSTS = "insts"
CORES = "cores"

TEMP = "temp"

class MutantInfo:
    def __init__(self, sub_root, mutation, seed):
        self.seed = seed
        self.orig_path = f"{sub_root}/orig.smt2"
        self.lbl_path = f"{sub_root}/lbl.smt2"
        self.mutation = mutation
        self.mut_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.smt2"
        self.trace_path = f"{sub_root}/{TRACES}/{mutation}.{seed}"
        self.insts_path = f"{sub_root}/{INSTS}/{mutation}.{seed}"
        self.core_path = f"{sub_root}/{CORES}/{mutation}.{seed}.smt2"
        self.core_log = f"{sub_root}/{CORES}/{mutation}.{seed}.log"

        self.trace_rcode = -1
        self.trace_time = -1
        self.proof_time = -1

    def __hash__(self) -> int:
        return hash((self.mutation, self.seed))

    def create_mutant(self, source=None):
        if source is None:
            source = self.orig_path

        if os.path.exists(self.mut_path):
            return

        emit_mutant_query(source, self.mut_path, self.mutation, self.seed)

    def build_trace(self):
        self.create_mutant()

        solver_args = [
            "./bin/z3-4.13.0",
            f"-t:{TRACE_TIME_LIMIT_SEC*1000}",
            self.mut_path,
            "trace=true",
            f"trace_file_name={self.trace_path}",
        ]

        stdout, stderr, elapsed = subprocess_run(solver_args, check=True, debug=False)
        res = output_as_rcode(stdout)
        return (res, elapsed)

    def get_qids(self):
        return parse_trace(self.orig_path, self.trace_path)

    def load_insts(self):
        with open(self.insts_path, "rb") as f:
            self.proof_info: ProofInfo = pickle.load(f)

    def build_core(self):
        self.create_mutant(self.lbl_path)

        with open(self.mut_path, "a") as f:
            f.write("(get-unsat-core)\n")

        log_info(f"[core] attempt {self.mut_path}")

        cf = open(self.core_log, "w+")
        subprocess.run(
            [
                "./bin/z3-4.13.0",
                self.mut_path,
                f"-t:{CORE_TIME_LIMIT_SEC*1000}",
            ],
            stdout=cf,
        )
        cf.close()
        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()

        if len(lines) == 0 or "unsat\n" not in lines:
            return None

        args = [
            MARIPOSA,
            "-i",
            self.lbl_path,
            "--action=reduce-core",
            f"--core-log-path={self.core_log}",
            f"-o",
            self.core_path,
        ]

        # if self.keep_quantified:
        #     args.append("--core-keep-quantified")

        subprocess_run(args, check=True, debug=True)

        log_check(
            os.path.exists(self.core_path),
            f"failed to create core query {self.core_path}",
        )

        return True


def _build_fail_trace(mi: MutantInfo):
    res = mi.build_trace()
    log_info(f"[trace-fail] {mi.trace_path}, {res[0]}, {res[1]}")
    if res[0] == RCode.UNSAT:
        return None
    return res


def _build_any_trace(mi: MutantInfo):
    res = mi.build_trace()
    log_info(f"[trace-any] {mi.trace_path}, {res[0]}, {res[1]}")
    return res


def _build_core(mi: MutantInfo):
    res = mi.build_core()
    if res:
        log_info(f"[core] success {mi.core_path}")
    else:
        log_warn(f"[core] failure {mi.core_path}")
    return res


def _build_proof(mi: MutantInfo):
    target = mi.mut_path
    if os.path.exists(mi.core_path):
        log_info(f"[proof] from core (!) {mi.core_path}")
        target = mi.core_path
    else:
        mi.create_mutant()

    log_info(f"[proof] attempt {target}")
    pr = ProofBuilder(target)
    pi = pr.try_prove()

    if pi is not None:
        pi.save(mi.insts_path)
        log_info(f"[proof] success {target}")
        return (mi.mutation, mi.seed, pr.proof_time)

    log_warn(f"[proof] failure {mi.mut_path}")
    return None


def create_mut_table(cur):
    cur.execute(
        f"""CREATE TABLE mutants (
        mutation varchar(10),
        seed varchar(20),
        trace_rcode INTEGER DEFAULT -1,
        trace_time INTEGER DEFAULT -1,
        proof_time INTEGER DEFAULT -1,
        from_core BOOLEAN DEFAULT FALSE,
        PRIMARY KEY (mutation, seed))"""
    )


class Debugger3:
    def __init__(self, query_path, clear, from_core):
        self.base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.base_name}"
        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.lbl_path = f"{self.sub_root}/lbl.smt2"
        self.trace_dir = f"{self.sub_root}/{TRACES}"
        self.muts_dir = f"{self.sub_root}/{MUTANTS}"
        self.insts_dir = f"{self.sub_root}/{INSTS}"
        self.cores_dir = f"{self.sub_root}/{CORES}"
        self.db_path = f"{self.sub_root}/db.sqlite"
        self.__build_proof_from_core = from_core

        self.__init_dirs(query_path, clear)

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []

        log_info(f"[init] {self.orig_path}")

        self.__init_db()
        self.__init_traces()
        self.__init_cores()
        self.refresh_status()
        self.__init_proofs()
        self.refresh_status()

        pins = [p.proof_info for p in self.proofs]
        self.analyzer = TraceAnalyzer(self.orig_path, pins)

    def __init_dirs(self, query_path, clear):
        if clear and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

        for dir in [
            self.sub_root,
            self.trace_dir,
            self.muts_dir,
            self.insts_dir,
            self.cores_dir,
        ]:
            if not os.path.exists(dir):
                os.makedirs(dir)

        if not os.path.exists(self.orig_path):
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

    def __init_db(self):
        self.con = sqlite3.connect(self.db_path, timeout=10)
        cur = self.con.cursor()

        if not table_exists(cur, "mutants"):
            create_mut_table(cur)
            self.con.commit()
        else:
            self.refresh_status()

    def create_mutants_info(self, mutations: List[Mutation]):
        args = []

        for m in mutations:
            for _ in range(MUTANT_COUNT):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                args.append(MutantInfo(self.sub_root, m, s))

        random.shuffle(args)
        return args

    def __run_with_pool(self, func, args, goal=0, time_bound=600):
        success = []
        start_time = time.time()

        pool = multiprocessing.Pool(PROC_COUNT)

        if goal <= 0 or goal > len(args):
            goal = len(args)

        while True:
            if len(success) >= goal:
                log_info(f"[pool] goal reached, {len(success)} successes")
                break

            if len(args) == 0:
                log_info(f"[pool] no more args")
                break

            res = pool.map(func, args[:PROC_COUNT])
            args = args[PROC_COUNT:]
            success += [r for r in res if r is not None]

            time_elapsed = int(time.time() - start_time)

            log_info(
                f"[pool] {len(success)} successes, {time_elapsed}(s) elapsed, {len(args)} jobs left"
            )

            if time_elapsed >= time_bound:
                log_info(f"[pool] time budget exceeded: {time_elapsed}")
                break

        pool.close()
        return success

    def __init_traces(self):
        count = len(self.traces)

        if count > 0:
            log_info(f"[init] currently {count} traces")
            return

        for f in [_build_any_trace, _build_fail_trace]:
            args = self.create_mutants_info(
                [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]
            )

            res = self.__run_with_pool(
                f, args, goal=TRACE_GOAL_COUNT, time_bound=TRACE_TOTAL_TIME_LIMIT_SEC
            )
            cur = self.con.cursor()
            for i, r in enumerate(res):
                cur.execute(
                    f"""INSERT INTO mutants (mutation, seed, trace_rcode, trace_time)
                    VALUES (?, ?, ?, ?)""",
                    (args[i].mutation, str(args[i].seed), r[0].value, r[1]),
                )
            self.con.commit()

    def __init_cores(self):
        count = len(self.cores)

        log_info(f"[init] currently {count} cores")

        if count >= CORE_GOAL_COUNT:
            return

        goal = CORE_GOAL_COUNT - count

        args = self.create_mutants_info(
            [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]
        )

        res = self.__run_with_pool(
            _build_core, args, goal=goal, time_bound=CORE_TOTAL_TIME_LIMIT_SEC
        )
        log_check(len(res) != 0, "no core built")

    def __init_proofs(self):
        count = len(self.proofs)

        log_info(f"[init] currently {count} proofs")

        if count >= PROOF_GOAL_COUNT:
            return

        goal = PROOF_GOAL_COUNT - count
        res = []

        if len(self.cores) != 0 and self.__build_proof_from_core:
            skip = set([(mi.mutation, mi.seed) for mi in self.proofs])
            args = [mi for mi in self.cores if (mi.mutation, mi.seed) not in skip]
            log_info(
                f"[proof] from core (!) skipping {len(self.cores) - len(args)} cores"
            )

            res = self.__run_with_pool(
                _build_proof,
                args,
                goal=goal,
                time_bound=PROOF_TOTAL_TIME_LIMIT_SEC,
            )
        else:
            args = self.create_mutants_info([Mutation.SHUFFLE, Mutation.RESEED])
            res = self.__run_with_pool(
                _build_proof, args, goal=goal, time_bound=PROOF_TOTAL_TIME_LIMIT_SEC
            )
            log_check(len(res) != 0, "no proof found")

        cur = self.con.cursor()

        for r in res:
            cur.execute(
                "INSERT INTO mutants (mutation, seed, proof_time) VALUES (?, ?, ?)",
                (r[0], str(r[1]), r[2]),
            )
        self.con.commit()

    def refresh_status(self):
        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []

        cur = self.con.cursor()
        cur.execute("SELECT * FROM mutants")
        mutants = cur.fetchall()
        cur.close()

        for r in mutants:
            if r[2] != -1:
                mi = MutantInfo(self.sub_root, r[0], int(r[1]))
                mi.trace_rcode = RCode(r[2])
                mi.trace_time = r[3]
                self.traces.append(mi)
            elif r[4] != -1:
                mi = MutantInfo(self.sub_root, r[0], int(r[1]))
                mi.proof_time = r[4]
                mi.load_insts()
                self.proofs.append(mi)

        for file in os.listdir(self.cores_dir):
            if file.endswith(".smt2"):
                mi = MutantInfo(
                    self.sub_root, file.split(".")[0], int(file.split(".")[1])
                )
                self.cores.append(mi)

    def get_candidate_trace(self):
        for tmi in self.traces:
            if tmi.trace_rcode != RCode.UNSAT and tmi.trace_time < 200:
                return tmi

        tomis = [
            tmi for tmi in self.traces if tmi.trace_time >= TRACE_TIME_LIMIT_SEC * 1000
        ]

        if len(tomis) >= 1:
            return random.choice(tomis)

        return max(self.traces, key=lambda tmi: tmi.trace_time)

    def get_proof_inst_counts(self, qids):
        result = dict()
        for qid in qids:
            counts = []
            for pmi in self.proofs:
                count = pmi.proof_info.get_inst_count(qid)
                counts.append(count)
            result[qid] = counts
        return result

    def get_proof_total_inst_counts(self):
        return self.analyzer.get_proof_total_inst_counts()

    def debug_trace(self, report_file=None, table_limit=None, tmi: MutantInfo=None):
        if tmi is None:
            tmi = self.get_candidate_trace()

        traced = tmi.get_qids()
        report = self.analyzer.get_report(traced, table_limit)

        verus_proc = find_verus_procedure_name(self.orig_path)
        # verus_proc = "unknown"

        if report_file is not None:
            with open(report_file, "w+") as f:
                f.write("base name:\n")
                f.write(self.base_name + "\n\n")
                f.write("query path:\n")
                f.write(self.orig_path + "\n\n")
                f.write("trace path:\n")
                f.write(tmi.trace_path + "\n\n")
                f.write(f"{tmi.trace_time} {tmi.trace_rcode}\n\n")
                f.write("verus procedure:\n")
                f.write(verus_proc + "\n\n")
                f.write(report)
        else:
            print(report)

    def select_suppress_qids(self, tmi: MutantInfo, version):
        log_info(f"debugging trace {tmi.mut_path} {tmi.trace_time} {tmi.trace_rcode}")
        traced = tmi.get_qids()
        if version == 1:
            return self.analyzer.select_qids_v1(traced, 5)
        elif version == 2:
            return self.analyzer.select_qids_v2(traced, 5)
        assert False

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
            table.append([v.mutation, v.seed, v.proof_time])
        log_info(f"listing {len(table)} proof mutants:")
        print(tabulate(table, headers=["mutation", "seed", "time"]))

    def get_editor(self) -> QueryEditor:
        log_check(len(self.proofs) != 0, "no proofs")
        return QueryEditor(self.orig_path, self.proofs[0].proof_info)

def make_iteration_dir(input_query_path):
    base_name = os.path.basename(input_query_path)
    assert base_name.endswith(".smt2")
    base_name = base_name[:-5]
    temp_dir = f"{TEMP}/{base_name}."
    if os.path.exists(TEMP):
        os.system(f"rm {temp_dir}*")
    os.system(f"mkdir {TEMP}")
    return temp_dir

if __name__ == "__main__":
    set_param(proof=True)

    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "-o", "--output-query-path", required=False, help="the output query path"
    )
    parser.add_argument(
        "-r", "--report-path", required=False, help="the output report path"
    )
    parser.add_argument(
        "--from-core",
        default=False,
        action="store_true",
        help="build proofs from cores",
    )
    parser.add_argument(
        "--clear",
        default=False,
        action="store_true",
        help="clear the existing experiment",
    )
    parser.add_argument("--version", default=1, help="suppressor version")

    args = parser.parse_args()
    dbg = Debugger3(args.input_query_path, args.clear, args.from_core)

    if args.report_path is not None:
        dbg.debug_trace(args.report_path)

    # if args.output_query_path is None:
    #     sys.exit(0)

    version = int(args.version)
    
