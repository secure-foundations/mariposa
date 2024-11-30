#!/usr/bin/env python3

import argparse
import json
import binascii, random
import sqlite3
import time
from z3 import set_param
from base.defs import DEBUG_ROOT
from base.solver import RCode
from debugger.trace_analyzer import InstDiffer
from debugger.edit_info import EditInfo, EditAction
from query_editor import QueryEditor
from utils.database_utils import table_exists
import multiprocessing
import os, sys
from typing import Dict, List
from utils.query_utils import (
    Mutation,
    find_verus_procedure_name,
)
from utils.system_utils import (
    confirm_input,
    log_check,
    log_info,
    log_warn,
    subprocess_run,
)
from tabulate import tabulate
from debugger.mutant_info import *


PROC_COUNT = 4
MUTANT_COUNT = 8

TRACE_TOTAL_TIME_LIMIT_SEC = 480
CORE_TOTAL_TIME_LIMIT_SEC = 120
PROOF_TOTAL_TIME_LIMIT_SEC = 120


def _build_fail_trace(mi: MutantInfo):
    res = mi.build_trace()
    if res[0] == RCode.UNSAT and res[1] < TRACE_TIME_LIMIT_SEC * 1000:
        log_info(f"[trace-fail] ignored: {mi.trace_path}, {res[0]}, {res[1]}")
        return None
    log_info(f"[trace-fail] {mi.trace_path}, {res[0]}, {res[1]}")
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
    def __init__(
        self,
        query_path,
        reset=False,
        clear_edits=False,
        proof_from_core=True,
        ids_available=False,
        overwrite_reports=False,
    ):
        self.base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{self.base_name}"
        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.lbl_path = f"{self.sub_root}/lbl.smt2"
        self.trace_dir = f"{self.sub_root}/{TRACES}"
        self.muts_dir = f"{self.sub_root}/{MUTANTS}"
        self.insts_dir = f"{self.sub_root}/{INSTS}"
        self.cores_dir = f"{self.sub_root}/{CORES}"
        self.edit_dir = f"{self.sub_root}/edits"
        self.graph_dir = f"{self.sub_root}/graphs"
        self.edits_meta = f"{self.sub_root}/edits.json"

        self.db_path = f"{self.sub_root}/db.sqlite"
        self.__edit_infos: Dict[int, EditInfo] = dict()
        self.__build_proof_from_core = proof_from_core

        self.__init_dirs(query_path, reset, ids_available)

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []
        self.cores: List[MutantInfo] = []

        self.__init_db()
        self.__init_traces()
        self.__init_cores()
        self.refresh_status()
        self.__init_proofs()
        self.__init_edits(clear_edits)
        self.refresh_status()

        self.pis = [p.proof_info for p in self.proofs]

        self.tmi = self.get_candidate_trace()

        self.differ = InstDiffer(self.orig_path, self.pis[0], self.tmi)
        self.editor = QueryEditor(self.orig_path, self.pis[0])
        self.save_report(overwrite=overwrite_reports)

    def __del__(self):
        infos = [ei.to_dict() for ei in self.__edit_infos.values()]
        json.dump(infos, open(self.edits_meta, "w+"))

    def __init_dirs(self, query_path, reset, ids_available):
        if reset and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

        for dir in [
            self.sub_root,
            self.trace_dir,
            self.muts_dir,
            self.insts_dir,
            self.cores_dir,
            self.edit_dir,
        ]:
            if not os.path.exists(dir):
                os.makedirs(dir)

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

    def __init_db(self):
        self.con = sqlite3.connect(self.db_path, timeout=10)
        cur = self.con.cursor()

        if not table_exists(cur, "mutants"):
            create_mut_table(cur)
            self.con.commit()
        else:
            self.refresh_status()

    def clear_edits(self):
        if os.path.exists(self.edit_dir):
            count = len(os.listdir(self.edit_dir))
            if count > 10:
                confirm_input(f"clear {count} edits?")
            os.system(f"rm {self.edit_dir}/*")

        self.__edit_infos = dict()
        log_info("[edit] cleared")

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

        if count >= TRACE_GOAL_COUNT:
            return

        log_info(f"[init] currently {count} traces")

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
                print(f"inserted {args[i].mutation} {args[i].seed}", r[0], r[1])
            self.con.commit()

    def __init_cores(self):
        count = len(self.cores)

        if count >= CORE_GOAL_COUNT or not self.__build_proof_from_core:
            return

        log_info(f"[init] currently {count} cores")

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

        if count >= PROOF_GOAL_COUNT:
            return

        log_info(f"[init] currently {count} proofs")

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

    def __init_edits(self, clear_edits):
        if clear_edits:
            return self.clear_edits()

        if not os.path.exists(self.edits_meta):
            return
        
        infos = json.load(open(self.edits_meta, "r"))
        self.__edit_infos = dict()

        for ei in infos:
            ei = EditInfo.from_dict(ei)
            self.__edit_infos[ei.get_id()] = ei

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

        return max(self.traces, key=lambda tmi: tmi.get_trace_size())

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

        log_info("orig path: ")
        log_info(self.orig_path)

        log_info("report path: ")

        for i in range(1, 3):
            log_info(self.get_report_path(i))

    def get_report_path(self, version=1):
        # the version is not the same as the edit version
        return f"{self.sub_root}/report_v{version}.txt"

    def save_report(self, overwrite=False):
        report_path = self.get_report_path()
        if os.path.exists(report_path) and not overwrite:
            log_warn(f"[report] already exists: {report_path}")
            return

        report = self.differ.get_report()
        verus_proc = find_verus_procedure_name(self.orig_path)

        with open(report_path, "w+") as f:
            f.write("base name:\n")
            f.write(self.base_name + "\n\n")
            f.write("query path:\n")
            f.write(self.orig_path + "\n\n")
            f.write("trace path:\n")
            f.write(self.tmi.trace_path + "\n\n")
            f.write(f"{self.tmi.trace_time} {self.tmi.trace_rcode}\n\n")
            f.write("verus procedure:\n")
            f.write(verus_proc + "\n\n")
            f.write(report)

        log_info(f"[report] written: {report_path}")

    def _save_edit(self, ei: EditInfo):
        assert isinstance(ei, EditInfo)
        self.editor.do_edits(ei.edit)
        self.editor.save(ei.path)

    def test_edit(self, edit):
        ei = self.init_edit_info(edit)
        if ei.has_data():
            log_warn("[edit] specified edit already exists")
            return ei
        ei = EditInfo(ei.path, edit)
        ei.run_query()
        self.__edit_infos[ei.get_id()] = ei
        return ei

    def test_edit_with_id(self, edit_id) -> EditInfo:
        path = f"{self.edit_dir}/{edit_id}.smt2"
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

    def _try_edits(self, targets, create_query, run_query):
        args, edits = [], dict()

        for edit in targets:
            ei = self.init_edit_info(edit, create_query)

            if ei.has_data():
                log_warn("[edit] specified edit already exists")
                continue

            if not ei.query_exists():
                if not create_query:
                    log_warn("[edit] not creating query")
                    continue
                self._save_edit(ei)

            args.append(ei.path)
            # this is a bit redundant, but it's fine
            self.__edit_infos[ei.get_id()] = ei

        if not run_query:
            log_info(f"[edit] skipped running, queries saved in {self.edit_dir}")
            return

        time_bound = int((10 * len(edits) + 1) / PROC_COUNT)
        run_res = self.__run_with_pool(_run_query, args, time_bound=time_bound)

        for path, r, e, t in run_res:
            ei = EditInfo(path, edits[path], r, e, t)
            self.__edit_infos[ei.get_id()] = ei

    def try_random_edits(self, size=1):
        NUM_TRIES = 30
        edits = []

        for _ in range(NUM_TRIES):
            edit = set(random.sample(self.differ.actions.keys(), size))
            edits.append({qid: self.differ.actions[qid] for qid in edit})

        self._try_edits(edits, create_query=True, run_query=True)

    def try_less_random_edits(self, size=2):
        NUM_TRIES = 30
        edits = []

        for _ in range(NUM_TRIES):
            edit = set(random.sample(self.differ.actions.keys(), size))
            if all(self.differ.actions[qid] != EditAction.INSTANTIATE for qid in edit):
                continue
            edits.append({qid: self.differ.actions[qid] for qid in edit})

        self._try_edits(edits, create_query=True, run_query=True)

    def register_single_edits(self):
        for qid in self.differ.actions:
            self.register_edit_info({qid})
        log_info(f"[edit] {len(self.__edit_infos)} edits registered")

    def make_single_edits_project(self):
        name = self.make_project("single_edits")

        print(f"./src/exper_wizard.py data-sync -i data/projs/{name}/base.z3 --clear")
        print(
            f"./src/exper_wizard.py manager -e verus_verify --total-parts 10 -s z3_4_13_0 --clear-existing -i data/projs/{name}/base.z3"
        )
        print(
            f"./src/analysis_wizard.py veri-verus -e verus_verify -s z3_4_13_0 -i data/projs/{name}/base.z3"
        )
        print(
            f"./src/exper_wizard.py data-sync -i data/projs/{name}_filtered/base.z3 --clear"
        )
        print(
            f"./src/exper_wizard.py manager -e verus_quick --total-parts 10 -s z3_4_13_0 --clear-existing -i data/projs/{name}_filtered/base.z3"
        )
        print(
            f"./src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i data/projs/{name}_filtered/base.z3"
        )

    def get_project_name(self, suffix):
        prefix = self.base_name.replace("-", "_").replace(".", "_")
        return f"{prefix}_{suffix}"

    def make_project(self, suffix):
        name = self.get_project_name(suffix)

        if os.path.exists(f"data/projs/{name}"):
            log_warn(f"[proj] {name} already exists")
            return name

        subprocess_run(
            [
                "./src/proj_wizard.py",
                "create",
                "-i",
                self.edit_dir,
                "--new-project-name",
                name,
            ],
            check=True,
            debug=True,
        )
        return name

    def get_passing_edits(self):
        passed = [ei for ei in self.__edit_infos if ei.std_out == RCode.UNSAT]
        return sorted(passed, key=lambda ei: ei.time)

def main():
    set_param(proof=True)

    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "--proof-from-core",
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
    parser.add_argument(
        "--overwrite-reports",
        default=False,
        action="store_true",
        help="overwrite the existing report(s)",
    )
    # parser.add_argument("--version", default=1, help="")

    args = parser.parse_args()

    dbg = Debugger3(
        args.input_query_path,
        # clear=args.clear,
        proof_from_core=args.proof_from_core,
        overwrite_reports=args.overwrite_reports,
    )
    
    # g = dbg.differ.graph2
    # ranked = g.estimate_all_costs(g.estimate_cost_v1)
    # for qid in ranked:
    #     print(qid, ranked[qid])

    # dbg.register_single_edits()
    # dbg.make_single_edits_project()


if __name__ == "__main__":
    main()
