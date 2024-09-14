import binascii, random
import sqlite3
from base.solver import RCode
from utils.database_utils import get_cursor, table_exists, conclude
import multiprocessing
import os, sys
from typing import Dict, List
from base.defs import DEBUG_ROOT, MARIPOSA
from base.solver import output_as_rcode
from utils.query_utils import Mutation, emit_mutant_query, parse_trace
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from tabulate import tabulate
from query.instantiater import Instantiater

TRACE_TIME_LIMIT_SEC = 10
MUTANT_COUNT = 10
PROC_COUNT = 4
QID_TABLE_LIMIT = 30

TRACES = "traces"
MUTANTS = "mutants"


class MutantInfo:
    def __init__(self, sub_root, mutation, seed):
        self.seed = seed
        self.orig_path = f"{sub_root}/orig.smt2"
        self.mutation = mutation
        self.mut_path = f"{sub_root}/{MUTANTS}/{mutation}.{seed}.smt2"
        self.trace_path = f"{sub_root}/{TRACES}/{mutation}.{seed}"

        self.trace_rcode = -1
        self.trace_time = -1
        self.proof_time = -1

    def create_mutant(self):
        if os.path.exists(self.mut_path):
            return

        emit_mutant_query(self.orig_path, self.mut_path, self.mutation, self.seed)

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


def _build_trace(mi: MutantInfo):
    res = mi.build_trace()
    log_info(f"[built-trace] {mi.trace_path}, {res[0]}, {res[1]}")
    return res


def _build_proof(mi: MutantInfo):
    mi.create_mutant()
    ins = Instantiater(mi.mut_path)

    if ins.process():
        log_info(f"[build-inst] success {mi.mut_path}")
        return (mi.mutation, mi.seed, ins.proof_time)

    log_warn(f"[build-inst] failed {mi.mut_path}")
    return None


def create_mut_table(cur):
    cur.execute(
        f"""CREATE TABLE mutants (
        mutation varchar(10),
        seed varchar(20),
        trace_rcode INTEGER DEFAULT -1,
        trace_time INTEGER DEFAULT -1,
        proof_time INTEGER DEFAULT -1,
        PRIMARY KEY (mutation, seed))"""
    )


class Debugger3:
    def __init__(self, query_path, clear):
        base_name = os.path.basename(query_path)
        self.sub_root = f"{DEBUG_ROOT}{base_name}"

        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.trace_dir = f"{self.sub_root}/{TRACES}"
        self.mutant_dir = f"{self.sub_root}/{MUTANTS}"
        self.db_path = f"{self.sub_root}/db.sqlite"

        if clear and os.path.exists(self.sub_root):
            os.system(f"rm -rf {self.sub_root}")

        for dir in [self.sub_root, self.trace_dir, self.mutant_dir]:
            if not os.path.exists(dir):
                os.makedirs(dir)

        if not os.path.exists(self.orig_path):
            os.system(f"cp {query_path} {self.orig_path}")

        self.con = sqlite3.connect(self.db_path, timeout=10)

        self.traces: List[MutantInfo] = []
        self.proofs: List[MutantInfo] = []

        self.__init_traces()
        self.__init_proofs()
        self.__load_mutants()

    def create_mutants(self, mutations: List[Mutation]):
        args = []

        for m in mutations:
            for _ in range(MUTANT_COUNT):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                args.append(MutantInfo(self.sub_root, m, s))

        random.shuffle(args)
        return args

    def __init_traces(self):
        cur = self.con.cursor()

        if not table_exists(cur, "mutants"):
            create_mut_table(cur)
            self.con.commit()

        cur.execute("SELECT COUNT(*) FROM mutants WHERE trace_rcode != -1")
        count = cur.fetchall()[0][0]
        cur.close()

        if count > 0:
            return

        args = self.create_mutants([Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED])
        pool = multiprocessing.Pool(PROC_COUNT)
        res = pool.map(_build_trace, args)
        pool.close()

        cur = self.con.cursor()
        for i, r in enumerate(res):
            cur.execute(
                f"""INSERT INTO mutants (mutation, seed, trace_rcode, trace_time)
                VALUES (?, ?, ?, ?)""",
                (args[i].mutation, str(args[i].seed), r[0].value, r[1]),
            )
        self.con.commit()

    def __load_mutants(self):
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
                self.proofs.append(mi)

    def __init_proofs(self):
        cur = self.con.cursor()
        cur.execute("SELECT COUNT(*) FROM mutants WHERE proof_time != -1")
        count = cur.fetchall()[0][0]
        cur.close()

        if count > 0:
            return

        args = self.create_mutants([Mutation.SHUFFLE, Mutation.RESEED])

        res = []
        pool = multiprocessing.Pool(PROC_COUNT)

        while len(args) > 0:
            batch, args = args[:PROC_COUNT], args[PROC_COUNT:]
            res = pool.map(_build_proof, batch)
            res = [r for r in res if r is not None]
            if len(res) > 0:
                break
        pool.close()

        log_check(len(res) != 0, "no proof found")

        for r in res:
            cur = self.con.cursor()
            cur.execute(
                "INSERT INTO mutants (mutation, seed, proof_time) VALUES (?, ?, ?)", (r[0], str(r[1]), r[2])
            )
        self.con.commit()

    def debug_trace(self, pmi: MutantInfo):
        ins = Instantiater(pmi.mut_path)
        ins.process()
        proof = ins.inst_freq
        ins.output("out.smt2")

        for v in self.traces:
            if v.trace_rcode == RCode.UNSAT:
                continue

            table = []
            explored = v.get_qids()

            for qid in explored:
                table += [(qid, explored[qid], proof[qid] if qid in proof else 0)]

            print(tabulate(table, headers=["QID", "Trace Count", "Proof Count"]))
            break

    def print_mutants(self):
        table = []
        print("trace mutants")
        for v in self.traces:
            table.append([v.mutation, v.seed, v.trace_time, v.trace_rcode])
        log_info(f"listing {len(table)} trace mutants:")
        print(tabulate(table, headers=["mutation", "seed", "time", "result"]))

        table = []
        for v in self.proofs:
            table.append([v.mutation, v.seed, v.proof_time])
        log_info(f"listing {len(table)} proof mutants:")
        print(tabulate(table, headers=["mutation", "seed", "time"]))

if __name__ == "__main__":
    debugger = Debugger3(sys.argv[1], False)
    debugger.print_mutants()
    proof = debugger.proofs[0]
    debugger.debug_trace(proof)
