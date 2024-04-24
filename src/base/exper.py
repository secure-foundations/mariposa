import os, random
import numpy as np

from typing import Dict
from base.defs import MAGIC_IGNORE_SEED
from utils.query_utils import Mutation, find_verus_procedure_name

from utils.system_utils import *
from utils.database_utils import *
from base.solver import Solver, RCode, EXPECTED_CODES
# from base.factory import FACT
from base.project import Project, Partition, get_qid
from base.defs import delegate

class QueryExpResult:
    def __init__(self, query_path, mutations=[], blob=None):
        self.qid = get_qid(query_path)
        self.query_path = query_path
        self.mutations = mutations

        if blob is not None:
            assert blob.shape[0] == len(mutations)
            assert blob.shape[1] == 2

        self.timeout = None
        self.blob = blob

    def is_dummy(self):
        return self.blob is None

    def __str__(self):
        return f"query: {self.query_path}"
    
    def __hash__(self):
        return hash(self.query_path)

    def get_mutation_blob(self, mutation):
        index = self.mutations.index(mutation)
        return self.blob[index]
    
    def get_mutation_status(self, mutation):
        # print(self.mutations)
        index = self.mutations.index(mutation)
        return self.blob[index][0], self.blob[index][1]

    def get_original_status(self):
        return self.blob[0][0][0], self.blob[0][1][0]

    def enforce_timeout(self, timeout):
        assert timeout > 1000
        if np.isinf(timeout):
            return
        new_blobs = np.copy(self.blob)
        for index in range(len(self.mutations)):
            old_blob = self.blob[index]
            new_blob = new_blobs[index]
            new_blob[0][old_blob[1] > timeout] = RCode.TIMEOUT.value
            new_blob[1][old_blob[1] > timeout] = timeout
        self.blob = new_blobs
        self.timeout = timeout

    def print_status(self, verbosity=0):
        from tabulate import tabulate

        if verbosity == 0:
            return

        # v_rcode, v_time = self.get_original_status()
        # print(f"plain result: {RCode(v_rcode)} {v_time / 1000}s")

        if self.timeout != None:
            print(f"alternative timeout: {self.timeout/1000}s")


        table = [["mutation"] + [str(rc) for rc in EXPECTED_CODES] 
                 + ["mean", "std"]]
        for m in self.mutations:
            trow = [m]
            rcodes, times = self.get_mutation_status(m)
            rcs = {rc: 0 for rc in EXPECTED_CODES}

            for rc in rcodes:
                rc = RCode(rc)
                if rc not in EXPECTED_CODES:
                    log_warn(f"unexpected rcode '{rc}' in {self.query_path}")
                    rc = RCode.UNKNOWN
                rcs[rc] += 1
            for rc in EXPECTED_CODES:
                trow.append(rcs[rc])

            times = times / 1000
            trow.append(round(np.mean(times), 2))
            trow.append(round(np.std(times), 2))
            table.append(trow)
        print(tabulate(table, headers="firstrow"))
        print("")

    # def get_fast_pass(self):
    #     if self.blob is None:
    #         return False
    #     rc, et = self.get_original_status()
    #     if et < 1000 and rc == RCode.UNSAT.value:
    #         return True
    #     return False

def get_table_prefix(proj, solver, part=None):
    if part is None:
        part = proj.part
    if part.is_whole():
        return scrub(f"{proj.full_name}_{str(solver)}")
    return scrub(f"{proj.full_name}_{str(solver)}_{part}")

def get_table_names(proj, solver, part=None):
    prefix = get_table_prefix(proj, solver, part)
    return f"{prefix}_exp", f"{prefix}_sum"

class ExpTask:
    """represents a single task, 
    which is a single query with a single mutation"""
    def __init__(self, v_path, g_path, perturb, mut_seed):
        self.origin_path = v_path
        self.perturb = perturb
        self.mut_seed = mut_seed
        self.mutant_path = g_path
        self.quake = False

class ExpConfig:
    def __init__(self, name, obj):
        self.exp_name = name
        # what mutations do we use?
        self.enabled_muts = obj["mutations"]

        # how many mutants to generate
        self.num_mutant = obj["num_mutants"]

        # how many processes do we use?
        self.num_procs = obj["num_procs"]

        # do we keep the mutants after running?
        self.keep_mutants = obj["keep_mutants"]

        # how long do we wait? (seconds)
        self.timeout = obj["exp_timeout"]
    
    def as_dict(self):
        return {"mutations": self.enabled_muts,
                "num_mutants": self.num_mutant,
                "num_procs": self.num_procs,
                "keep_mutants": self.keep_mutants,
                "exp_timeout": self.timeout}

@delegate('proj', 'get_path', 'list_queries', 'get_log_dir')
class Experiment(ExpConfig):
    """
    an experiment is a collection of tasks
    defined by (a project, a solver, an experiment config)
    the project.part may not be whole
    """
    def __init__(self, proj: Project, cfg: ExpConfig, solver: Solver):
        # this is a bit of a hack
        super().__init__(cfg.exp_name, cfg.as_dict())

        self.proj: Project = proj
        self.solver: Solver = solver

        self.table_prefix = get_table_prefix(proj, solver)
        self.exp_table_name, self.sum_table_name = get_table_names(proj, solver)
        self.gen_dir = proj.get_gen_dir(self.exp_name)
        self.db_path = proj.get_db_path(self.exp_name)

        if not os.path.exists(self.db_path):
            os.makedirs(os.path.dirname(self.db_path), exist_ok=True)

        # this just clears the gen dir
        reset_dir(self.gen_dir, True)
        
        self.retry_count = 0

    def signature(self):
        return f"{self.proj.full_name}_{self.proj.part}_{self.solver}_{self.exp_name}"

    def print_info(self):
        print(f"project dir:\t{self.proj.sub_root}")
        print(f"exper config:\t{self.exp_name}")
        print(f"solver path:\t{self.solver.path}")

    def create_db(self, clear):

        con, cur = get_cursor(self.db_path)

        for table_name in [self.exp_table_name, self.sum_table_name]:
            if table_exists(cur, table_name):
                if clear:
                    log_info(f"{table_name} already exists, removing")
                else:
                    confirm_input(f"{table_name} already exists, remove it?")
                cur.execute(f"""DROP TABLE {table_name}""")

        create_exp_table(cur, self.exp_table_name)
        create_sum_table(cur, self.sum_table_name)
        conclude(con)

    def create_query_tasks(self, origin_path):
        base = get_qid(origin_path)
        base.replace(".smt2", "")

        task = ExpTask(origin_path, origin_path, None, 0)
        tasks = [task]

        for m in self.enabled_muts:
            if m == Mutation.QUAKE:
                mutant_path = f"{self.gen_dir}/{base}.quake.smt2"
                qtask = ExpTask(origin_path, mutant_path, Mutation.QUAKE, None)
                qtask.quake = True
                tasks.append(qtask)
                continue

            for _ in range(self.num_mutant):
                s = random.randint(0, 0xffffffffffffffff)
                mut_path = f"{self.gen_dir}/{base}.{str(s)}.{m}.smt2"
                task = ExpTask(origin_path, mut_path, m, s)
                tasks.append(task)
        # log_info(f"created {len(tasks)} tasks for {origin_path}")
        return tasks

    @staticmethod
    def parse_mutant_path(mutant_path):
        parts = os.path.basename(mutant_path).split(".")
        if parts[-1] != "smt2":
            log_check(parts[-3] == "quake", "unexpected mutant path")
            return Mutation(parts[-3]), int(parts[-1])
        try:
            return Mutation(parts[-2]), int(parts[-3])
        except ValueError:
            return Mutation.NONE, MAGIC_IGNORE_SEED

    # this is called by the runner
    # should not call this for analysis
    def create_tasks(self, clear):
        self.create_db(clear)
        tasks = []
        origin_paths = self.list_queries()
        log_info(f"running {len(origin_paths)} original queries")

        for origin_path in origin_paths:
            tasks.extend(self.create_query_tasks(origin_path))

        if not self.proj.is_whole():
            log_debug(f"running ONLY {self.proj.part} in {self.proj.full_name}")
        else:
            log_debug(f"running ALL of {self.proj.full_name}")

        log_debug(f"adding {len(tasks)} tasks")
        return tasks

    def insert_exp_row(self, task, mutant_path, rcode, elapsed):
        try:
            con, cur = get_cursor(self.db_path)
            cur.execute(f"""INSERT INTO {self.exp_table_name}
                (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
                VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
                (mutant_path, task.origin_path, task.perturb, str(task.mut_seed), "", "", rcode, elapsed))
            conclude(con)
        except sqlite3.OperationalError:
            log_error(f"failed to insert {mutant_path} into {self.exp_table_name}, retrying")
            time.sleep(1)
            self.insert_exp_row(task, mutant_path, rcode, elapsed)
            self.retry_count += 1

        if self.retry_count > 10:
            log_error(f"failed to insert {mutant_path} into {self.exp_table_name}, giving up")
            sys.exit(1)

    def insert_sum_row(self, cur, v_path, v_rcode, v_time):
        mutations = self.enabled_muts

        blob = np.zeros((len(mutations), 2, self.num_mutant + 1), dtype=int)

        blob[:, 0, 0] = v_rcode
        blob[:, 1, 0] = v_time
        
        for (i, m) in enumerate(mutations):
            rows = get_mutant_rows(cur, self.exp_table_name, v_path, m)

            if len(rows) < self.num_mutant:
                log_warn(f"{v_path} {m} has {len(rows)} mutants, expected {self.num_mutant}")
                log_info(f"filling with {self.num_mutant - len(rows)} rcode '{RCode.ERROR}'")
                blob[i][0] = RCode.ERROR.value
            else:
                log_check(len(rows) == self.num_mutant, f"{v_path} {m} has {len(rows)} mutants, expected {self.num_mutant}")

            for (j, row) in enumerate(rows):
                blob[i][0][j + 1] = row[0]
                blob[i][1][j + 1] = row[1]

        cur.execute(f"""INSERT INTO {self.sum_table_name}
        VALUES(?, ?);""", (v_path, blob))

    def populate_sum_table(self):
        con, cur = get_cursor(self.db_path)

        vanilla_rows = get_vanilla_paths(cur, self.exp_table_name)

        cur.execute(f"""DROP TABLE IF EXISTS {self.sum_table_name}""")
        create_sum_table(cur, self.sum_table_name)

        processed = set()

        for (v_path, v_rcode, v_time) in vanilla_rows:
            if v_path in processed:
                continue
            processed.add(v_path)
            self.insert_sum_row(cur, v_path, v_rcode, v_time)
        conclude(con)

        log_info("done post processing exp data")

    def is_done(self):
        # print(self.db_path, self.sum_table_name)
        if not os.path.exists(self.db_path):
            return False
        con, cur = get_cursor(self.db_path)
        res = table_exists(cur, self.sum_table_name)
        con.close()
        return res

    def load_sum_table(self) -> Dict[str, QueryExpResult]:
        con, cur = get_cursor(self.db_path)
        sum_name = self.sum_table_name
        summaries = dict()

        if not table_exists(cur, sum_name):
            con.close()
            return summaries

        res = cur.execute(f"""SELECT * FROM {sum_name}""")
        rows = res.fetchall()
        con.close()

        mut_size = self.num_mutant

        for row in rows:
            blob = np.frombuffer(row[1], dtype=int)
            blob = blob.reshape((len(self.enabled_muts), 2, mut_size + 1))
            path = self.get_path(get_qid(row[0]))
            qr = QueryExpResult(path, self.enabled_muts, blob)
            qr.enforce_timeout(self.timeout * 1000)
            summaries[qr.qid] = qr

        return summaries

    def get_missing_qids(self):
        expected = set([get_qid(q) for q in self.list_queries()])
        con, cur = get_cursor(self.db_path)
        res = cur.execute(f"""SELECT vanilla_path FROM {self.sum_table_name}""")
        rows = res.fetchall()
        con.close()
        existing = set([get_qid(r[0]) for r in rows])
        missing = expected - existing
        log_info(f"missing {len(missing)} experiments in {self.sum_table_name}")
        return missing

    # def _sanity_check_summary(self, expected, actual):
    #     missing = actual - expected

    #     if missing != set():
    #         log_warn(f"{len(missing)} queries files are missing in {self.sum_table_name}")

    #     missing = expected - actual

    #     if missing != set():
    #         log_error(f"{len(missing)} experiments are missing in {self.sum_table_name}")
    #         for i, q in enumerate(missing):
    #             if i <= 10:
    #                 print(f"missing: {q}.smt2")
    #             else:
    #                 break
    #         if len(missing) > 10:
    #             exit_with(f"eliding {len(missing) - 10} more")
    #         sys.exit(1)

    def import_partition_tables(self, other_db_path, part):
        log_check(self.proj.is_whole(), "importing into a partial project does not make sense")
        con, cur = get_cursor(self.db_path)

        assert table_exists(cur, self.exp_table_name)
        assert table_exists(cur, self.sum_table_name)

        cur.execute(f'ATTACH "{other_db_path}" as OTHER_DB;')
        other_exp_tname, other_sum_tname = get_table_names(self.proj, self.solver, part)
        cur.execute(f"INSERT INTO {self.exp_table_name} SELECT * FROM OTHER_DB.{other_exp_tname}")
        cur.execute(f"INSERT INTO {self.sum_table_name} SELECT * FROM OTHER_DB.{other_sum_tname}")
        conclude(con)

    def probe_other_db(self, other_db_path):
        log_check(self.proj.is_whole(), "importing to a partial project does not make sense")
        tables = get_tables(other_db_path)
        exps, sums = set(), set()

        for table in tables:
            if table.startswith(self.table_prefix):
                part = table[len(self.table_prefix)+1:-4]
                part = Partition.from_str(part)
                if table.endswith("_exp"):
                    exps.add(part)
                else: 
                    assert table.endswith("_sum")
                    sums.add(part)
        return exps

    def get_mutants(self, v_path):
        con, cur = get_cursor(self.db_path)
        res = cur.execute(f"""SELECT query_path, result_code, elapsed_milli FROM {self.exp_table_name} WHERE vanilla_path = ?""", (v_path,))
        rows = res.fetchall()
        con.close()
        return rows

