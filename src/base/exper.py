import os, random
import numpy as np

from typing import Dict
from enum import Enum
from utils.query_utils import find_verus_procedure_name

from utils.system_utils import *
from utils.database_utils import *
from base.solver import Solver, RCode, EXPECTED_CODES
# from base.factory import FACT
from base.project import Project, Partition
from base.defs import EXPER_CONFIG_PATH

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    RESEED = "reseed"
    QUAKE = "quake"
    COMPOSE = "compose"

    def __str__(self):
        return str.__str__(self)

class QueryExpResult:
    def __init__(self, query_path, proj_root, mutations=[], blob=None):
        self.base_name = os.path.basename(query_path)
        self.query_path = os.path.join(proj_root, self.base_name)
        self.mutations = mutations

        if blob is not None:        
            assert blob.shape[0] == len(mutations)
            assert blob.shape[1] == 2

        self.timeout = None
        self.blob = blob

    def __str__(self):
        return f"query: {self.query_path}"
    
    def __hash__(self):
        return hash(self.query_path)

    def get_mutation_blob(self, mutation):
        index = self.mutations.index(mutation)
        return self.blob[index]

    def is_dummy(self):
        return self.blob is None
    
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

    def print_status(self, verbosity=1):
        from tabulate import tabulate
        log_info(f"command to copy query")
        print(f"cp '{self.query_path}' temp/woot.smt2")

        v_rcode, v_time = self.get_original_status()
        proc = find_verus_procedure_name(self.query_path)

        if proc != None:
            log_info(f"procedure name: {proc}")

        if self.timeout != None:
            log_info(f"alternative timeout: {self.timeout/1000}s")

        if verbosity <= 1:
            return

        table = [["mutation"] + [str(rc) for rc in EXPECTED_CODES] 
                 + ["mean", "std"]]
        print(f"plain query {RCode(v_rcode)} in {v_time / 1000}s")

        for m in self.mutations:
            trow = [m]
            rcodes, times = self.get_mutation_status(m)
            rcs = {rc: 0 for rc in EXPECTED_CODES}

            for rc in rcodes:
                rc = RCode(rc)
                if rc not in EXPECTED_CODES:
                    print(f"[WARN] unexpected rcode '{rc}' in {self.query_path}")
                rcs[rc] += 1
            for rc in EXPECTED_CODES:
                trow.append(rcs[rc])

            times = times / 1000
            trow.append(round(np.mean(times), 2))
            trow.append(round(np.std(times), 2))
            table.append(trow)

        print(tabulate(table, headers="firstrow"))

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

class Experiment(ExpConfig):
    """
    an experiment is a collection of tasks
    defined by (a project, a solver, an experiment config)
    the project.part may not be whole
    """
    def __init__(self, cfg: ExpConfig, proj: Project, solver: Solver):
        # this is a bit of a hack
        super().__init__(cfg.exp_name, cfg.as_dict())

        self.proj: Project = proj
        self.solver: Solver = solver
        self.is_whole = proj.is_whole()

        self.table_prefix = get_table_prefix(proj, solver)
        self.exp_table_name, self.sum_table_name = get_table_names(proj, solver)
        self.gen_dir = os.path.join(proj.get_gen_dir(), self.exp_name)
        self.db_path = os.path.join(proj.get_db_dir(), f"{self.exp_name}.db")

        # this won't reset the db
        create_dir(self.proj.get_db_dir())
        # this just clears the gen dir
        reset_dir(self.gen_dir, True)

    def signature(self):
        return f"{self.proj.full_name}_{self.proj.part}_{self.solver}_{self.exp_name}"

    def debug(self):
        return f"""project: {self.proj.full_name}
part: {self.part}
experiment: {self.exp_name}
db_path: {self.db_path}
sub_root: {self.proj.sub_root}
solver: {self.solver}"""

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

    def __build_query_tasks(self, origin_path):
        base = os.path.basename(origin_path)
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

        return tasks

    def __build_tasks(self):
        tasks = []
        origin_paths = self.proj.list_queries()
        log_info(f"running {len(origin_paths)} original queries")

        for origin_path in origin_paths:
            tasks.extend(self.__build_query_tasks(origin_path))

        if not self.proj.is_whole():
            log_info(f"running ONLY {self.proj.part} in {self.proj.full_name}")
        else:
            log_info(f"running ALL of {self.proj.full_name}")

        log_info(f"adding {len(tasks)} tasks")
        return tasks

    # this is called by the runner
    # should not call this for analysis
    def create_tasks(self, clear):
        self.create_db(clear)
        return self.__build_tasks()

    def insert_exp_row(self, task, mutant_path, rcode, elapsed):
        con, cur = get_cursor(self.db_path)

        cur.execute(f"""INSERT INTO {self.exp_table_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (mutant_path, task.origin_path, task.perturb, str(task.mut_seed), "", "", rcode, elapsed))
        conclude(con)

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

    def sum_table_exists(self):
        # print(self.db_path, self.sum_table_name)
        if not os.path.exists(self.db_path):
            return False
        con, cur = get_cursor(self.db_path)
        res = table_exists(cur, self.sum_table_name)
        con.close()
        return res

    def load_sum_table(self, enable_dummy=False) -> Dict[str, QueryExpResult]:
        con, cur = get_cursor(self.db_path)
        sum_name = self.sum_table_name
        summaries = dict()

        if not table_exists(cur, sum_name):
            log_check(enable_dummy, f"[ERROR] {sum_name} does not exist in {self.db_path}")
            print(f"[WARN] {sum_name} does not exist, creating dummy data!")
            for path in self.proj.list_queries():
                qr = QueryExpResult(path, self.proj.sub_root)
                if qr.mutations == []:
                    qr.mutations = self.enabled_muts
                summaries[qr.base_name] = qr
            return summaries

        res = cur.execute(f"""SELECT * FROM {sum_name}""")
        rows = res.fetchall()
        con.close()

        mut_size = self.num_mutant

        for row in rows:
            blob = np.frombuffer(row[1], dtype=int)
            if blob.shape == (488,):
                assert False
            else:
                blob = blob.reshape((len(self.enabled_muts), 2, mut_size + 1))

            path = row[0]
            qr = QueryExpResult(path, self.proj.sub_root, self.enabled_muts, blob)
            if qr.mutations == []:
                qr.mutations = self.enabled_muts
            summaries[qr.base_name] = qr

        self._sanity_check_summary(set(summaries.keys()))

        return summaries

    def _sanity_check_summary(self, actual):
        expected = set([os.path.basename(q) for q in self.proj.list_queries()])
        missing = actual - expected
        if missing != set():
            log_warn(f"{len(missing)} queries files are missing in {self.sum_table_name}")
            # for q in missing:
            #     print(f"[WARN] missing: {q}")

        missing = expected - actual
        if missing != set():
            print(f"[ERROR] experiments are missing in {self.sum_table_name}:")
            for q in missing:
                print(f"[ERROR] missing: {q}")
            print(f"[ERROR] {len(missing)} experiments are missing in {self.sum_table_name}")
            sys.exit(1)

    def import_partition_tables(self, other_db_path, part):
        log_check(self.is_whole, "importing into a partial project does not make sense")
        con, cur = get_cursor(self.db_path)

        assert table_exists(cur, self.exp_table_name)
        assert table_exists(cur, self.sum_table_name)

        cur.execute(f'ATTACH "{other_db_path}" as OTHER_DB;')
        other_exp_tname, other_sum_tname = get_table_names(self.proj, self.solver, part)
        cur.execute(f"INSERT INTO {self.exp_table_name} SELECT * FROM OTHER_DB.{other_exp_tname}")
        cur.execute(f"INSERT INTO {self.sum_table_name} SELECT * FROM OTHER_DB.{other_sum_tname}")
        conclude(con)

    def probe_other_db(self, other_db_path):
        log_check(self.is_whole, "importing to a partial project does not make sense")
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

    # this is only used for migration
    def import_tables(self, other_db_path, other_exp, other_sum):
        con, cur = get_cursor(self.db_path)
        if table_exists(cur, self.exp_table_name):
            cur.execute(f"""DROP TABLE {self.exp_table_name}""")
        if table_exists(cur, self.sum_table_name):
            cur.execute(f"""DROP TABLE {self.sum_table_name}""")

        create_exp_table(cur, self.exp_table_name)
        create_sum_table(cur, self.sum_table_name)

        cur.execute(f'ATTACH "{other_db_path}" as OTHER_DB;')
        cur.execute(f"INSERT INTO {self.exp_table_name} SELECT * FROM OTHER_DB.{other_exp}")
        
        res = cur.execute(f"""SELECT * FROM OTHER_DB.{other_sum}""")
        rows = res.fetchall()
        # con.close()

        mut_size = self.num_mutant

        special_convert = "opaque" in self.exp_name
        # print(self.exp_name, special_convert)

        for row in rows:
            blob = np.frombuffer(row[2], dtype=int)
            if blob.shape == (488,):
                blob = blob.reshape((4, 2, mut_size + 1))
                blob = blob[:3, :, :]
            else:
                blob = blob.reshape((len(self.enabled_muts), 2, mut_size + 1))

            path = row[0]
            if special_convert:
                path = path.replace(".dfyxxx", ".dfy.").replace(".1.smt2", ".smt2")
            cur.execute(f"""INSERT INTO {self.sum_table_name} VALUES(?, ?);""", (path, blob))
        conclude(con)

        self.load_sum_table()
