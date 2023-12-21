from enum import Enum
import numpy as np
import json, random
from typing import Dict, List
from utils.sys_utils import *
from utils.db_utils import *

from execute.solver_runner import SolverRunner
from execute.exp_result import QueryExpResult
from configure.project import Project, Partition

EXP_CONFIG_PATH = "configs/experiments.json"        

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    RESEED = "reseed"
    QUAKE = "quake"
    ALL = "all"

    def __str__(self):
        return str.__str__(self)

class ExpConfig:
    def __init__(self, name):
        objs = json.loads(open(EXP_CONFIG_PATH).read())
        obj = objs["default"]
        obj.update(objs[name])

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

        # where do we store the db?
        self.db_path = obj["db_path"]

def get_table_prefix(proj, solver, part):
    if part.is_whole():
        return scrub(f"{proj.full_name}_{str(solver)}")
    return scrub(f"{proj.full_name}_{str(solver)}_{part}")

class ExpTask:
    """represents a single task, 
    which is a single query with a single mutation"""
    def __init__(self, v_path, g_path, perturb, mut_seed):
        self.origin_path = v_path
        self.perturb = perturb
        self.mut_seed = mut_seed
        self.quake = False
        self.mutant_path = g_path

class ExpPart(ExpConfig):
    """represents a collection of tasks,
    if part is not whole, it is one partition of the project
    this class is used to generate tasks and populate the db
    """
    def __init__(self, exp_name, proj, solver, part=Partition(1, 1)):
        super().__init__(exp_name)
        self.proj = proj
        self.part = part
        self.solver = SolverRunner(solver)

        self.table_prefix = get_table_prefix(proj, solver, part)
        self.exp_table_name = self.table_prefix + "_exp"
        self.sum_table_name = self.table_prefix + "_sum"
        self.gen_dir = f"gen/{self.exp_table_name}"

        if not os.path.exists(self.gen_dir):
            os.makedirs(self.gen_dir)

    def __str__(self):
        return f"""project: {self.proj.full_name}
part: {self.part}
experiment: {self.exp_name}
db_path: {self.db_path}
sub_root: {self.proj.root_dir}
solver: {self.solver}"""

    @staticmethod
    def single_mode_exp(query_path, solver):
        proj = Project.single_mode_project(query_path)
        part = Partition(1, 1)
        exp = ExpPart("single", proj, solver, part)
        exp.db_path = f"{proj.root_dir}/single.db"
        return exp

    def build_query_tasks(self, origin_path):
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

    def build_tasks(self):
        tasks = []
        origin_paths = self.proj.list_queries(self.part)
        print(f"[INFO] running {len(origin_paths)} original queries")

        for origin_path in origin_paths:
            tasks.extend(self.build_query_tasks(origin_path))

        if not self.part.is_whole():
            print(f"[INFO] running ONLY {self.part} in {self.proj.full_name}")

        print(f"[INFO] adding {len(tasks)} tasks")
        return tasks

    def check_tables(self, clear=False):
        con, cur = get_cursor(self.db_path)

        for table_name in [self.exp_table_name, self.sum_table_name]:
            if table_exists(cur, table_name):
                if clear:
                    print(f"[INFO] {table_name} already exists, removing")
                else:
                    print(f"[INFO] {table_name} already exists, remove it? [Y]")
                    san_check(input() == "Y", f"[INFO] aborting")
                cur.execute(f"""DROP TABLE {table_name}""")

        create_exp_table(cur, self.exp_table_name)
        create_sum_table(cur, self.sum_table_name)
        conclude(con)

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
            assert len(rows) == self.num_mutant
            for (j, row) in enumerate(rows):
                blob[i][0][j + 1] = row[0]
                blob[i][1][j + 1] = row[1]

        cur.execute(f"""INSERT INTO {self.sum_table_name}
        VALUES(?, ?, ?);""", (v_path, "", blob))

    def populate_sum_table(self):
        con, cur = get_cursor(self.db_path)

        vanilla_rows = get_vanilla_paths(cur, self.exp_table_name)

        cur.execute(f"""DROP TABLE IF EXISTS {self.sum_table_name}""")
        create_sum_table(cur, self.sum_table_name)

        processed = set()
        print(f"[INFO] post processing exp data")

        for (v_path, v_rcode, v_time) in vanilla_rows:
            if v_path in processed:
                continue
            processed.add(v_path)
            self.insert_sum_row(cur, v_path, v_rcode, v_time)

        conclude(con)

    def load_sum_table(self) -> Dict[str, QueryExpResult]:
        con, cur = get_cursor(self.db_path)
        sum_name = self.sum_table_name

        if not table_exists(cur, sum_name):
            print(f"[INFO] skipping {sum_name}")
            return None

        res = cur.execute(f"""SELECT * FROM {sum_name}""")
        rows = res.fetchall()
        con.close()

        summaries = dict()
        mut_size = self.num_mutant

        for row in rows:
            blob = np.frombuffer(row[2], dtype=int)
            blob = blob.reshape((len(self.enabled_muts), 2, mut_size + 1))
            qr = QueryExpResult(row[0], self.proj.root_dir, self.enabled_muts, blob)
            summaries[qr.base_name] = qr

        return summaries

    def import_tables(self, other_db_path, part):
        assert self.part.is_whole()
        con, cur = get_cursor(self.db_path)

        assert table_exists(cur, self.exp_table_name)
        assert table_exists(cur, self.sum_table_name)

        cur.execute(f'ATTACH "{other_db_path}" as OTHER_DB;')
        other_exp_tname = get_table_prefix(self.proj, self.solver, part) + "_exp"
        cur.execute(f"INSERT INTO {self.exp_table_name} SELECT * FROM OTHER_DB.{other_exp_tname}")
        other_sum_tname = get_table_prefix(self.proj, self.solver, part) + "_sum"
        cur.execute(f"INSERT INTO {self.sum_table_name} SELECT * FROM OTHER_DB.{other_sum_tname}")
        conclude(con)

    def probe_other_db(self, other_db_path):
        assert self.part.num == 1
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
