import sys, os, subprocess
import multiprocessing as mp
import time
import random
import scipy.stats as stats
import numpy as np
import math

from db_utils import *
from configs.projects import *
from configs.experiments import *

MARIPOSA_BIN_PATH = "./target/release/mariposa"

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    SSEED = "sseed"

ALL_MUTS = [e.value for e in Mutation]

def subprocess_run(command, time_limit, debug=False, cwd=None):
    command = f"timeout {time_limit} " + command
    if debug:
        print(command)
    start_time = time.time()
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

def parse_basic_output_z3(output):
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "unknown" in output:
        return "unknown"
    elif "timeout" in output:
        return "timeout"
    return "error"

def parse_basic_output_cvc(output, error):
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "unknown" in output:
        return "unknown"
    elif "interrupted by timeout" in error:
        return "timeout"
    return "error"

class SolverTaskGroup:
    def __init__(self, cfg, vanilla_path, solver):
        self.vanilla_path = vanilla_path
        self.mutant_paths = []
        self.solver = solver
        assert isinstance(cfg, QueryExpConfig)
        self.cfg = cfg
        self.table_name = cfg.get_solver_table_name(self.solver)

    def _sample_size_enough(self, veri_times, veri_results):
        sample_size = len(veri_times)
        assert (sample_size == len(veri_results))

        if sample_size < self.cfg.min_mutants:
            return False

        t_critical = stats.t.ppf(q=self.cfg.confidence_level, df=sample_size-1)  

        p = sum(veri_results) / sample_size
        res_moe = t_critical * math.sqrt((p*(1-p))/sample_size)

        # # get the sample standard deviation
        # time_stdev = np.std(veri_times, ddof=1)
        # # standard deviation estimate
        # sigma = time_stdev/math.sqrt(sample_size) 
        # time_moe = t_critical * sigma

        return res_moe < self.cfg.res_moe_limit

    def _run_single(self, query_path, perturb):
        assert (self.cfg.trials == 1)

        if self.solver.brand == SolverBrand.Z3:
            # -st
            command = f"{self.solver.path} {query_path} -T:{self.cfg.timeout}"
        else:
            assert (self.solver.brand == SolverBrand.CVC5)
            # --stats
            command = f"{self.solver.path} {query_path} --tlimit={self.cfg.timeout * 1000}"

        out, err, elapsed = subprocess_run(command, self.cfg.timeout + 1)

        # parse_basic_output_cvc

        if self.solver.brand == SolverBrand.Z3:
            rcode = parse_basic_output_z3(out)
        else:
            rcode = parse_basic_output_cvc(out, err)

        if rcode == "error":
            print(out, err)

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {self.table_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (query_path, self.vanilla_path, perturb, command, out, err, rcode, elapsed))
        con.commit()
        con.close()
        return elapsed, rcode

    def run_pert_group(self, gen_path_pre, perturb):
        veri_times = []
        veri_results = []

        for _ in range(self.cfg.max_mutants):
            seed = random.randint(0, 0xffffffffffff)

            file_name = f"{str(seed)}.{perturb}.smt2"
            mutant_path = gen_path_pre.replace("smt2", file_name)
            command = f"{MARIPOSA_BIN_PATH} -i {self.vanilla_path} -p {perturb} -o {mutant_path} -s {seed}"

            # generate mutant
            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
            if result.returncode != 0:
                print("[WARN] MARIPOSA failed: " + command)
                return

            elapsed, rcode = self._run_single(mutant_path, perturb)

            # remove mutant
            os.system(f"rm {mutant_path}")

            veri_times.append(elapsed)
            if rcode == "unsat":
                veri_results.append(1)
            else:
                veri_results.append(0)

            if self._sample_size_enough(veri_times, veri_results):
                break

    def run(self):
        elapsed, rcode = self._run_single(self.vanilla_path, None)
        if rcode != "unsat":
            print("[WARN] vanilla not unsat: " + self.vanilla_path + " " + str(elapsed) + " milliseconds " + rcode)

        gen_path_pre = "gen/" + self.table_name + "/" + self.vanilla_path[5::]

        for perturb in ALL_MUTS:
            self.run_pert_group(gen_path_pre, perturb)

def run_group_tasks(queue):
    while True:
        task = queue.get()
        print(queue.qsize())
        if task is None:
            break
        task.run()
    print("worker exit")

class Runner:
    def __init__(self, cfg, override=False):
        assert isinstance(cfg, ExpConfig)
        self.__setup_tables(cfg, override)

        con = get_connection()
        con, cur = get_cursor()

        mp.set_start_method('spawn')
        self.task_queue = mp.Queue()

        for solver, queries in cfg.samples.items():
            print("loading tasks")
            for query in tqdm(queries):
                task = SolverTaskGroup(cfg.qcfg, query, solver)
                if self.__should_run_task(cfg.qcfg, cur, task):
                    self.task_queue.put(task)
        con.close()


        # for proc exit
        for _ in range(cfg.num_procs):
            self.task_queue.put(None)

        processes = []

        for _ in range(cfg.num_procs):
            p = mp.Process(target=run_group_tasks, args=(self.task_queue,))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

    def __setup_tables(self, cfg, override):
        con, cur = get_cursor()
        ok = True

        for solver in cfg.samples:
            table_name = cfg.qcfg.get_solver_table_name(solver)
            if check_table_exists(cur, table_name):
                if override:
                    ok = confirm_drop_table(cur, table_name)
                    if not ok:
                        sys.exit()
                    create_experiment_table(cur, table_name)
                else:
                    print(f"[INFO] keep existing table {table_name}")
            else:
                create_experiment_table(cur, table_name)
        con.commit()
        con.close()

    # check if enough data has been collected in previous runs
    def __should_run_task(self, cfg, cur, task):
        threshold = cfg.min_mutants * len(ALL_MUTS)
        cur.execute(f"""SELECT COUNT(*) from {cfg.get_solver_table_name(task.solver)}
            WHERE vanilla_path=?
            """, (task.vanilla_path,))
        if cur.fetchone()[0] < threshold:
            return True
        return False

if __name__ == '__main__':
    # cfg = ExpConfig("D_FVBKV_Z3", D_FVBKV, [Z3_4_4_2, Z3_4_6_0, Z3_4_11_2], None)
    cfg = ExpConfig("D_FVBKV_Z3", D_FVBKV, [Z3_4_5_0])
    r = Runner(cfg, True)