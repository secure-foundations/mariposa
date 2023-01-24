import sys, os, subprocess
import multiprocessing as mp
import time
import random
import scipy.stats as stats
import numpy as np
import math

from db_utils import *
from configer import Mutation, ALL_MUTS

MARIPOSA_BIN_PATH = "./target/release/mariposa"

def subprocess_run(command, debug=False, cwd=None):
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
    def __init__(self, vanilla_path, solver_path):
        # assert ("z3" in solver_path)
        if "z3" in solver_path:
            self.solver_name = SolverName.Z3
        else:
            assert ("cvc5" in solver_path)
            self.solver_name = SolverName.CVC5

        self.vanilla_path = vanilla_path
        self.mutant_paths = []
        self.solver_path = solver_path

    def _sample_size_enough(self, veri_times, veri_results, cfg):
        sample_size = len(veri_times)
        assert (sample_size == len(veri_results))

        if sample_size < cfg.min_mutants:
            return False

        t_critical = stats.t.ppf(q=cfg.confidence_level, df=sample_size-1)  

        p = sum(veri_results) / sample_size
        res_moe = t_critical * math.sqrt((p*(1-p))/sample_size)

        # # get the sample standard deviation
        # time_stdev = np.std(veri_times, ddof=1)
        # # standard deviation estimate
        # sigma = time_stdev/math.sqrt(sample_size) 
        # time_moe = t_critical * sigma

        return res_moe < cfg.res_moe_limit

    def _run_single(self, query_path, perturb, cfg):
        assert (cfg.trials == 1)

        if self.solver_name == SolverName.Z3:
            # -st
            command = f"{self.solver_path} {query_path} -T:{cfg.timeout}"
        else:
            assert (self.solver_name == SolverName.CVC5)
            # --stats
            # TODO: maybe instead cleanup push/pop
            command = f"{self.solver_path} {query_path} -i --tlimit={cfg.timeout * 1000}"

        out, err, elapsed = subprocess_run(command)

        # parse_basic_output_cvc

        if self.solver_name == SolverName.Z3:
            rcode = parse_basic_output_z3(out)
        else:
            rcode = parse_basic_output_cvc(out, err)

        if rcode == "error":
            print(out, err)

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {cfg.table_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (query_path, self.vanilla_path, perturb, command, out, err, rcode, elapsed))
        con.commit()
        con.close()
        return elapsed, rcode

    def run_pert_group(self, gen_path_pre, perturb, cfg):
        veri_times = []
        veri_results = []

        for _ in range(cfg.max_mutants):
            seed = random.randint(0, 0xffffffffffff)

            file_name = f"{str(seed)}.{perturb}.smt2"
            mutant_path = gen_path_pre.replace("smt2", file_name)
            command = f"{MARIPOSA_BIN_PATH} -i {self.vanilla_path} -p {perturb} -o {mutant_path} -s {seed}"

            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
            if result.returncode != 0:
                print("MARIPOSA failed: " + command)
                return

            elapsed, rcode = self._run_single(mutant_path, perturb, cfg)

            veri_times.append(elapsed)
            if rcode == "unsat":
                veri_results.append(1)
            else:
                veri_results.append(0)

            if self._sample_size_enough(veri_times, veri_results, cfg):
                # print(f"{self.vanilla_path} mutants: {len(veri_times)}")
                break

    def run(self, cfg):
        elapsed, rcode = self._run_single(self.vanilla_path, None, cfg)
        if rcode != "unsat":
            print("[WARN] vanilla: " + self.vanilla_path + " " + str(elapsed) + " milliseconds " + rcode)

        gen_path_pre = "gen/" + cfg.table_name + "_" + self.vanilla_path[5::]

        for perturb in ALL_MUTS:
            self.run_pert_group(gen_path_pre, perturb, cfg)

def run_group_tasks(queue, cfg):
    while True:
        task = queue.get()
        print(queue.qsize())
        if task is None:
            break
        task.run(cfg)
    print("worker exit")

class Runner:
    def _add_group_task(self, path, cfg):
        # for each solver create a task group
        for solver_path in cfg.solver_paths:
            task = SolverTaskGroup(path, solver_path)
            self.task_queue.put(task)

    def __init__(self, cfg):
        mp.set_start_method('spawn')
        self.task_queue = mp.Queue()

        for path in cfg.queries:
            self._add_group_task(path, cfg)

        # for proc exit
        for _ in range(cfg.num_procs):
            self.task_queue.put(None)

        processes = []
        # drop_experiment_table(cfg, True)
        # setup_experiment_table(cfg)

        for _ in range(cfg.num_procs):
            p = mp.Process(target=run_group_tasks, args=(self.task_queue, cfg,))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

if __name__ == '__main__':
    queries = sample_vanilla_queries(PNAME_SERVAL_KOMODO, None)
    cfg = ExpConfig("test2", ["z3-4.4.2", "z3-4.11.2"], queries)
    # print(cfg.timeout)
    r = Runner(cfg)

    # con = sqlite3.connect(DB_PATH)
    # cur = con.cursor()
    # res = cur.execute(f"""SELECT * FROM test_results""")
    # for row in res.fetchall():
    #     print(row[3])
    #     print(row[4])
    #     print(row[5])