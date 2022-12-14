import sys, os, subprocess
from db_utils import *
import multiprocessing as mp
import time
import random
import scipy.stats as stats
import numpy as np
import math

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

def z3_basic_parse(output):
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "unknown" in output:
        return "unknown"
    elif "timeout" in output:
        return "timeout"
    return "error"

class Z3TaskGroup:
    def __init__(self, mut, vanilla_path, solver_path):
        assert ("z3" in solver_path)
        self.vanilla_path = vanilla_path
        self.mutant_paths = []
        self.solver_path = solver_path

    def _sample_size_enough(self, veri_times, veri_results, cfg):
        sample_size = len(veri_times)
        assert (sample_size == len(veri_results))

        if sample_size < cfg.min_mutants:
            return False

        t_critical = stats.t.ppf(q=cfg.confidence_level, df=sample_size-1)  
        # get the sample standard deviation
        time_stdev = np.std(veri_times, ddof=1)
        # standard deviation estimate
        sigma = time_stdev/math.sqrt(sample_size) 
        time_moe = t_critical * sigma

        p = sum(veri_results) / sample_size
        res_moe = t_critical * math.sqrt((p*(1-p))/sample_size)

        # res_stdev = np.std(veri_results, ddof=1)
        # sigma = res_stdev/math.sqrt(sample_size) 
        # res_moe = t_critical * sigma
        # print(res_moe, time_moe)

        return time_moe < cfg.time_moe_limit * 1000 and res_moe < cfg.res_moe_limit

    def _run_single(self, query_path, is_mut, cfg):
        assert (cfg.trials == 1)
        command = f"{self.solver_path} {query_path} -T:{cfg.timeout} -st"
        print(command)
        out, err, elapsed = subprocess_run(command)
        rcode = z3_basic_parse(out)

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {cfg.table_name}
            (query_path, vanilla_path, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?);""",
            (query_path, self.vanilla_path, command, out, err, rcode, elapsed))
        con.commit()
        con.close()
        return elapsed, rcode

    def run(self, cfg):
        elapsed, rcode = self._run_single(self.vanilla_path, False, cfg)
        # print("vanilla done: " + str(elapsed) + " milliseconds " + rcode)

        gen_path_pre = "gen/" + cfg.table_name + "_" + self.vanilla_path[5::]

        veri_times = []
        veri_results = []

        for _ in range(cfg.max_mutants):
            seed = random.randint(0, 0xffffffffffffffff)
            mutant_path = gen_path_pre.replace("smt2", str(seed) + ".me.smt2")
            command = f"{MARIPOSA_BIN_PATH} -i {self.vanilla_path} -p mix -o {mutant_path} -s {seed}"
            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
            if result.returncode != 0:
                print("MARIPOSA failed: " + command)
                return

            elapsed, rcode = self._run_single(mutant_path, True, cfg)
            veri_times.append(elapsed)
            if rcode == "unsat":
                veri_results.append(1)
            else:
                veri_results.append(0)

            if self._sample_size_enough(veri_times, veri_results, cfg):
                print(f"{self.vanilla_path} mutants: {len(veri_times)}")
                break
            # self.mutant_paths.append(mutant_path)
            # print("mutant done: " + str(elapsed) + " milliseconds " + rcode)

def run_group_tasks(queue, cfg):
    while True:
        task = queue.get()
        if task is None:
            break
        task.run(cfg)
    print("worker exit")

class Runner:
    def _add_group_task(self, path, cfg):
        # for each solver create a task group
        for solver_path in cfg.solver_paths:
            if "z3" in solver_path:
                task = Z3TaskGroup(False, path, solver_path)
            else:
                assert (False)
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
        drop_experiment_table(cfg, True)
        setup_experiment_table(cfg)

        for _ in range(cfg.num_procs):
            p = mp.Process(target=run_group_tasks, args=(self.task_queue, cfg,))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

if __name__ == '__main__':
    queries = sample_vanilla_queries(PNAME_SERVAL_KOMODO, 200)
    cfg = ExpConfig("test2", ["z3-4.4.2"], queries)
    # print(cfg.timeout)
    r = Runner(cfg)

    # con = sqlite3.connect(DB_PATH)
    # cur = con.cursor()
    # res = cur.execute(f"""SELECT * FROM test_results""")
    # for row in res.fetchall():
    #     print(row[3])
    #     print(row[4])
    #     print(row[5])