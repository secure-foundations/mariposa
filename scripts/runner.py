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
    assert "timeout" in output
    return "timeout"

def print_sample_stats(samples, moe):
    sample_mean = np.mean(samples)
    confidence_interval = (sample_mean - moe, sample_mean + moe)  

    print(f"""size: {len(samples)}
mean: {sample_mean}
margin of error: {moe}
confidence interval: {confidence_interval}
""")

class Z3TaskGroup:
    def __init__(self, cfg, mut, vanilla_path, solver_path):
        assert ("z3" in solver_path)
        self.table_name = cfg.table_name
        self.vanilla_path = vanilla_path
        self.mutant_paths = []
        self.solver_path = solver_path
        self.timeout = cfg.timeout
        self.trials = cfg.trials
        self.max_mutants = cfg.max_mutants
        self.min_mutants = cfg.min_mutants

    def run_single(self, query_path, is_mut):
        assert (self.trials == 1)
        command = f"{self.solver_path} {query_path} -T:{self.timeout} -st"
        out, err, elapsed = subprocess_run(command)
        rcode = z3_basic_parse(out)

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {self.table_name}
            (query_path, is_mut, command, std_out, std_error, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?);""", (self.vanilla_path, is_mut, command, out,
            err, elapsed))
        con.commit()
        con.close()
        return elapsed, rcode

    def run(self):
        print(self.vanilla_path)
        elapsed, rcode = self.run_single(self.vanilla_path, False)
        print("vanilla done: " + str(elapsed) + " milliseconds " + rcode)

        gen_path_pre = "gen/" + self.table_name + "_" + self.vanilla_path[5::]

        veri_times = []
        veri_results = []

        for _ in range(self.max_mutants):
            seed = random.randint(0, 0xffffffffffffffff)
            mutant_path = gen_path_pre.replace("smt2", str(seed) + ".me.smt2")
            command = f"{MARIPOSA_BIN_PATH} -i {self.vanilla_path} -p mix -o {mutant_path} -s {seed}"
            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
            assert (result.returncode == 0)

            elapsed, rcode = self.run_single(mutant_path, True)
            veri_times.append(elapsed)
            if rcode == "unsat":
                veri_results.append(100)
            else:
                veri_results.append(0)

            print("mutant done: " + str(elapsed) + " milliseconds " + rcode)

            sample_size = len(veri_times)

            if sample_size >= self.min_mutants:
                t_critical = stats.t.ppf(q=0.95, df=sample_size-1)  
                # get the sample standard deviation
                time_stdev = np.std(veri_times, ddof=1)
                # standard deviation estimate
                sigma = time_stdev/math.sqrt(sample_size) 
                time_moe = t_critical * sigma

                res_stdev = np.std(veri_results, ddof=1)
                sigma = res_stdev/math.sqrt(sample_size) 
                res_moe = t_critical * sigma

                print(res_moe, time_moe)

                if time_moe < 3000 and res_moe < 5:
                    break

        print_sample_stats(veri_times, time_moe)
        print_sample_stats(veri_results, res_moe)

def run_group_tasks(queue):
    while True:
        task = queue.get()
        if task is None:
            break
        task.run()
    print("worker exit")

class Runner:
    def _add_group_task(self, path, cfg):
        # for each solver create a task group
        for solver_path in cfg.solver_paths:
            if "z3" in solver_path:
                task = Z3TaskGroup(cfg, False, path, solver_path)
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
            p = mp.Process(target=run_group_tasks, args=(self.task_queue,))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

        # con = sqlite3.connect(DB_PATH)
        # cur = con.cursor()
        # res = cur.execute(f"""SELECT * FROM test_results""")
        # for row in res.fetchall():
        #     print(row[3])
        #     print(row[4])
        #     print(row[5])
        drop_experiment_table(cfg, False)

if __name__ == '__main__':
    queries = sample_vanilla_queries(PNAME_SERVAL_KOMODO, 1)
    # queries = ["data/cs_komodo/1546.2.smt2"]
    cfg = ExpConfig("test", ["z3-4.4.2"], queries)
    cfg.num_procs = 1
    r = Runner(cfg)
