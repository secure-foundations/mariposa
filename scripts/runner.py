import sys, os, subprocess
from db_utils import *
import multiprocessing as mp
import time

def subprocess_run(command, cwd=None):
    print(command)
    start_time = time.time()
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

class Z3Task:
    def __init__(self, cfg, mut, query_path, solver_path):
        assert ("z3" in solver_path)
        self.table_name = cfg.table_name
        self.mut = mut
        self.query_path = query_path
        self.solver_path = solver_path
        self.timeout = cfg.timeout

    def run(self):
        command = f"{self.solver_path} {self.query_path} -T:{self.timeout} -st"
        out, err, elapsed = subprocess_run(command)

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {self.table_name}
            (query_path, is_mut, command, std_out, std_error, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?);""", (self.query_path, self.mut, command, out,
            err, elapsed))

        con.commit()
        con.close()

def run_tasks(queue):
    while True:
        task = queue.get()
        if task is None:
            break
        task.run()
    print("proc exit")

class Runner:
    def __init__(self, cfg):
        mp.set_start_method('spawn')
        task_queue = mp.Queue()

        for path in cfg.queries:
            task = Z3Task(cfg, False, path, cfg.solver_paths[0])
            task_queue.put(task)

        # for proc exit
        for _ in range(cfg.num_procs):
            task_queue.put(None)

        processes = []
        # drop_experiment_table(cfg)
        setup_experiment_table(cfg)

        for _ in range(cfg.num_procs):
            p = mp.Process(target=run_tasks, args=(task_queue,))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

        con = sqlite3.connect(DB_PATH)
        cur = con.cursor()
        res = cur.execute(f"""SELECT * FROM test_results""")
        for row in res.fetchall():
            print(row[3])
            print(row[4])
            print(row[5])
        drop_experiment_table(cfg)

if __name__ == '__main__':
    queries = sample_vanilla_queries(PNAME_SERVAL_KOMODO, 30)
    cfg = ExpConfig("test", ["z3-4.4.2"], queries)
    r = Runner(cfg)