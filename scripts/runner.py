import sys, os, argparse
import time, random
import subprocess
import multiprocessing as mp
import numpy as np
import itertools

from db_utils import *
from configs.projects import *
from configs.experiments import *

MARIPOSA_BIN_PATH = "./target/release/mariposa"

def subprocess_run(command, time_limit, debug=False, cwd=None):
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
    elif "timeout" in output:
        return "timeout"
    elif "unknown" in output:
        return "unknown"
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

class Task:
    def __init__(self, cfg, exp_name, origin_path, perturb, mut_seed, solver):
        self.cfg = cfg
        self.exp_name = exp_name
        self.solver = solver
        self.origin_path = origin_path
        self.perturb = perturb
        self.mut_seed = mut_seed

    def run(self):
        solver = self.solver
        cfg = self.cfg

        if self.perturb is not None:
            gen_path_pre = "gen/" + self.exp_name + "/" + self.origin_path[5::]
            file_name = f"{str(self.mut_seed)}.{self.perturb}.smt2"
            mutant_path = gen_path_pre.replace("smt2", file_name)

            command = f"{MARIPOSA_BIN_PATH} -i {self.origin_path} -p {self.perturb} -o {mutant_path} -s {self.mut_seed}"

            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

            if result.returncode != 0:
                print("[ERROR] MARIPOSA failed: " + command)
                return
        else:
            mutant_path = self.origin_path

        command = f"{solver.path} {mutant_path} -T:{cfg.timeout}"
        out, err, elapsed = subprocess_run(command, cfg.timeout + 1)

        # TODO: handle other solvers
        rcode = parse_basic_output_z3(out)

        if rcode == "error":
            print("[INFO] solver error: ", out, err)

        if cfg.remove_mut and self.perturb is not None:
            # remove mutant
            os.system(f"rm {mutant_path}")
        
        con = sqlite3.connect(cfg.db_path)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {self.exp_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (mutant_path, self.origin_path, self.perturb, command, out, err, rcode, elapsed))
        con.commit()
        con.close()

def run_tasks(queue, start_time):
    from datetime import timedelta
    from datetime import datetime
    init_size = queue.qsize()

    while True:
        task = queue.get()
        cur_size = queue.qsize()
        done_size = init_size - cur_size
        if done_size % 200 == 0:
            elapsed = round((time.time() - start_time) / 3600, 2)
            estimated = round(cur_size * (elapsed / done_size), 2)
            print(f"finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {datetime.now() + timedelta(hours=estimated)}")
        if task is None:
            break
        task.run()

def print_single_status(cfg, origin_path, solver, sum_name, ana):
    con, cur = get_cursor(cfg.db_path)
    res = cur.execute(f"""SELECT * FROM {sum_name}
                    WHERE vanilla_path = ?;""", (origin_path,))
    rows = res.fetchall()
    con.close()
    assert len(rows) == 1
    row = rows[0]

    mut_size = cfg.max_mutants
    perturbs = ast.literal_eval(row[1])
    blob = np.frombuffer(row[2], dtype=int)
    blob = blob.reshape((len(perturbs), 2, mut_size + 1))
    status, votes = ana.categorize_query(blob)

    print("")
    print("--- overall ---")
    print("query:", origin_path)
    print("solver:", solver.path)
    print("status:", status)
    print("")
    print("--- original ---")
    print("result:", RCode(blob[0][0][0]))
    print("time:", round(blob[0][1][0]/1000, 2), "(s)")
    print("")
    for i in range(len(perturbs)):
        print(f"--- {perturbs[i]} ---")
        count = count_within_timeout(blob[i], RCode.UNSAT, timeout=ana.timeout)
        times = np.clip(blob[i][1], 0, ana.timeout) / 1000
        print(f"status: {votes[i]}")
        print("success:", f"{count}/{mut_size+1} {round(count / (mut_size+1) * 100, 1)}%")
        print("time mean:", f"{round(np.mean(times), 2)}(s)")
        print("time std:", f"{round(np.std(times), 2)}(s)")
        print("")

class Runner:
    def _set_up_table(self):
        con, cur = get_cursor(self.cfg.db_path)
        exists = check_table_exists(cur, self.exp_name)
        if not exists:
            create_experiment_table(cur, self.exp_name)
        elif cfg.db_mode == DBMode.CREATE and exists:
            ok = confirm_drop_table(cur, self.exp_name)
            if not ok:
                print(f"[INFO] keep existing table {self.exp_name}")
                sys.exit()
            create_experiment_table(cur, self.exp_name)
        con.commit()
        con.close()

    def __init__(self, cfg):
        mp.set_start_method('spawn')
        self.task_queue = mp.Queue()
        self.cfg = cfg
    
        if cfg.init_seed is not None:
            print(f"[INFO] using initial seed: {cfg.init_seed}")
            random.seed(cfg.init_seed)

    def _add_exp(self, origin_path, solver):
        task = Task(self.cfg, self.exp_name, origin_path, None, None, solver)
        self.task_queue.put(task)

        for perturb in self.cfg.enabled_muts:            
            for _ in range(self.cfg.max_mutants):
                mut_seed = random.randint(0, 0xffffffffffffffff)
                task = Task(self.cfg, self.exp_name, origin_path, perturb, mut_seed, solver)
                self.task_queue.put(task)

    def _run_workers(self):
        start_time = time.time()
        processes = []
        print(f"[INFO] {self.task_queue.qsize()} tasks queued")
        
        for _ in range(self.cfg.num_procs):
            p = mp.Process(target=run_tasks, args=(self.task_queue, start_time,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

        print("[INFO] workers finished")

    def run_project_exps(self, project, solver):
        self.exp_name = self.cfg.get_exp_name(project, solver)
        self._set_up_table()
        for origin_path in project.list_queries():
            self._add_exp(origin_path, solver)
        sum_name = self.cfg.get_sum_name(project, solver)
        create_sum_table(cfg, self.exp_name, sum_name)

    def run_single_exp(self, origin_path, solver):
        self.exp_name = self.cfg.get_exp_name(MISC, solver)
        self._set_up_table()       
        self._add_exp(origin_path, solver)
        self._run_workers()

def run_multi_exps(cfg, projects, solvers):
    for project, solver in itertools.product(projects, solvers):
        r = Runner(cfg)
        r.run_project_exps(project, solver)

def check_serenity_status():
    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"

    print("[INFO] building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    # assert stdout == "master"
    os.system("cargo build --release")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='mariposa is a tool for testing stability')

    parser.add_argument("-q", "--query", required=True, help="the input query (multiple check-sat will be split)")
    parser.add_argument("-s", "--solver", required=True, help="the solver to use")
    parser.add_argument("-c", "--clear", default=False, action='store_true', help="clear data from previous experiments")
    args = parser.parse_args()

    origin_path = args.query
    solver = SolverInfo.from_path(args.solver)

    if args.clear:
        os.system(f"rm -rf gen/*")
        print("[INFO] cleared data from past experiment")

    cfg = ExpConfig("test", "gen/test.db")
    cfg.init_seed = 0xdeadbeef

    ana = Analyzer("z_test")
    ana.timeout = cfg.timeout * 1000

    r = Runner(cfg)
    r.run_single_exp(args.query, solver)

    sum_name = cfg.get_sum_name(MISC, solver)
    create_sum_table(cfg, r.exp_name, sum_name)
    print_single_status(cfg, origin_path, solver, sum_name, ana)

# from ana import RCode 
# from ana import Analyzer
# from ana import Stability
# from runner import parse_basic_output_z3
# from runner import subprocess_run
# import numpy as np

# timeout = 60

# def async_run_single_mutant(results, command):
#     items = command.split(" ")
#     os.system(command)
#     items = command.split(" ")
#     command = f"./solvers/z3_place_holder {items[6]} -T:{timeout}"
#     out, err, elapsed = subprocess_run(command, timeout + 1)
#     rcode = parse_basic_output_z3(out)
#     # os.system(f"rm {items[6]}")
#     results.append((elapsed, rcode))

# def mariposa(task_file):
#     commands = [t.strip() for t in open(task_file, "r").readlines()]
#     plain = commands[0]
#     commands = commands[1:]

#     import multiprocessing as mp
#     manager = mp.Manager()
#     pool = mp.Pool(processes=7)

#     command = f"./solvers/z3_place_holder {plain} -T:{timeout}"
#     out, err, elapsed = subprocess_run(command, timeout + 1)
#     rcode = parse_basic_output_z3(out)
#     pr = (elapsed, rcode)
#     ana = Analyzer("z_test")
#     ana.timeout = 6e4 # 1 min

#     reseeds = manager.list([pr])
#     renames = manager.list([pr])
#     shuffles = manager.list([pr])

#     for command in commands:
#         if "rseed" in command:
#             pool.apply_async(async_run_single_mutant, args=(reseeds, command))
#         elif "rename" in command:
#             pool.apply_async(async_run_single_mutant, args=(renames, command))
#         elif "shuffle" in command:
#             pool.apply_async(async_run_single_mutant, args=(shuffles, command))
#         else:
#             assert False
    
#     pool.close()
#     pool.join()

#     assert len(reseeds) == len(renames) == len(shuffles) == 61

#     blob = np.zeros((3, 2, 61), dtype=int)
#     for i, things in enumerate([reseeds, renames, shuffles]):
#         for j, (veri_times, veri_res) in enumerate(things):
#             blob[i, 0, j] = RCode.from_str(veri_res).value
#             blob[i, 1, j] = veri_times

#     cat = ana.categorize_query(blob)

#     print(blob)
#     print(cat)

#     if cat == Stability.STABLE:
#         exit(0) # good
#     if cat == Stability.INCONCLUSIVE:
#         exit(125) # skip
#     exit(1) # bad 

# if __name__ == "__main__":
#     mariposa(sys.argv[1])