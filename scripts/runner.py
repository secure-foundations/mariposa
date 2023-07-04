import sys, os
import time, random
import subprocess
import multiprocessing as mp
import itertools

from db_utils import *
from configer import *

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
    def __init__(self, exp, exp_tname, origin_path, perturb, mut_seed, solver):
        self.exp = exp
        self.exp_tname = exp_tname
        self.solver = solver
        self.origin_path = origin_path
        self.perturb = perturb
        self.mut_seed = mut_seed

    def run_z3(self, mutant_path):
        solver = self.solver
        exp = self.exp

        import subprocess

        def start(z3):
            return subprocess.Popen(
                [z3, "-in"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE)

        def read(process):
            return process.stdout.readline().decode("utf-8").strip()

        def write(process, message):
            process.stdin.write(f"{message.strip()}\n".encode("utf-8"))
            process.stdin.flush()

        def terminate(process):
            process.stdin.close()
            process.terminate()
            process.wait(timeout=0.2)
        
        p = start(solver.path)
        
        with open(mutant_path, "r") as f:
            repeat = False
            context = []
            for line in f:
                if "(push" in line:
                    repeat = True
                if repeat and "(get-info" not in line:
                    context.append(line)
                else:
                    write(p, line)
                if "(check-sat)" in line:
                    context.append("(pop 1)\n")
                    break

        context.insert(1, f"(set-option :timeout {exp.timeout * 1000})\n")
        context.insert(-1, "(set-option :timeout 0)\n")

        context = "".join(context)
        # print(context)

        reports = dict()

        for i in range(exp.num_mutant + 1):
            start_time = time.time()
            write(p, context)
            out = read(p)
            elapsed = round((time.time() - start_time) * 1000)
            rcode = parse_basic_output_z3(out)

            if rcode == "error":
                print("[INFO] solver error: ", out)
            # else:
            #     print("[INFO] solver result: ", rcode, elapsed)

            reports[i] = (rcode, elapsed, out)

        if not exp.keep_mutants and self.perturb is not None:
            # remove mutant
            os.system(f"rm '{mutant_path}'")
        
        con = sqlite3.connect(exp.db_path)
        cur = con.cursor()
        for i in reports:
            rcode, elapsed, out = reports[i]
            if i != 0:
                mutant_path = self.origin_path + "." + str(i)
                per = "inc"
            else:
                per = None

            cur.execute(f"""INSERT INTO {self.exp_tname}
                (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
                VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
                (mutant_path, self.origin_path, per, "", out, "", rcode, elapsed))
        con.commit()
        con.close()

    def run(self):
        if self.perturb is not None:
            query_name = os.path.basename(self.origin_path)
            assert query_name.endswith(".smt2")
            query_name.replace(".smt2", "")
            gen_path_pre = "gen/" + self.exp_tname + "/" + query_name
            mutant_path = f"{gen_path_pre}.{str(self.mut_seed)}.{self.perturb}.smt2"

            command = f"{MARIPOSA_BIN_PATH} -i '{self.origin_path}' -m {self.perturb} -o '{mutant_path}' -s {self.mut_seed}"

            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

            if result.returncode != 0 or not os.path.exists(mutant_path):
                print("[ERROR] MARIPOSA failed: " + command)
                return
        else:
            mutant_path = self.origin_path
            
        self.run_z3(mutant_path)

def print_eta(elapsed, cur_size, init_size):
    from datetime import timedelta
    from datetime import datetime

    elapsed = round(elapsed/3600, 2)
    done_size = init_size - cur_size
    estimated = round(cur_size * (elapsed / done_size), 2)
    estimated = datetime.now() + timedelta(hours=estimated)
    print(f"[INFO] finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {estimated.strftime('%Y-%m-%d %H:%M')}")

def run_tasks(queue, start_time, id):
    init_size = queue.qsize()
    pelapsed = 0

    while True:
        task = queue.get()
        if id == 0:
            elapsed = time.time() - start_time
            if elapsed > pelapsed + 60:
                print_eta(elapsed, queue.qsize(), init_size)
                pelapsed = elapsed
        if task is None:
            break
        task.run()

class Runner:
    def _set_up_table(self):
        con, cur = get_cursor(self.exp.db_path)
        exists = table_exists(cur, self.exp_tname)
        exit_with_on_fail(not exists, f"[ERROR] table {self.exp_tname} already exists")
        create_experiment_table(cur, self.exp_tname)
        con.commit()
        con.close()

    def __init__(self, exp):
        self.task_queue = mp.Queue()
        self.exp = exp
    
        if exp.init_seed is not None:
            print(f"[INFO] using initial seed: {exp.init_seed}")
            random.seed(exp.init_seed)

    def _run_workers(self):
        start_time = time.time()
        processes = []
        print(f"[INFO] {self.task_queue.qsize() + self.exp.num_procs} tasks queued")

        for i in range(self.exp.num_procs):
            p = mp.Process(target=run_tasks, args=(self.task_queue, start_time, i,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

        print("[INFO] workers finished")

    def run_project(self, project, solver, part_id, part_num):
        self.exp_tname = self.exp.get_exp_tname(project, solver, part_id, part_num)
        self.sum_tname = self.exp.get_sum_tname(project, solver, part_id, part_num)
        self._set_up_table()
        tasks = []
        for origin_path in project.list_queries(part_id, part_num):
            task = Task(self.exp, self.exp_tname, origin_path, None, None, solver)
            tasks.append(task)

            for perturb in self.exp.enabled_muts:            
                for _ in range(self.exp.num_mutant):
                    mut_seed = random.randint(0, 0xffffffffffffffff)
                    task = Task(self.exp, self.exp_tname, origin_path, perturb, mut_seed, solver)
                    tasks.append(task)

        if (part_id, part_num) != (1, 1):
            print(f"[INFO] running ONLY part {part_id}th of {part_num} in {project.name}")

        random.shuffle(tasks)
        for task in tasks:
            self.task_queue.put(task)

        self._run_workers()
        self.exp.enabled_muts = ["inc"]
        populate_sum_table(self.exp, self.exp_tname, self.sum_tname)

# def run_projects_solvers(exp, projects, solvers):
#     for project, solver in itertools.product(projects, solvers):
#         r = Runner(exp)
#         r.run_single_project(project, solver)

def check_serenity_status():
    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"

    print("[INFO] building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    # assert stdout == "master"
    os.system("cargo build --release")

if __name__ == "__main__":
    import numpy as np

    c = Configer()
    solver = c.load_known_solver("z3_4_12_1")
    exp = c.load_known_experiment("incremental")
    p = c.load_known_project("nr")

    r = Runner(exp)
    r.run_project(p, solver, 1, 100)

    con, cur = get_cursor(exp.db_path)
    sum_name = exp.get_sum_tname(p, solver, 1, 100)

    res = cur.execute(f"""SELECT * FROM {sum_name}""")
    rows = res.fetchall()

    nrows = []
    mut_size = exp.num_mutant
    for row in rows:
        mutations = ast.literal_eval(row[1])
        blob = np.frombuffer(row[2], dtype=int)
        blob = blob.reshape((len(mutations), 2, mut_size + 1))
        nrow = [row[0], mutations, blob]
        nrows.append(nrow)
        print(blob)