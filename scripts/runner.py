import sys, os
import time, random
import multiprocessing as mp

from db_utils import *
from configer import *

MARIPOSA_BIN_PATH = "./target/release/mariposa"

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

def parse_basic_output_cvc(output, timeout):
    if timeout:
        return "timeout"
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "timeout" in output:
        return "timeout"
    elif "unknown" in output:
        return "unknown"
    return "error"

def start_z3(z3_path):
    return subprocess.Popen(
        [z3_path, "-in"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE)

def start_cvc(cvc_path, timelimit, mut_seed=None):
    args = [cvc_path, "--incremental", "-q", "--tlimit-per", str(timelimit)]
    if mut_seed is not None:
        args += ["--sat-random-seed", str(mut_seed), "--seed", str(mut_seed)]
    return subprocess.Popen(
        args,
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
    process.stdout.close()
    process.stderr.close()
    process.terminate()

class Task:
    def __init__(self, exp, exp_tname, origin_path, perturb, mut_seed, solver):
        self.exp = exp
        self.exp_tname = exp_tname
        self.solver = solver
        self.origin_path = origin_path
        self.perturb = perturb
        self.mut_seed = mut_seed
        self.quake = False

    def run_solver(self, mutant_path):
        solver = self.solver
        exp = self.exp

        solver_type = None

        if "z3" in solver.name:
            solver_type = "z3"
            p = start_z3(solver.path)
        elif "cvc" in solver.name:
            solver_type = "cvc"
            if self.perturb == "reseed" or self.perturb == "all":
                p = start_cvc(solver.path, exp.timeout * 1000, self.mut_seed)
            else:
                p = start_cvc(solver.path, exp.timeout * 1000)
        else:
            print("Solver is currently unsupported. If you are using z3 or cvc, please make sure z3 or cvc is present in the solver name in config.json.")
            sys.exit(1)
        
        with open(mutant_path, "r") as f:
            repeat = False
            context = []
            for line in f:
                if solver_type == "cvc" and "(set-option" in line:
                    continue
                if "(push" in line:
                    repeat = True
                if repeat:
                    if "(get-info" in line:
                        continue
                    context.append(line)
                    if "(check-sat)" in line:
                        context.append("(pop 1)\n")
                        break
                else:
                    if "(check-sat)" in line:
                        break
                    write(p, line)

        if not repeat:
            context = ["(push 1)\n", "(check-sat)\n", "(pop 1)\n"]

        if solver_type == "z3":
            context.insert(1, f"(set-option :timeout {exp.timeout * 1000})\n")
            context.insert(-1, "(set-option :timeout 0)\n")

        context = "".join(context)

        reports = dict()
        repeat = 1

        if self.quake:
            repeat = exp.num_mutant + 1

        for i in range(repeat):
            start_time = time.time()
            out = write(p, context)
            out = read(p)
            elapsed = round((time.time() - start_time) * 1000)
#           print(elapsed)
            if solver_type == "z3":
                rcode = parse_basic_output_z3(out)
            elif solver_type == "cvc":
                rcode = parse_basic_output_cvc(out, elapsed > exp.timeout * 1000)

            if rcode == "error":
                print("[INFO] solver error: ", out)
#           print(rcode)

            reports[i] = (rcode, elapsed, out)

        terminate(p)

        if not exp.keep_mutants and mutant_path != self.origin_path:
            # remove mutant
            os.system(f"rm '{mutant_path}'")

        con = sqlite3.connect(exp.db_path)
        cur = con.cursor()

        for i in reports:
            rcode, elapsed, out = reports[i]

            perturb = self.perturb

            if self.quake and i > 0:
                perturb = str(Mutation.QUAKE)
                mutant_path = self.origin_path + "." + str(i)

            cur.execute(f"""INSERT INTO {self.exp_tname}
                (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
                VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
                (mutant_path, self.origin_path, perturb, "", out, "", rcode, elapsed))
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
            
        self.run_solver(mutant_path)

def print_eta(elapsed, cur_size, init_size):
    from datetime import timedelta
    from datetime import datetime

    elapsed = round(elapsed/3600, 2)
    if init_size is not None and cur_size is not None:
        done_size = init_size - cur_size
        estimated = round(cur_size * (elapsed / done_size), 2)
        estimated = datetime.now() + timedelta(hours=estimated)
        print(f"[INFO] finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {estimated.strftime('%Y-%m-%d %H:%M')}")
    else:
        print(f"[INFO] elapsed: {elapsed} hours")

def run_tasks(queue, start_time, id):
    try:
        init_size = queue.qsize()
    except NotImplementedError:
        init_size = None
    pelapsed = 0

    while True:
        task = queue.get()
        if id == 0:
            elapsed = time.time() - start_time
            if elapsed > pelapsed + 60:
                try:
                    qsize = queue.qsize()
                except NotImplementedError:
                    qsize = None
                print_eta(elapsed, qsize, init_size)
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
        try:
            print(f"[INFO] {self.task_queue.qsize() + self.exp.num_procs} tasks queued")
        except NotImplementedError:
            print(f"[INFO] at least {self.exp.num_procs} tasks queued")

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
        origin_paths = project.list_queries(part_id, part_num)
        print(f"[INFO] running {len(origin_paths)} original queries")

        for origin_path in origin_paths:
            task = Task(self.exp, self.exp_tname, origin_path, None, None, solver)
            if Mutation.QUAKE in self.exp.enabled_muts:
                task.quake = True
            tasks.append(task)

            for perturb in self.exp.enabled_muts:
                if perturb == Mutation.QUAKE:
                    continue
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
        populate_sum_table(self.exp, self.exp_tname, self.sum_tname)

# def run_projects_solvers(exp, projects, solvers):
#     for project, solver in itertools.product(projects, solvers):
#         r = Runner(exp)
#         r.run_single_project(project, solver)

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
