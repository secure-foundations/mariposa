import sys, os
import time, random
import multiprocessing as mp
import select
from quake import *

from db_utils import *
from scripts.configure.solver import *


def start_z3(z3_path, mutant_path):
    return subprocess.Popen([z3_path, mutant_path], stdout=subprocess.PIPE)

def start_cvc5(cvc5_path, mutant_path, timelimit):
    args = [cvc5_path, "--incremental", "-q", "--tlimit-per", str(timelimit), mutant_path]
    return subprocess.Popen(args, stdout=subprocess.PIPE)

class Task:
    def __init__(self, exp, exp_tname, origin_path, perturb, mut_seed, solver):
        self.exp = exp
        self.exp_tname = exp_tname
        self.solver = solver
        self.origin_path = origin_path
        self.perturb = perturb
        self.mut_seed = mut_seed
        self.quake = False

    def run_solver_inc(self, mutant_path):
        do_quake(self.origin_path, mutant_path, self.exp.timeout, self.exp.num_mutant + 1)
        assert os.path.exists(mutant_path)

        # max_time = self.exp.timeout * (self.exp.num_mutant + 1)
        if self.solver.type == SolverType.Z3:
            p = start_z3(self.solver.path, mutant_path)
        else:
            assert self.solver.type == SolverType.CVC5
            p = start_cvc5(self.solver.path, mutant_path, self.exp.timeout * 1000)


        give_up = False

        for i in range(self.exp.num_mutant + 1):
            if not give_up:
                std_out = ""
                start_time = time.time()
                poll_result = poll_obj.poll((self.exp.timeout + 3) * 1000)
                elapsed = time.time() - start_time
                if poll_result:
                    outputs = []
                    while "[INFO] mariposa-quake" not in std_out:
                        std_out = p.stdout.readline().decode("utf-8").strip()
                        # print(std_out, i)
                        outputs.append(std_out)
                        if std_out == "":
                            break
                    std_out = "".join(outputs)
                    rcode = parse_basic_output(std_out)
                else:
                    assert std_out == ""
                    print(f"[WARN] solver timeout in {i}th quake seconds")
                    give_up = True

            # give up and set the rest to timeout
            if give_up:
                rcode = "timeout"
                std_out = "Mariposa: quake timeout"
                elapsed = self.exp.timeout * 1000

            if i > 0:
                perturb = str(Mutation.QUAKE)
                mutant_path = self.origin_path + "." + str(i)
            else:
                perturb = None
                mutant_path = self.origin_path
            self.save_result_to_db(mutant_path, perturb, "(interactive session)", rcode, std_out, "", elapsed)

        p.stdout.close()
        p.terminate()

    # def run_solver(self, mutant_path):
    #     if self.solver.type == SolverType.Z3:
    #         command = f"{self.solver.path} '{mutant_path}' -T:{self.exp.timeout}"
    #         out, err, elapsed = subprocess_run(command)
    #         rcode = parse_basic_output(out)
    #     elif self.solver.type == SolverType.CVC5:
    #         seed_options = ""
    #         if self.perturb == Mutation.RESEED:
    #             mutant_path = self.origin_path
    #             seed_options = f"--sat-random-seed {self.mut_seed} --seed {self.mut_seed}"
    #         command = f"{self.solver.path} --incremental --quiet --tlimit-per {self.exp.timeout * 1000} '{mutant_path}' {seed_options}"
    #         out, err, elapsed = subprocess_run(command)
    #         if elapsed >= self.exp.timeout * 1000:
    #             rcode = "timeout"
    #         else:
    #             rcode = parse_basic_output(out)
    #     if rcode == "error":
    #         print("[ERROR] solver error: {} {} {}".format(command, out, err))
    #     self.save_result_to_db(mutant_path, self.perturb, command, rcode, out, err, elapsed)

    def run(self):
        query_name = os.path.basename(self.origin_path)
        assert query_name.endswith(".smt2")
        query_name.replace(".smt2", "")
        gen_path_pre = "gen/" + self.exp_tname + "/" + query_name
        
        if self.perturb is not None:
            mutant_path = f"{gen_path_pre}.{str(self.mut_seed)}.{self.perturb}.smt2"

            command = f"{MARIPOSA_BIN_PATH} -i '{self.origin_path}' -m {self.perturb} -o '{mutant_path}' -s {self.mut_seed}"

            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

            if result.returncode != 0 or not os.path.exists(mutant_path):
                print("[ERROR] MARIPOSA failed: " + command)
                return
        else:
            mutant_path = self.origin_path

        if self.quake:
            mutant_path = f"{gen_path_pre}.quake.smt2"
            self.run_solver_inc(mutant_path)
        else:
            self.run_solver(mutant_path)

        if not self.exp.keep_mutants and mutant_path != self.origin_path:
            # remove mutant
            os.system(f"rm '{mutant_path}'")

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
    print(f"[INFO] worker {id} finished")

class Runner:
    def _set_up_table(self):
        con, cur = get_cursor(self.exp.db_path)
        exists = table_exists(cur, self.exp_tname)
        san_check(not exists, f"[ERROR] table {self.exp_tname} already exists")
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

        for origin_path in origin_paths:
            tasks += self.get_tasks_from_original_query(origin_path, solver)

        if (part_id, part_num) != (1, 1):
            print(f"[INFO] running ONLY part {part_id}th of {part_num} in {project.name}")

        random.shuffle(tasks)

        for task in tasks:
            self.task_queue.put(task)

        self._run_workers()
        populate_sum_table(self.exp, self.exp_tname, self.sum_tname)

    def update_project(self, project, solver, query_path):
        self.exp_tname = self.exp.get_exp_tname(project, solver)
        self.sum_tname = self.exp.get_sum_tname(project, solver)
        drop_query(self.exp.db_path, self.exp_tname, self.sum_tname, query_path)

        tasks = self.get_tasks_from_original_query(query_path, solver)

        for task in tasks:
            self.task_queue.put(task)

        self._run_workers()

        con, cur = get_cursor(self.exp.db_path)
        res = cur.execute(f"""
        SELECT query_path, result_code, elapsed_milli
        FROM {self.exp_tname}
        WHERE query_path = ?""", (query_path,))

        vanilla_rows = res.fetchall()
        assert len(vanilla_rows) == 1

        (vanilla_path, v_rcode, v_time) = vanilla_rows[0]
        add_single_summary(self.exp, cur, self.exp_tname, self.sum_tname, query_path, v_rcode, v_time)

        con.commit()
        con.close()

# def run_projects_solvers(exp, projects, solvers):
#     for project, solver in itertools.product(projects, solvers):
#         r = Runner(exp)
#         r.run_single_project(project, solver)

def dump_status(project, solver, cfg, ana):
    rows = load_sum_table(project, solver, cfg)
    # print("solver:", solver.path)
    print("solver used:", solver.path)

    for row in rows:
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

if __name__ == "__main__":
    import shutil
    query_path = sys.argv[1]

    c = Configer()
    solver = c.load_known_solver("cvc5_1_0_3")
    exp = c.load_known_experiment("debug")
    p = create_single_mode_project(query_path, solver)

    if exp.db_path == "":
        exp.db_path = f"{p.clean_dir}/test.db"
    dir_exists = os.path.exists(p.clean_dir)
    if dir_exists:
        shutil.rmtree(p.clean_dir, ignore_errors=True)
    os.makedirs(p.clean_dir)

    command = f"./target/release/mariposa -i '{query_path}' --chop --remove-debug -o '{p.clean_dir}/split.smt2'"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    print(result.stdout.decode('utf-8'), end="")
    r = Runner(exp)
    r.run_project(p, solver, 1, 1)

    con, cur = get_cursor(exp.db_path)
    sum_name = exp.get_sum_tname(p, solver, 1, 1)

    ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")
    dump_status(p, p.artifact_solver, exp, ANA)
    # split_query_context(sys.argv[1])
