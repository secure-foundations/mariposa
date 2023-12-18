from exp_manager import *
from solver_info import *
import os
import multiprocessing as mp

MARIPOSA_BIN_PATH = "./target/release/mariposa"

def output_as_rcode(output):
    if "unsat" in output:
        return RCode.UNSAT
    elif "sat" in output:
        return RCode.SAT
    elif "timeout" in output:
        return RCode.TIMEOUT
    elif "unknown" in output:
        return RCode.UNKNOWN
    return RCode.ERROR

class Worker:
    def __init__(self, epart, worker_id):
        self.worker_id = worker_id
        self.exp_part = epart

    def __generate_mutant(self, task):
        query_name = os.path.basename(task.origin_path)
        gen_prefix = f"gen/{self.exp_part.exp_table_name}/{query_name}"
        mutant_path = f"{gen_prefix}.{str(task.mut_seed)}.{task.perturb}.smt2"

        assert query_name.endswith(".smt2")
        query_name.replace(".smt2", "")

        if task.perturb is None:
            return task.origin_path

        command = f"{MARIPOSA_BIN_PATH} -i '{task.origin_path}' -m {task.perturb} -o '{mutant_path}' -s {task.mut_seed}"

        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

        if result.returncode != 0 or not os.path.exists(mutant_path):
            print("[ERROR] MARIPOSA failed: " + command)
            return None

        return mutant_path

    # assert self.solver.type == SolverType.CVC5:
    # seed_options = ""
    # if self.perturb == Mutation.RESEED:
    #     mutant_path = self.origin_path
    #     seed_options = f"--sat-random-seed {self.mut_seed} --seed {self.mut_seed}"
    # command = f"{self.solver.path} --incremental --quiet --tlimit-per {self.exp.timeout * 1000} '{mutant_path}' {seed_options}"
    # out, err, elapsed = subprocess_run(command)
    # if elapsed >= self.exp.timeout * 1000:
    #     rcode = "timeout"
    # else:
    #     rcode = parse_basic_output(out)

    def __run_solver(self, mutant_path):
        if self.exp_part.solver.type == SolverType.Z3:
            command = f"{self.exp_part.solver.path} '{mutant_path}' -T:{self.exp_part.timeout}"
            out, err, elapsed = subprocess_run(command)
            rcode = output_as_rcode(out)
        else:
            assert False

        if rcode == RCode.ERROR:
            print("[ERROR] solver error: {} {} {}".format(command, out, err))

        return rcode.value, elapsed

    def run_task(self, task):
        assert task.quake == False
        mutant_path = self.__generate_mutant(task)
        rcode, elapsed = self.__run_solver(mutant_path)

        if not self.exp_part.keep_mutants and task.perturb is not None:
            os.remove(mutant_path)

        self.exp_part.insert_exp_row(task, mutant_path, rcode, elapsed)

def run_tasks(worker, queue, start_time):
    while True:
        task = queue.get()
        if task is None:
            break
        worker.run_task(task)
    elapsed = int((time.time() - start_time) / 3600)
    print(f"[INFO] worker {worker.worker_id} finished in {elapsed} hours")

class Runner:
    def __init__(self):
        self.task_queue = mp.Queue()
        
    def run_project(self, epart):
        self.epart = epart
        epart.check_tables()
        tasks = epart.build_tasks()
        random.shuffle(tasks)

        for task in tasks:
            self.task_queue.put(task)

        start_time = time.time()
        processes = []

        # try:
        #     print(f"[INFO] {self.task_queue.qsize() + self.epart.num_procs} tasks queued")
        # except NotImplementedError:
        #     pass

        for i in range(self.epart.num_procs):
            worker = Worker(self.epart, i)
            p = mp.Process(target=run_tasks, 
                           args=(worker, self.task_queue, start_time,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

        print("[INFO] workers finished")

        self.epart.populate_sum_table()
