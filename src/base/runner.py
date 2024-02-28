import os
import multiprocessing as mp

from basics.experiment import *
from basics.solver import SolverType, RCode
from utils.query_utils import emit_quake_file

MARIPOSA_BIN_PATH = "./target/release/mariposa"

class Worker:
    def __init__(self, epart, worker_id):
        self.worker_id = worker_id
        self._exp = epart
        
    def __getattr__(self, item):
        return getattr(self._exp, item)

    def __generate_mutant(self, task):
        mutant_path = task.mutant_path

        if task.perturb == Mutation.QUAKE:
            emit_quake_file(task.origin_path, 
                task.mutant_path, 
                self.timeout, 
                self.num_mutant)
            return

        if task.perturb is None:
            return
            
        command = f"{MARIPOSA_BIN_PATH} -i '{task.origin_path}' -m {task.perturb} -o '{mutant_path}' -s {task.mut_seed}"            

        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

        san_check(result.returncode == 0 and os.path.exists(mutant_path),
                  f"[ERROR] MARIPOSA failed: {command}")

        # if self._exp.shake:
            # command = f"{MARIPOSA_BIN_PATH} -i '{mutant_path}' -o '{mutant_path}' -m tree-shake "

    def run_quake_task(self, task):
        self.solver.start_process(task.mutant_path, self.timeout)

        for i in range(self.num_mutant):
            rcode, elapsed = self.solver.run_quake_iteration(self.timeout)    

            mutant_path = task.mutant_path + "." + str(i)
            self.insert_exp_row(task, mutant_path, rcode, elapsed)
        self.solver.end_process()

    def run_task(self, task):
        cvc_reseed = task.perturb == Mutation.RESEED and \
            self.solver.type == SolverType.CVC5
        mutant_path = task.mutant_path

        # if not cvc_reseed:
        #     self.__generate_mutant(task)

        if task.quake:
            self.run_quake_task(task)
        else:
            if cvc_reseed:
                seeds = task.mut_seed
                mutant_path = task.origin_path
            else:
                seeds = None
            rcode, elapsed = self.solver.run(mutant_path, self.timeout, seeds)
            self.insert_exp_row(task, mutant_path, rcode.value, elapsed)

        if not self.keep_mutants and mutant_path != task.origin_path:
            os.system(f"rm '{mutant_path}'")

def print_eta(elapsed, cur_size, init_size):
    from datetime import timedelta
    from datetime import datetime

    elapsed = round(elapsed/3600, 2)
    if init_size is not None and cur_size is not None:
        done_size = init_size - cur_size
        estimated = round(cur_size * (elapsed / done_size), 2)
        estimated = datetime.now() + timedelta(hours=estimated)
        print(f"[INFO] finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {estimated.strftime('%m-%d %H:%M')}")
    else:
        print(f"[INFO] elapsed: {elapsed} hours")

def try_get_size(q):
    try:
        size = q.qsize()
    except NotImplementedError:
        size = None
    return size

def run_tasks(worker, queue):
    start_time = time.time()
    init_size = try_get_size(queue)
    prev_time = 0

    while True:
        task = queue.get()

        if task is None:
            break

        elapsed = time.time() - start_time
        if elapsed - prev_time > 60:
            prev_time = elapsed
            qsize = try_get_size(queue)
            print_eta(elapsed, qsize, init_size)

        worker.run_task(task)

    elapsed = round((time.time() - start_time) / 3600, 2)
    print(f"[INFO] worker {worker.worker_id} finished in {elapsed} hours")

class Runner:
    def __init__(self):
        self.task_queue = mp.Queue()

    def run_project(self, epart, clear):
        self.epart = epart
        epart.check_tables(clear)
        tasks = epart.build_tasks()
        random.shuffle(tasks)

        for task in tasks:
            self.task_queue.put(task)

        processes = []

        for i in range(self.epart.num_procs):
            worker = Worker(self.epart, i)
            p = mp.Process(target=run_tasks, 
                           args=(worker, self.task_queue,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

        print("[INFO] workers finished")

        self.epart.populate_sum_table()
