import os
import multiprocessing as mp

from base.exper import *
from utils.query_utils import Mutation, emit_mutant_query, emit_quake_query

class Worker:
    def __init__(self, exp: Experiment, worker_id):
        self.worker_id = worker_id
        self._exp = exp
        
    def __getattr__(self, item):
        return getattr(self._exp, item)

    def __generate_mutant(self, task):
        if task.perturb == Mutation.QUAKE:
            emit_quake_query(task.origin_path, 
                task.mutant_path, 
                self.num_mutant)
            return

        emit_mutant_query(task.origin_path, 
            task.mutant_path, 
            task.perturb, 
            task.mut_seed)

    def run_quake_task(self, task):
        self.solver.start_process(task.mutant_path, self.timeout)

        for i in range(self.num_mutant):
            rcode, elapsed = self.solver.run_quake_iteration(self.timeout)    
            mutant_path = task.mutant_path + "." + str(i)
            self.insert_exp_row(task, mutant_path, rcode.value, elapsed)

        self.solver.end_process()

    def run_task(self, task):
        actual_path = task.mutant_path
        is_reseed = task.perturb == Mutation.RESEED
        is_compose = task.perturb == Mutation.COMPOSE

        if is_reseed or task.perturb is None:
            actual_path = task.origin_path
        else:
            self.__generate_mutant(task)

        if task.quake:
            self.run_quake_task(task)
        else:
            seeds = task.mut_seed if is_reseed or is_compose else None
            rcode, elapsed = self.solver.run(actual_path, self.timeout, seeds)
            self.insert_exp_row(task, task.mutant_path, rcode.value, elapsed)

        if not self.keep_mutants and actual_path != task.origin_path:
            os.system(f"rm '{actual_path}'")

def print_eta(elapsed, cur_size, init_size):
    from datetime import timedelta
    from datetime import datetime

    elapsed = round(elapsed/3600, 2)
    if init_size is not None and cur_size is not None:
        done_size = init_size - cur_size
        estimated = round(cur_size * (elapsed / done_size), 2)
        estimated = datetime.now() + timedelta(hours=estimated)
        log_debug(f"finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {estimated.strftime('%m-%d %H:%M')}")
    else:
        log_debug(f"elapsed: {elapsed} hours")

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
        if elapsed - prev_time > 120:
            prev_time = elapsed
            qsize = try_get_size(queue)
            print_eta(elapsed, qsize, init_size)

        worker.run_task(task)

    elapsed = round((time.time() - start_time) / 3600, 2)
    log_debug(f"worker {worker.worker_id} finished in {elapsed} hours")

class Runner:
    def __init__(self, epart: Experiment):
        self.task_queue = mp.Queue()
        self.exp = epart

    def run_experiment(self, clear):
        tasks = self.exp.create_tasks(clear)
        self.__run(tasks)
        self.exp.populate_sum_table()

    def update_experiment(self, qids):
        tasks = []
        for qid in qids:
            path = self.exp.proj.get_path(qid)
            # TODO: handle overwrite
            log_check(self.exp.get_mutants(path) == [], 
                      f"experiment already exists for {path}")
            tasks.extend(self.exp.create_query_tasks(path))
        self.__run(tasks)
        self.exp.populate_sum_table()

    def fix_missing(self):
        mqids = self.exp.get_missing_qids()
        self.update_experiment(mqids)

    def __run(self, tasks):
        random.shuffle(tasks)

        for task in tasks:
            self.task_queue.put(task)

        log_info(f"running {len(tasks)} tasks")

        processes = []

        for i in range(self.exp.num_procs):
            worker = Worker(self.exp, i)
            p = mp.Process(target=run_tasks, 
                           args=(worker, self.task_queue,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

        log_info("workers finished")
