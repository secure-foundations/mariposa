import sys, os, subprocess
import multiprocessing as mp
import time
import random
import scipy.stats as stats
import numpy as np
import math

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
    def __init__(self, qcfg, original_query, perturb, solver):
        self.qcfg = qcfg
        self.solver = solver
        self.original_query = original_query
        self.perturb = perturb

    def run(self):
        seed = random.randint(0, 0xffffffffffffffff)
        solver = self.solver
        qcfg = self.qcfg
        
        table_name = qcfg.get_solver_table_name(self.solver)
        if self.perturb is not None:
            gen_path_pre = "gen/" + table_name + "/" + self.original_query[5::]
            file_name = f"{str(seed)}.{self.perturb}.smt2"
            mutant_path = gen_path_pre.replace("smt2", file_name)

            command = f"{MARIPOSA_BIN_PATH} -i {self.original_query} -p {self.perturb} -o {mutant_path} -s {seed}"

            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)

            if result.returncode != 0:
                print("[ERROR] MARIPOSA failed: " + command)
                return
        else:
            mutant_path = self.original_query

        if solver.brand == SolverBrand.Z3:
            command = f"{solver.path} {mutant_path} -T:{qcfg.timeout}"
        else:
            assert (solver.brand == SolverBrand.CVC5)
            command = f"{solver.path} {mutant_path} -i --tlimit={qcfg.timeout * 1000} --no-nl-cov --nl-ext=none --fmf-mbqi=none --no-mbqi --no-cbqi --no-cegqi"

        out, err, elapsed = subprocess_run(command, qcfg.timeout + 1)

        if solver.brand == SolverBrand.Z3:
            rcode = parse_basic_output_z3(out)
        else:
            rcode = parse_basic_output_cvc(out, err)

        if rcode == "error":
            print(out, err)

        if qcfg.remove_mut and self.perturb is not None:
            # remove mutant
            os.system(f"rm {mutant_path}")
        
        con = sqlite3.connect(qcfg.db_path)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {table_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (mutant_path, self.original_query, self.perturb, command, out, err, rcode, elapsed))
        con.commit()
        con.close()
        # print(rcode, elapsed)

def run_tasks(queue, start_time):
    from datetime import timedelta
    from datetime import datetime
    init_size = queue.qsize()

    while True:
        task = queue.get()
        cur_size = queue.qsize()
        done_size = init_size - cur_size
        if done_size % 100 == 0:
            elapsed = round((time.time() - start_time) / 3600, 2)
            estimated = round(cur_size * (elapsed / done_size), 2)
            print(f"finished: {done_size}/{init_size}, elapsed: {elapsed} hours, estimated: {datetime.now() + timedelta(hours=estimated)}")
        if task is None:
            break
        task.run()
    print("[INFO] worker exit")

def setup_table(qcfg, solver):
    con, cur = get_cursor(qcfg.db_path)
    table_name = qcfg.get_solver_table_name(solver)
    if check_table_exists(cur, table_name):
        if qcfg.overwrite:
            ok = confirm_drop_table(cur, table_name)
            if not ok:
                print(f"[INFO] keep existing table {table_name}")
                sys.exit()
    create_experiment_table(cur, table_name)
    con.commit()
    con.close()

def print_single_status(summary_table):
    classifier = Classifier("z_test")
    classifier.timeout = 6e4 # 1 min

    con, cur = get_cursor(qcfg.db_path)
    res = cur.execute(f"""SELECT * FROM {summary_table}""")
    rows = res.fetchall()
    con.close()

    assert len(rows) == 1
    row = rows[0]
    
    mut_size = qcfg.max_mutants
    perturbs = ast.literal_eval(row[1])
    blob = np.frombuffer(row[2], dtype=int)
    blob = blob.reshape((len(perturbs), 2, mut_size + 1))
    status, votes = classifier.categorize_query(blob)

    print("")
    print("overall:", status)
    print("original:")
    print("\tresult:", RCode(blob[0][0][0]))
    print("\ttime:", round(blob[0][1][0]/1000, 2), "(s)")
    for i in range(len(perturbs)):
        count = count_within_timeout(blob[i], RCode.UNSAT, timeout=classifier.timeout)
        times = np.clip(blob[i][1], 0, classifier.timeout) / 1000
        print(f"{perturbs[i]}: {votes[i]}")
        print("\tsuccess:", f"{count}/{mut_size+1}")
        print("\tmean:", round(np.mean(times), 2), "(s)")
        print("\tstd:", round(np.std(times), 2), "(s)")

class Runner:
    def __init__(self) -> None:
        mp.set_start_method('spawn')
        self.task_queue = mp.Queue()

    def _add_single_exp(self, qcfg, original_query, solver):
        task = Task(qcfg, original_query, None, solver)
        self.task_queue.put(task)

        for perturb in qcfg.enabled_muts:
            for _ in range(qcfg.max_mutants):
                task = Task(qcfg, original_query, perturb, solver)
                self.task_queue.put(task)

    def _setup_tables(self, qcfgs, solvers):
        for qcfg in qcfgs:
            for solver in solvers:
                setup_table(qcfg, solver)

    def _run_workers(self, num_procs):
        start_time = time.time()
        processes = []
        for _ in range(num_procs):
            p = mp.Process(target=run_tasks, args=(self.task_queue, start_time,))
            p.start()
            processes.append(p)
            self.task_queue.put(None)

        for p in processes:
            p.join()

    def run_single_exp(self, qcfg, original_query, solver):
        self._setup_tables(self, [qcfg], [solver])
        self._add_single_exp(original_query, solver)
        self._run_workers(qcfg.num_procs)
        summary_table = build_solver_summary_table(qcfg, Z3_4_12_1)
        print_single_status(summary_table)
        
    def run_multi_exps(self, qcfgs, solvers):
        import itertools
        self._setup_tables(qcfgs, solvers)

        for qcfg, solver in itertools.product(qcfgs, solvers):
            for original_query in qcfg.project.list_queries(10):
                self._add_single_exp(qcfg, original_query, solver)
        print(f"[INFO] total tasks: {self.task_queue.qsize()}")
        self._run_workers(qcfg.num_procs)
        print(f"[INFO] start post processing")
        for qcfg, solver in itertools.product(qcfgs, solvers):
            build_solver_summary_table(qcfg, Z3_4_12_1)

if __name__ == '__main__':
    # qcfg = QueryExpConfig("test", S_KOMODO, "./data/test.db")
    # qcfg.overwrite = True
    # r = Runner()
    # r.run_multi_exps([qcfg], [Z3_4_12_1])
    # qcfg.overwrite = True
    # run_single_exp(qcfg, "data/d_komodo_z3_clean/verified-words_and_bytes.s.dfyCheckWellformed___module.__default.BEUintToSeqByte.smt2", Z3_4_12_1)
    pass

# from analyzer import RCode 
# from analyzer import Classifier
# from analyzer import Stability
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
#     classifier = Classifier("z_test")
#     classifier.timeout = 6e4 # 1 min

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

#     cat = classifier.categorize_query(blob)

#     print(blob)
#     print(cat)

#     if cat == Stability.STABLE:
#         exit(0) # good
#     if cat == Stability.INCONCLUSIVE:
#         exit(125) # skip
#     exit(1) # bad 

# if __name__ == "__main__":
#     mariposa(sys.argv[1])