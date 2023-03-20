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

# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-entry.i.dfyImpl___module.__default.lemma__userExecutionModel__sufficiency.smt2 1
# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-mapping.s.dfyCheckWellformed___module.__default.updateL2Pte.smt2 2
# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-secprop-conf_ni_entry.i.dfyImpl___module.__default.lemma__validEnclaveEx__conf.smt2 3
# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-secprop-sec_prop_util.i.dfyImpl___module.__default.lemma__user__regs__domain.smt2 4
# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-sha-sha256-body-16-xx.gen.dfyCheckWellformed___module.__default.va__refined__Body__16__XX.smt2 5
# ./run-script-smtcomp-current example/data/d_komodo_cvc5_clean/verified-valesupp.i.dfyCheckWellformed___module.__default.va__get__osp.smt2 6

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

class SolverTaskGroup:
    def __init__(self, cfg, vanilla_path, solver, remove_mut):
        self.vanilla_path = vanilla_path
        self.mutant_paths = []
        self.solver = solver
        assert isinstance(cfg, QueryExpConfig)
        self.cfg = cfg
        self.table_name = cfg.get_solver_table_name(self.solver)
        self.remove_mut = remove_mut

    def _run_single(self, query_path, perturb):
        assert (self.cfg.trials == 1)

        if self.solver.brand == SolverBrand.Z3:
            # -st
            command = f"{self.solver.path} {query_path} -T:{self.cfg.timeout}"
        else:
            assert (self.solver.brand == SolverBrand.CVC5)
            # --stats
            command = f"{self.solver.path} {query_path} -i --tlimit={self.cfg.timeout * 1000} --no-nl-cov --nl-ext=none --fmf-mbqi=none --no-mbqi --no-cbqi --no-cegqi"

        out, err, elapsed = subprocess_run(command, self.cfg.timeout + 1)

        # parse_basic_output_cvc

        if self.solver.brand == SolverBrand.Z3:
            rcode = parse_basic_output_z3(out)
        else:
            rcode = parse_basic_output_cvc(out, err)

        if rcode == "error":
            print(out, err)

        con = sqlite3.connect(self.cfg.db_path)
        cur = con.cursor()
        cur.execute(f"""INSERT INTO {self.table_name}
            (query_path, vanilla_path, perturbation, command, std_out, std_error, result_code, elapsed_milli)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?);""",
            (query_path, self.vanilla_path, perturb, command, out, err, rcode, elapsed))
        con.commit()
        con.close()
        return elapsed, rcode

    def run_pert_group(self, gen_path_pre, perturb):
        for _ in range(self.cfg.max_mutants):
            seed = random.randint(0, 0xffffffffffffffff)

            file_name = f"{str(seed)}.{perturb}.smt2"
            mutant_path = gen_path_pre.replace("smt2", file_name)
            command = f"{MARIPOSA_BIN_PATH} -i {self.vanilla_path} -p {perturb} -o {mutant_path} -s {seed}"

            # generate mutant
            result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
            if result.returncode != 0:
                print("[WARN] MARIPOSA failed: " + command)
                return

            elapsed, rcode = self._run_single(mutant_path, perturb)

            if self.remove_mut:
                # remove mutant
                os.system(f"rm {mutant_path}")
 
    def run(self):
        elapsed, rcode = self._run_single(self.vanilla_path, None)
        if rcode != "unsat":
            print("[WARN] vanilla not unsat: " + self.vanilla_path + " " + str(elapsed) + " milliseconds " + rcode)

        gen_path_pre = "gen/" + self.table_name + "/" + self.vanilla_path[5::]

        for perturb in self.cfg.enabled_muts:
            self.run_pert_group(gen_path_pre, perturb)

def run_group_tasks(queue, start_time):
    from datetime import timedelta
    from datetime import datetime
    init_size = queue.qsize()

    while True:
        task = queue.get()
        cur_size = queue.qsize()
        done_size = init_size - cur_size
        elapsed = round((time.time() - start_time) / 3600, 2)
        estimated = round(queue.qsize() * (elapsed / done_size), 2)

        print(f"finished: {done_size}/{init_size}, elapsed: {elapsed}, estimated: {datetime.now() + timedelta(hours=estimated)}")
        if task is None:
            break
        task.run()
    print("worker exit")

class Runner:
    def __init__(self, cfgs, override=False, remove_mut=True):
        for cfg in cfgs:
            assert isinstance(cfg, ExpConfig)
            self.__setup_tables(cfg, override)

        con = get_connection()
        con, cur = get_cursor()

        mp.set_start_method('spawn')
        self.task_queue = mp.Queue()

        if not remove_mut:
            print("[WARN] not removing generated mutant files!")

        print("loading tasks")
        tasks = []
        for cfg in cfgs:
            for solver, queries in cfg.samples.items():
                print(f"loading tasks {str(solver)}")
                for query in tqdm(queries):
                    task = SolverTaskGroup(cfg.qcfg, query, solver, remove_mut)
                    tasks.append(task)
        con.close()
        print("shuffling tasks")
        random.shuffle(tasks)
        for task in tasks:
            self.task_queue.put(task)

        # for proc exit
        for _ in range(cfg.num_procs):
            self.task_queue.put(None)
        processes = []

        print("starting solvers")

        for _ in range(cfg.num_procs):
            start_time = time.time()
            p = mp.Process(target=run_group_tasks, args=(self.task_queue, start_time, ))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

    def __setup_tables(self, cfg, override):
        con, cur = get_cursor(cfg.qcfg.db_path)
        ok = True

        for solver in cfg.samples:
            table_name = cfg.qcfg.get_solver_table_name(solver)
            if check_table_exists(cur, table_name):
                if override:
                    ok = confirm_drop_table(cur, table_name)
                    if not ok:
                        sys.exit()
                    create_experiment_table(cur, table_name)
                else:
                    print(f"[INFO] keep existing table {table_name}")
            else:
                create_experiment_table(cur, table_name)
        con.commit()
        con.close()
