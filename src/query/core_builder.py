import os, random, subprocess
from base.solver import SolverType
from utils.local_utils import get_query_stability
from utils.query_utils import Mutation, emit_mutant_query
from utils.system_utils import *
from base.defs import MARIPOSA

class MutCoreBuilder:
    def __init__(self, input_query, output_query, solver, timeout, ids_available, restarts):
        log_check(os.path.exists(input_query), f"input query {input_query} does not exist")
        log_check(solver.stype == SolverType.Z3, f"only z3 solver is supported, got {solver}")
        self.solver = solver

        name_hash = get_name_hash(input_query)
        self.input_query = input_query
        self.lbl_query = f"gen/{name_hash}/lbl.smt2"
        self.lbl_mut_query = f"gen/{name_hash}/lbl.mut.smt2"
        self.core_log = f"gen/{name_hash}/z3-core.log"
        self.timeout = timeout
        self.output_query = output_query
        self.clear_temp_files()
        self.ids_available = ids_available
        self.restarts = restarts

        self.__create_label_query()

    def run(self):
        for i in range(self.restarts):
            remove_file(self.lbl_mut_query)
            remove_file(self.core_log)

            s = random.randint(0, 0xffffffffffffffff)
            emit_mutant_query(self.lbl_query, 
                              self.lbl_mut_query, 
                              Mutation.COMPOSE, s)

            with open(self.lbl_mut_query, "a") as f:
                f.write("(get-unsat-core)\n")

            success = self.__run_solver(seed=s)

            if success:
                log_info(f"core iteration {i}, successfully used mutant seed: {s}")
                self.__create_core_query(seed=s)
                # self.clear_temp_files()
                return True
            else:
                log_info(f"core iteration {i}, failed to use mutant seed: {s}")

        self.clear_temp_files()
        exit_with(f"failed to use mutants {self.solver} on {self.input_query}, no core log created")
        return False

    def clear_temp_files(self):
        remove_file(self.lbl_query)
        remove_file(self.lbl_mut_query)
        remove_file(self.core_log)

    def __create_label_query(self):
        remove_file(self.lbl_query)
        
        args = [
            MARIPOSA,
            "-i", self.input_query,
            "-o", self.lbl_query,
            "--action=label-core",
        ]

        if not self.ids_available:
            args.append("--reassign-ids")

        subprocess_run(args, check=True)

        # we do not expect labeling to fail
        log_check(os.path.exists(self.lbl_query), 
                  f"failed to create {self.lbl_query}")

    def __run_solver(self, seed):
        cf = open(self.core_log, "w+")
        start = time.time()
        args = self.solver.get_basic_command(
            self.lbl_mut_query, self.timeout, seed)
        subprocess.run(args, stdout=cf)
        cf.close()
        elapsed = time.time() - start
        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()
        log_info(f"elapsed: {elapsed} seconds")

        if len(lines) == 0 or "unsat\n" not in lines:
            os.remove(self.core_log)
            return False
        return True

    def __create_core_query(self, seed):
        subprocess_run([
            MARIPOSA,
            "-i", self.lbl_query,
            "--action=reduce-core",
            f"--core-log-path={self.core_log}",
            f"-o", self.output_query,
        ], check=True, debug=True)

        log_check(os.path.exists(self.output_query), f"failed to create core query {self.output_query}")

        with open(self.output_query, "a") as f:
            f.write(f'(set-info :comment seed_{seed})\n')

class CompleteCoreBuilder:
    def __init__(self, input_query, output_query, solver, timeout, ids_available, restarts):
        b = MutCoreBuilder(input_query, output_query, solver,  timeout, ids_available, restarts)
        out = b.run()
        get_query_stability(output_query, "debug")
