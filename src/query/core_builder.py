import os
import subprocess
from utils.system_utils import *

MARIPOSA_BIN = "src/smt2action/target/release/mariposa" 

class BasicCoreBuilder:
    def __init__(self, input_query, solver, output_query, timeout, clear=False):
        self.solver_path = solver.path
        assert timeout < 1000

        if not os.path.exists(input_query):
            log_warn(f"input query {input_query} does not exist")
            return

        self.input_query = input_query
        self.output_query = output_query
        self.timeout = timeout

        name_hash = get_name_hash(input_query)

        self.lbl_query = f"gen/{name_hash}.lbl.smt2"
        self.core_log = f"gen/{name_hash}.core"

        if clear:
            self.clear(all=True)

    def run(self):
        self.__create_label_query()
        self.__run_solver()
        self.__create_core_query()

    def clear(self, all=False):
        if os.path.exists(self.lbl_query):
            os.remove(self.lbl_query)
        if os.path.exists(self.core_log):
            os.remove(self.core_log)
        if all and os.path.exists(self.output_query):
            os.remove(self.output_query)

    def __create_label_query(self):
        if os.path.exists(self.lbl_query):
            # we do not expect labelled query to change ...
            log_info(f"{self.lbl_query} already exists")
            return

        subprocess.run([
            MARIPOSA_BIN,
            "-i", self.input_query,
            "-o", self.lbl_query, 
            "--action=label-core",
        ])

        # we do not expect labeling to fail
        if not os.path.exists(self.lbl_query):
            exit_with(f"failed to create {self.lbl_query}")

    def __run_solver(self):
        if os.path.exists(self.core_log):
            log_info(f"{self.core_log} already exists")
            os.remove(self.core_log)

        cf = open(self.core_log, "w+")
        subprocess.run([
            self.solver_path,
            self.lbl_query,
            f"-T:{self.timeout}"],
            stdout=cf)
        cf.close()

        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()

        if len(lines) <= 1 or "unsat\n" not in lines:
            os.remove(self.core_log)
            exit_with(f"failed to run {self.solver_path} on {self.lbl_query}, no core log created")

    def __create_core_query(self):
        if os.path.exists(self.output_query):
            log_info(f"core query {self.output_query} already exists")
            return

        subprocess.run([
            MARIPOSA_BIN,
            "-i", self.lbl_query,
            "--action=reduce-core",
            f"--core-log-path={self.core_log}",
            f"-o", self.output_query,
        ])

        if os.path.exists(self.output_query):
            # clear temp files
            self.clear()
        else:
            exit_with(f"failed to create core query {self.output_query}")
