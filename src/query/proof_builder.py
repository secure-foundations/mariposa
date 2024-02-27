import os
import shutil
import subprocess
from solver.runner import CVC5Runner
from utils.system_utils import *

class ProofBuilder:
    def __init__(self, input_query, output_proof, timeout, clear=False):
        self.solver: CVC5Runner = CVC5Runner("cvc5_1_1_1")

        if not os.path.exists(input_query):
            log_warn(f"input query {input_query} does not exist")
            return

        self.input_query = input_query
        self.output_proof = output_proof
        # timeout in seconds
        assert timeout < 1000
        self.timeout = timeout

        name_hash = get_name_hash(input_query)

        self.opt_query = f"gen/{name_hash}.opt.smt2"

        if clear:
            self.clear(all=True)

    def run(self):
        self.__create_option_query()
        self.__run_solver()
        
    def clear(self, all=False):
        if os.path.exists(self.opt_query):
            os.remove(self.opt_query)

    def __create_option_query(self):
        if os.path.exists(self.opt_query):
            # we do not expect option query to change ...
            log_info(f"{self.opt_query} already exists")
            return

        lines = open(self.input_query).readlines()

        if not lines[-1].startswith("(check-sat)"):
            exit_with(f"input query {self.input_query} does not end with (check-sat)")

        pre = ["(set-option :produce-proofs true)\n"
                 "(set-option :proof-format-mode lfsc)"]
        
        post = [f"(set-option :regular-output-channel \"{self.output_proof}\")\n"
                    "(get-proof)\n"]

        lines = pre + lines + post
        
        with open(self.opt_query, "w") as opt_file:
            opt_file.writelines(lines)

        san_check(os.path.exists(self.opt_query), 
                    f"failed to create {self.opt_query}")

    def __run_solver(self):
        rcode, elapsed = self.solver.run(self.opt_query, self.timeout)
        print(rcode, elapsed)

        san_check(os.path.exists(self.output_proof), 
                f"failed to create {self.output_proof}")
