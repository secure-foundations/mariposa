import os
from base.factory import FACT
from base.solver import CVC5Solver, RCode
from utils.system_utils import *

class ProofBuilder:
    def __init__(self, input_query, output_proof, timeout, clear=False):
        self.solver: CVC5Solver = FACT.get_solver_by_name("cvc5_1_1_1")

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
            self.clear(clear)

    def run(self):
        self.__create_option_query()
        self.__run_solver()
        
    def clear(self, all=False):
        if all and os.path.exists(self.opt_query):
            os.remove(self.opt_query)
        if os.path.exists(self.output_proof):
            os.remove(self.output_proof)

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

        log_check(os.path.exists(self.opt_query), 
                    f"failed to create {self.opt_query}")

    def __run_solver(self):
        rcode, elapsed = self.solver.run(self.opt_query, self.timeout)

        if rcode != RCode.UNSAT:
            self.clear(all=True)
            exit_with(f"failed to get proof for {self.input_query}")

        log_check(os.path.exists(self.output_proof), 
                f"failed to create {self.output_proof}")
