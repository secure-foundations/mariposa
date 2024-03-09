import os
from base.factory import FACT
from base.solver import CVC5Solver, RCode
from utils.system_utils import *

class InstBuilder:
    def __init__(self, input_query, output_proof, timeout, clear=False):
        self.solver: CVC5Solver = FACT.get_solver_by_name("cvc5_1_1_1")

        if not os.path.exists(input_query):
            log_warn(f"input query {input_query} does not exist")
            return

        self.output_proof = output_proof
        # timeout in seconds
        assert timeout < 1000
        self.timeout = timeout

        opts = [
            "--dump-instantiations"
        ]

        rcode, elapsed = self.solver.run(input_query, self.timeout, 
                out_file=output_proof, other_options=opts)

        if rcode != RCode.UNSAT:
            if os.path.exists(self.output_proof):
                os.remove(self.output_proof)
            exit_with(f"failed to get inst for {input_query}")

        log_check(os.path.exists(self.output_proof), 
                f"failed to create {self.output_proof}")
