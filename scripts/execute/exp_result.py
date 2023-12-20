from execute.solver_runner import RCode
import numpy as np
from tabulate import tabulate
from os import path

EXPECTED_CODES = [RCode.UNSAT, RCode.UNKNOWN, RCode.TIMEOUT]

class QueryExpResult:
    def __init__(self, query_path, proj_root, mutations, blob):
        self.base_name = path.basename(query_path)
        self.query_path = path.join(proj_root, self.base_name)
        self.mutations = mutations

        assert blob.shape[0] == len(mutations)
        assert blob.shape[1] == 2

        self.blob = blob

    def __str__(self):
        return f"query: {self.query_path}"
    
    def __hash__(self):
        return hash(self.query_path)

    def get_mutation_blob(self, mutation):
        index = self.mutations.index(mutation)
        return self.blob[index]

    def get_mutation_status(self, mutation):
        index = self.mutations.index(mutation)
        return self.blob[index][0], self.blob[index][1]

    def get_original_status(self):
        return self.blob[0][0][0], self.blob[0][1][0]

    def print_status(self):
        print(f"query path:\n\t'{self.query_path}'")
        table = [["mutation"] + [str(rc) for rc in EXPECTED_CODES] 
                 + ["mean", "std"]]
        v_rcode, v_time = self.get_original_status()
        print(f"{RCode(v_rcode)} in {v_time / 1000}s\n")

        for m in self.mutations:
            trow = [m]
            rcodes, times = self.get_mutation_status(m)
            rcs = RCode.empty_map()
            for rc in rcodes:
                rc = RCode(rc)
                assert rc in EXPECTED_CODES
                rcs[rc] += 1
            for rc in EXPECTED_CODES:
                trow.append(rcs[rc])

            times = times / 1000
            trow.append(round(np.mean(times), 2))
            trow.append(round(np.std(times), 2))
            table.append(trow)

        print(tabulate(table, headers="firstrow"))
        print("")
