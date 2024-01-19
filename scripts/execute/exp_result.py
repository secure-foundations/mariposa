from execute.solver_runner import RCode
from utils.sys_utils import san_check
import numpy as np
from tabulate import tabulate
from os import path

EXPECTED_CODES = [RCode.UNSAT, RCode.UNKNOWN, RCode.TIMEOUT]

# def _enforce_timeout(blob, timeout):
#     assert timeout > 1000
#     assert blob.shape[0] == 2
 

class QueryExpResult:
    def __init__(self, query_path, proj_root, mutations=[], blob=None):
        self.base_name = path.basename(query_path)
        self.query_path = path.join(proj_root, self.base_name)
        self.mutations = mutations

        if blob is not None:        
            assert blob.shape[0] == len(mutations)
            assert blob.shape[1] == 2

        self.timeout = None

        self.blob = blob

    def __str__(self):
        return f"query: {self.query_path}"
    
    def __hash__(self):
        return hash(self.query_path)

    def get_mutation_blob(self, mutation):
        index = self.mutations.index(mutation)
        return self.blob[index]

    def get_mutation_status(self, mutation):
        # print(self.mutations)
        index = self.mutations.index(mutation)
        return self.blob[index][0], self.blob[index][1]

    def get_original_status(self):
        return self.blob[0][0][0], self.blob[0][1][0]

    def enforce_timeout(self, timeout):
        assert timeout > 1000
        if np.isinf(timeout):
            return
        new_blobs = np.copy(self.blob)
        for index in range(len(self.mutations)):
            old_blob = self.blob[index]
            new_blob = new_blobs[index]
            new_blob[0][old_blob[1] > timeout] = RCode.TIMEOUT.value
            new_blob[1][old_blob[1] > timeout] = timeout
        self.blob = new_blobs
        self.timeout = timeout
    
    # def find_sus(self):
    #     rcs, qtms = self.get_mutation_status("quake")
    #     _, stms = self.get_mutation_status("shuffle")
    #     if np.mean(stms)/np.mean(qtms)> 50:
    #         print(np.mean(stms)/np.mean(qtms))

    def print_status(self):
        print(f"[INFO] to copy query path:\ncp '{self.query_path}' temp/woot.smt2")
        if self.timeout != None:
            print(f"[INFO] alternative timeout: {self.timeout/1000}s")
        table = [["mutation"] + [str(rc) for rc in EXPECTED_CODES] 
                 + ["mean", "std"]]
        v_rcode, v_time = self.get_original_status()
        print(f"\nplain query {RCode(v_rcode)} in {v_time / 1000}s")

        for m in self.mutations:
            trow = [m]
            rcodes, times = self.get_mutation_status(m)
            rcs = RCode.empty_map()

            for rc in rcodes:
                rc = RCode(rc)
                if rc not in EXPECTED_CODES:
                    print(f"[WARN] unexpected rcode '{rc}' in {self.query_path}")
                rcs[rc] += 1
            for rc in EXPECTED_CODES:
                trow.append(rcs[rc])

            times = times / 1000
            trow.append(round(np.mean(times), 2))
            trow.append(round(np.std(times), 2))
            table.append(trow)

        print(tabulate(table, headers="firstrow"))
