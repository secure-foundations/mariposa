from debugger.demo_utils import *
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer
import math 

# r = Reviewer2(q)
# report = r.get_report()
# indices = report.freq.loc[report.freq["qname"].isin(report.stabilized["qname"])].index
# report.freq["rank"] = report.freq["trace_count"].rank(method='min', ascending=False)
# print(report.freq.loc[indices]["rank"].min())
# # print(tabulate(report, headers='keys', tablefmt='psql'))

def get_collision_prob(k, n):
    return 100 * (1 - math.exp(-k*(k-1)/(2*n)))

# print(get_collision_prob(89838, 2**32))

dbgs = []
for q in UNSTABLE_MARIPOSA:
    dbgs.append(Debugger3(q))

import multiprocessing
pool = multiprocessing.Pool(4)

pool.map(Debugger3.reset_proof_cache, dbgs)

# proof_path = "dbg/ba85c910da/proofs/reseed.1192914506473029201.proof"
# # tt = TermTable(proof_path)
# ProofAnalyzer.from_proof_file(proof_path, True)
# # # tt.pprint_node(tt.root_ref, 3)