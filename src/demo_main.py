from debugger.demo_utils import *
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer

# with open("run.sh", "a") as f:
#     for item in statuses["finished"]:
#         f.write("./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i " + item + "\n")

proof = "dbg/0f400a3f00/proofs/reseed.3861177451995363889.proof"
# pa = ProofParser(proof)
tt = TermTable(proof)
# pa = ProofAnalyzer(proof)
# tt.debug()
tt.pprint_node("ad30eaf9")
print(tt.is_proof_free("ad30eaf9"))
# pa = ProofAnalyzer.from_proof_file(proof)


