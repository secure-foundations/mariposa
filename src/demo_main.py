from debugger.demo_utils import *
from debugger.tree_parser import ProofParser
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer


# with open("run.sh", "a") as f:
#     for item in statuses["finished"]:
#         f.write("./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i " + item + "\n")

proof = "dbg/1dbfa93b6f/proofs/shuffle.4136444131165753212.proof"
pa = ProofAnalyzer(proof)
pa.debug()
# pa = ProofAnalyzer.from_proof_file(proof)


