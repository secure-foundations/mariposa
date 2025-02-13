from benchmark_consts import UNSTABLE_MARIPOSA
from evaluator import Evaluator
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger.debugger import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer
from tqdm import tqdm

proof = "dbg/d8c62df78c/proofs/reseed.1276847554444104271.proof"

tt = TermTable(proof)

for qref in tt.quant_refs:
    tt.pprint_node(qref)
