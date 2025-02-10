from benchmark_consts import UNSTABLE_MARIPOSA
from evaluator import Evaluator
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger.debugger import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer
from tqdm import tqdm

cmds = []

for q in tqdm(UNSTABLE_MARIPOSA):
    # if dbg.get_status()["proofs"] == 0:
    #     continue
    # # cmds.append(f"./src/debuggers.py -i {q} --register-singleton")
    # dbg.check_singleton()
    # d = Debugger3(q)
    rev = Evaluator(q)
    # rev.collect_garbage()

# print("\n".join(cmds))
