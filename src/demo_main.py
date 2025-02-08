from evaluator import Evaluator
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger.debugger import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer

q = "dbg/c4b6442111/"
r = Evaluator(q)
report = r.build_report()
print(report.freq)
# r.collect_garbage()
