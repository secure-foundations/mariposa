from debugger.demo_utils import *
from debugger.symbol_table import TermTable
from debugger.tree_parser import ProofParser
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer
from debugger.proof_analyzer import ProofAnalyzer
import math 
import multiprocessing
import z3

q = "dbg/c4b6442111/"
r = Reviewer2(q)
r.collect_garbage()
