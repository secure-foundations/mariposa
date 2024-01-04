from tabulate import tabulate
from configure.project import PM
from analysis.core_analyzer import analyze_unsat_core
from analysis.bloat_analyzer import analyze_bloat
from analysis.reval_analyzer import analyze_reveal
# from analysis.basic_analyzer import ExpAnalyzer
# from execute.exp_part import ExpPart
# from configure.solver import SolverInfo
from utils.analyze_utils import *
import matplotlib.pyplot as plt
from scipy.stats import gmean

if __name__ == "__main__":
    analyze_unsat_core()
    # analyze_bloat()
    # analyze_reveal()
