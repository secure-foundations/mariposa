from tabulate import tabulate
from configure.project import PM
from analysis.core_analyzer import analyze_unsat_core
from analysis.bloat_analyzer import analyze_bloat
from analysis.reval_analyzer import analyze_reveal
from analysis.synth_analyzer import analyze_synth
from analysis.basic_analyzer import GroupAnalyzer
from analysis.categorizer import Categorizer

# from analysis.basic_analyzer import ExpAnalyzer
# from execute.exp_part import ExpPart
# from configure.solver import SolverInfo
from utils.analyze_utils import *
import matplotlib.pyplot as plt
from scipy.stats import gmean

def analyze_recollect():
    ana = Categorizer("60sec")
    g = GroupAnalyzer("v_uf", ana)
    # cats = g.orig.get_stability_status()
    # cats.print_status(skip_empty=True)
    names = g.orig.base_names()
    import random 
    names = set(random.sample(names, 100))
    print(len(names))

    sample_cats = CategorizedItems()

    for base_name in names:
        # qr = g.orig[base_name]
        sample_cats.add_item(g.orig.get_stability(base_name), base_name)
    
    sample_cats.finalize()
    sample_cats.print_status(skip_empty=True)
        # print(base_name)
    # for base_name in g.orig.base_names():
    #     print(base_name)
        # if qr.is_unsat():
        #     print(qr.base_name)

if __name__ == "__main__":
    analyze_unsat_core()
    # analyze_synth()
    # analyze_bloat()
    # analyze_reveal()
    # analyze_recollect()