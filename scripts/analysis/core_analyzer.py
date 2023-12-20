from configure.project import ProjectGroup, ProjectType
from analysis.exp_analyzer import ExpAnalyzer
from execute.exp_part import ExpPart
from analysis.categorizer import Categorizer 

class CoreAnalyzer:
    def __init__(self, gp):
        exp = gp.load_project(ProjectType.UNSAT_CORE)
        exp = ExpPart("unsat_core", exp, "z3_4_12_2")
        # self.orig = ExpAnalyzer(gp.load_project(ProjectType.ORIGINAL)
        self.core = ExpAnalyzer(exp)
        ana = Categorizer("default")
        self.core.print_stability_stats(ana)
        # self.extd = gp.load_project(ProjectType.UNSAT_CORE_EXT)
