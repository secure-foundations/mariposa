from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from execute.exp_part import ExpPart
from analysis.categorizer import Categorizer
from configure.project import PM, ProjectType
from configure.solver import SolverInfo

def analyze_synth():
    solver = SolverInfo("z3_4_12_2")
    ptype = ProjectType("original")
    project = PM.load_project("v_nl", ptype)
    analyzer = Categorizer("60sec")
    
    exp = ExpPart("synthetic", 
            project, 
            solver)
    exp = ExpAnalyzer(exp, analyzer)
    
    # for basename in exp.base_names():
    #     if exp.get_stability(basename) == "unstable":
    #         print(basename, exp.get_stability(basename))
