from base.factory import FACT
from base.project import ProjectGroup, ProjectType as PT
from query.analyzer import QueryAnalyzer, Stability
from analysis.expr_analyzer import ExprAnalyzer
from enum import Enum
from utils.analysis_utils import *

# from base.exper import Experiment
class CoreIssue(Enum):
    BASE_UNSOLVABLE = "base_unsolvable"
    BASE_UNSTABLE = "base_unstable"
    CORE_UNSOLVABLE = "core_unsolvable"
    
    def __str__(self):
        return self.value

class CoreAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        base = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"))
        solver = FACT.get_solver_by_name("z3_4_12_2")
        base = FACT.load_experiment("default", base, solver)
        core = FACT.load_experiment("default", core, solver)
        base = ExprAnalyzer(base, ana)
        core = ExprAnalyzer(core, ana)
        
        issues = Categorizer()

        for qid in base.qids:
            bs = base.get_query_stability(qid)
            if qid not in core:
                issues.add_item((bs.value, "missing"), qid)
            elif core.get_query_stability(qid) == Stability.UNSOLVABLE:
                issues.add_item((bs.value, Stability.UNSOLVABLE.value), qid)
        issues.finalize()
        print("stable -> unsolvable")
        for i in issues[('stable', "unsolvable")]:
            print(base[i])

        print("unstable -> missing")
        for i in issues[('unstable', 'missing')]:
            print(base[i])

        issues.print_status()

