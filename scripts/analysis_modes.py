from configure.project import ProjectManager
from analysis.core_analyzer import CoreAnalyzer

def analysis_main(args):
    m = ProjectManager()
    g = m.load_project_group("d_komodo")
    CoreAnalyzer(g)
