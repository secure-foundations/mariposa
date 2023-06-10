import os, random
from basic_utils import *
from solver import *
import json

def solver_from_path(spath):
    path = os.path.abspath(spath)
    for s in KNOWN_SOLVERS.values():
        if os.path.abspath(s.path) == path:
            return s
    s = SolverInfo("unknown_solver", "0.0.0", "1970/01/01", path)
    print(f"[INFO] {spath} does not matches any known solver")
    return s

class ProjectInfo:
    def __init__(self, name, clean_dir, artifact_solver):
        self.name = name
        self.clean_dir = clean_dir
        self.artifact_solver = artifact_solver

    def list_queries(self, size=None):
        queries = list_smt2_files(self.clean_dir)
        if size is None:
            return queries
        return random.sample(queries, size)

def load_known_projects():
    projects = dict()
    with open("configs/projects.json") as f:
        objs = json.loads(f.read())
        for obj in objs:
            solver = solver_from_path(obj["artifact_solver_path"])
            p = ProjectInfo(obj["name"], obj["clean_dir"], solver)
            projects[p.name] = p
    return projects

KNOWN_PROJECTS = load_known_projects()

S_KOMODO = KNOWN_PROJECTS["s_komodo"]
D_KOMODO = KNOWN_PROJECTS["d_komodo"]
D_FVBKV = KNOWN_PROJECTS["d_fvbkv"]
D_LVBKV = KNOWN_PROJECTS["d_lvbkv"]
FS_VWASM = KNOWN_PROJECTS["fs_vwasm"]
FS_DICE = KNOWN_PROJECTS["fs_dice"]

MAIN_PROJS = [S_KOMODO, D_KOMODO, D_FVBKV, D_LVBKV, FS_VWASM, FS_DICE]
