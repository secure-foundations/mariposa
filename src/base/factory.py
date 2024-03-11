import json, os, copy
from typing import List 
from base.defs import *
from base.exper import ExpConfig, Experiment
from base.project import Project, ProjectGroup, ProjectType
from base.solver import CVC5Solver, Solver, Z3Solver
from utils.system_utils import exit_with, log_check, reset_dir

from base.defs import SOLVER_CONFIG_PATH

class Factory:
    def __init__(self):
        self.all_solvers = dict()
        self.__init_solvers()

        self.all_configs = dict()
        self.__init_configs()

        self.groups = None

    def __init_solvers(self):
        objs = json.loads(open(SOLVER_CONFIG_PATH).read())
        for solver_name, solver_obj in objs.items():
            if solver_name.startswith("z3"):
                s = Z3Solver(solver_name, solver_obj)
            elif solver_name.startswith("cvc5"):
                s = CVC5Solver(solver_name, solver_obj)
            else:
                assert False
            self.all_solvers[solver_name] = s

    def __init_configs(self):
        objs = json.loads(open(EXPER_CONFIG_PATH).read())
        default = objs["default"]
        for name, obj in objs.items():
            cur = copy.deepcopy(default)
            cur.update(obj)
            self.all_configs[name] = ExpConfig(name, cur)

    def __init_projects(self):
        self.groups = dict()
        for gid in os.listdir(PROJ_ROOT):
            self.groups[gid] = ProjectGroup(gid, PROJ_ROOT + gid)

    def get_solver_by_name(self, name) -> Solver:
        log_check(name in self.all_solvers, f"no such solver {name}")
        return self.all_solvers[name]
    
    def get_solver_by_path(self, path) -> Solver:
        for s in self.all_solvers.values():
            if s.path == path:
                return s
        exit_with(f"no such solver with path {path} configured in {SOLVER_CONFIG_PATH}!")

    def get_config_by_name(self, name) -> ExpConfig:
        log_check(name in self.all_configs, f"no such configuration {name}")
        return self.all_configs[name]

    def __get_project(self, gid, ptype: ProjectType) -> Project:
        group = self.groups.get(gid)
        log_check(group, f"no such project group {gid}")
        proj = group.get_project(ptype)
        log_check(proj, f"no such sub-project {ptype} under {gid}")
        return proj
    
    def get_group_by_path(self, path) -> ProjectGroup:
        if self.groups is None:
            self.__init_projects()
        items = os.path.normpath(path).split(os.sep)[-1:]
        log_check(len(items) == 1, f"invalid group path {path}")
        return self.groups.get(items[0])
    
    def get_project_by_path(self, path) -> Project:
        if self.groups is None:
            self.__init_projects()
        log_check(path.startswith(PROJ_ROOT), f"invalid path {path}")
        items = os.path.normpath(path).split(os.sep)[-2:]
        log_check(len(items) == 2, f"invalid project path {path}")
        ptype = ProjectType.from_str(items[1])
        log_check(ptype, f"invalid project type {items[1]}")
        return self.__get_project(items[0], ptype)

    def get_project_groups(self):
        if self.groups is None:
            self.__init_projects()
        for pg in sorted(self.groups.values()):
            yield pg

    @staticmethod
    def _build_single_mode_project(query_path) -> Project:
        log_check(query_path.endswith(".smt2"),
                        'query must end with ".smt2"')
        query_path = query_path.replace(".smt2", "")
        reset_dir(SINGLE_MUT_ROOT, True)
        return Project("single", single_mode=True)

    @staticmethod
    def build_single_mode_exp(cfg_name, query_path, solver: Solver) -> Experiment:
        cfg = FACT.get_config_by_name(cfg_name)
        proj = Factory._build_single_mode_project(query_path)
        return Experiment(cfg, proj, solver)

    def build_experiment(self, cfg_name, proj: Project, solver: Solver) -> Experiment:
        cfg = FACT.get_config_by_name(cfg_name)
        return Experiment(cfg, proj, solver)

    def get_project_exps(self, proj: Project) -> List[Experiment]:
        cfgs = self.all_configs.values()
        solvers = self.all_solvers.values()
        exps = []
        for cfg in cfgs:
            for solver in solvers:
                exp = Experiment(cfg, proj, solver)
                if exp.sum_table_exists():
                    exps.append(exp)
        return exps
    
    # def switch_solver(self, proj: Project) -> Project:
    #     _ = self.__get_project(proj.gid, proj.ptype)
    #     return Project(proj.gid, proj.ptype.switch_solver())

FACT = Factory()