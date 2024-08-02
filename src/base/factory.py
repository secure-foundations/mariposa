import json, os, copy
import sys
from typing import List
from base.defs import *
from base.exper import ExpConfig, Experiment
from base.exper_analyzer import ExperAnalyzer
from base.project import Project, ProjectGroup, ProjectType
from base.solver import CVC5Solver, Solver, Z3Solver
from base.query_analyzer import QueryAnalyzer
from utils.system_utils import (
    exit_with,
    get_name_hash,
    list_smt2_files,
    log_check,
    log_info,
    log_warn,
    reset_dir,
    subprocess_run,
)


class Factory:
    def __init__(self):
        self.all_solvers = dict()
        self.__init_solvers()

        self.all_configs = dict()
        self.__init_configs()

        self.analyzers = dict()
        self.__init_analyzer()

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

    def __init_analyzer(self):
        objs = json.loads(open(ANALYZER_CONFIG_PATH).read())
        default = objs["default"]
        for name, obj in objs.items():
            cur = copy.deepcopy(default)
            cur.update(obj)
            self.analyzers[name] = QueryAnalyzer(name, cur)

    def get_solver(self, name) -> Solver:
        log_check(name in self.all_solvers, f"no such solver {name}")
        return self.all_solvers[name]

    def get_solver_by_path(self, path) -> Solver:
        for s in self.all_solvers.values():
            if s.path == path:
                return s
        exit_with(
            f"no such solver with path {path} configured in {SOLVER_CONFIG_PATH}!"
        )

    def get_config(self, name) -> ExpConfig:
        log_check(name in self.all_configs, f"no such configuration {name}")
        return self.all_configs[name]

    def __get_project(self, gid, ptype: ProjectType) -> Project:
        group = self.groups.get(gid)
        log_check(group, f"no such project group {gid}")
        proj = group.get_project(ptype)
        log_check(proj, f"no such sub-project {ptype} under {gid}")
        return proj

    def get_group(self, gid) -> ProjectGroup:
        if self.groups is None:
            self.__init_projects()
        return self.groups[gid]

    def get_group_by_path(self, path) -> ProjectGroup:
        if self.groups is None:
            self.__init_projects()
        items = os.path.normpath(path).split(os.sep)
        res = self.groups.get(items[-1])
        if res:
            return res
        res = self.groups.get(items[-2])
        if res:
            return res
        exit_with(f"no such project group associated with path {path}")

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

    def get_analyzer(self, name) -> QueryAnalyzer:
        log_check(name in self.analyzers, f"no such analyzer {name}")
        return self.analyzers[name]

    @staticmethod
    def get_single_project(query_path, skip_split=False, clear=False) -> Project:
        log_check(query_path.endswith(".smt2"), 'query must end with ".smt2"')
        name_hash = get_name_hash(query_path)
        proj = Project("single_" + name_hash, single_mode=True)

        if not clear and len(proj.qids) != 0:
            return proj

        sub_root = proj.sub_root

        reset_dir(sub_root, clear)

        if skip_split:
            subprocess_run(f"cp {query_path} {sub_root}/", shell=True, check=True)
        else:
            command = f"{MARIPOSA} -i '{query_path}' -o {sub_root}/split.smt2 -a split --convert-comments"
            subprocess_run(command, shell=True, check=True)

        proj.reload()

        if len(proj.qids) == 0:
            log_info(f"no queries were generated from {query_path}")
            sys.exit(0)

        return proj

    @staticmethod
    def get_single_exper(
        query_path, cfg: ExpConfig, solver: Solver, skip_split=False, clear=False
    ) -> Experiment:
        log_check(query_path.endswith(".smt2"), 'query must end with ".smt2"')
        proj = Factory.get_single_project(query_path, skip_split, clear)
        return Experiment(proj, cfg, solver)

    def get_exper(
        self, proj: Project, cfg: ExpConfig, solver: Solver, build=False
    ) -> Experiment:
        exp = Experiment(proj, cfg, solver)
        if not build:
            log_check(exp.is_done(), "experiment results do not exist")
        return exp

    def get_available_expers(self, proj: Project) -> List[Experiment]:
        cfgs = self.all_configs.values()
        solvers = self.all_solvers.values()
        exps = []
        for cfg in cfgs:
            for solver in solvers:
                exp = Experiment(proj, cfg, solver)
                if exp.is_done():
                    exps.append(exp)
        return exps

    def load_analysis(
        self,
        proj: Project,
        cfg: ExpConfig,
        solver: Solver,
        ana: QueryAnalyzer,
        allow_missing_exper=False,
        group_qids=None,
    ) -> ExperAnalyzer:
        exp = self.get_exper(proj, cfg, solver, allow_missing_exper)
        return ExperAnalyzer(exp, ana, allow_missing_exper, group_qids)

    def load_any_analysis(self, proj: Project, ana: QueryAnalyzer, group_qids=None) -> ExperAnalyzer:
        exps = self.get_available_expers(proj)
        if len(exps) == 0:
            log_warn(f"no available experiments for {proj.full_name}, returning a dummy")
            return self.load_default_analysis(proj, group_qids=group_qids)
        return ExperAnalyzer(exps[0], ana, group_qids=group_qids)

    def load_default_analysis(self, proj: Project, group_qids=None) -> ExperAnalyzer:
        solver = self.get_solver("z3_4_12_5")
        cfg = self.get_config("default")
        ana = self.get_analyzer("60nq")
        return self.load_analysis(
            proj, cfg, solver, ana, allow_missing_exper=True, group_qids=group_qids
        )


FACT = Factory()
