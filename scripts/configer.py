import os, random
from basic_utils import *
import json
from enum import Enum
from analyzer import Analyzer

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

class SolverInfo:
    def __init__(self, name, date, path):
        self.name = name
        self.date = date
        self.path = path
        exit_with_on_fail(os.path.exists(self.path), f"[ERROR] solver binary {self.path} does not exist")

    def __str__(self):
        return scrub(self.name).lower()

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return hash(self) == hash(other)

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    RESEED = "reseed"
    # LOWER_SHUFFLE = "lower_shuffle"

    def __str__(self):
        return str.__str__(self)

class DBMode(Enum):
    # update the existing table, create if none exists
    UPDATE = "update"
    # create new table, drop the existing one if exists
    CREATE = "create"

class ExpConfig:
    def __init__(self, name, enabled_muts, num_mutant, num_procs, keep_mutants, timeout, db_path, db_mode, init_seed):
        self.name = name

        # what mutations do we use?
        self.enabled_muts = enabled_muts

        # how many mutants to generate
        self.num_mutant = num_mutant

        # how many processes do we use?
        self.num_procs = num_procs

        # do we keep the mutants after running?
        self.keep_mutants = keep_mutants

        # how long do we wait? (seconds)
        self.timeout = timeout

        # where do we store the db?
        self.db_path = db_path

        # what to do with existing table?
        self.db_mode = db_mode

        # use a start seed if provided
        self.init_seed = None if init_seed == "" else int(init_seed)

    def get_exp_tname(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_exp"

    def get_sum_tname(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_sum"

class Configer:
    def __init__(self, path="configs.json"):
        f = open(path)
        objs = json.loads(f.read())

        self.solvers = dict()
        for obj in objs["solvers"]:
            self.solvers[obj["name"]] = SolverInfo(obj["name"], obj["date"], obj["path"])

        self.projects = dict()
        for obj in objs["projects"]:
            solver = obj["artifact_solver_name"]
            exit_with_on_fail(solver in self.solvers, f"[ERROR] unknown artifact solver {solver} for project {obj['name']}")
            self.projects[obj["name"]] = ProjectInfo(obj["name"], obj["clean_dir"], solver)

        self.analyzers = dict()
        for obj in objs["analyzers"]:
            self.analyzers[obj["name"]] = Analyzer(obj["confidence"], obj["ana_timeout"],obj["r_solvable"], obj["r_stable"], obj["discount"])

        self.exps = dict()
        for obj in objs["experiments"]:
            mutations = [Mutation(m) for m in obj["mutations"]]
            self.exps[obj["name"]] = ExpConfig(obj["name"], mutations, obj["num_mutants"], obj["num_procs"], obj["keep_mutants"], obj["exp_timeout"], obj["db_path"], DBMode(obj["db_mode"]), obj["init_seed"])

    def load_known_experiment(self, name):
        exit_with_on_fail(name in self.exps, f"[ERROR] unknown experiment {name}")
        return self.exps[name]

    def load_known_project(self, name):
        exit_with_on_fail(name in self.projects, f"[ERROR] unknown project {name}")
        return self.projects[name]
    
    def load_known_solver(self, name):
        exit_with_on_fail(name in self.solvers, f"[ERROR] unknown solver {name}")
        return self.solvers[name]
    
    def load_known_analyzer(self, name):
        exit_with_on_fail(name in self.analyzers, f"[ERROR] unknown analyzer {name}")
        return self.analyzers[name]