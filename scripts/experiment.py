from project import *
from analyzer import Analyzer
import json
from enum import Enum

DB_PATH = "data/mariposa.db"

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

    def get_exp_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_exp"

    def get_sum_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_sum"

def load_known_experiment(name):
    with open("configs/experiments.json", "r") as f:
        objs = json.loads(f.read())
        for obj in objs:
            if obj["name"] != name: continue
            mutations = [Mutation(m) for m in obj["mutations"]]
            cfg =ExpConfig(obj["name"], mutations, obj["num_mutants"], obj["num_procs"], obj["keep_mutants"], obj["exp_timeout"], obj["db_path"], DBMode(obj["db_mode"]), obj["init_seed"])
            ana = Analyzer(obj["confidence"], obj["ana_timeout"],obj["r_solvable"], obj["r_stable"], obj["discount"])
            return cfg, ana
    exit_with(f"[ERROR] unknown experiment {name}")
