from projects import *
import json
from types import SimpleNamespace

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
    def __init__(self):
        self.name = "main"

        # what mutations do we use?
        self.enabled_muts = [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]

        # how many mutants to generate
        self.num_mutant = 60

        # how many processes do we use?
        self.num_procs = 7

        # do we keep the mutants after running?
        self.keep_mutants = False

        # how long do we wait? (seconds)
        self.timeout = 60

        # where do we store the db?
        self.db_path = None

        # what to do with existing table?
        self.db_mode = DBMode.UPDATE

        # # use a start seed if provided
        self.init_seed = None

    def load(self, obj):
        assert isinstance(obj, dict)

        if "exp_name" in obj:
            self.name = obj["exp_name"]
        
        if "mutations" in obj:
            self.enabled_muts = [Mutation(m) for m in obj["mutations"]]
            
        if "num_mutants" in obj:
            self.num_mutant = obj["num_mutants"]
            
        if "keep_mutants" in obj:
            self.keep_mutants = obj["keep_mutants"]

        if "exp_timeout" in obj:
            self.timeout = obj["exp_timeout"]

        if "db_path" in obj:
            self.db_path = obj["db_path"]
            
        if "db_mode" in obj:
            self.db_mode = DBMode(obj["db_mode"])

    def get_exp_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_exp"

    def get_sum_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_sum"

MAIN_EXP = ExpConfig()
MAIN_EXP.load(json.loads(open("configs/main_cfg.json").read()))
