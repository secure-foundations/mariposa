from configs.projects import *

DB_PATH = "data/mariposa.db"

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    RSEED = "rseed"
    # LOWER_SHUFFLE = "lower_shuffle"

    def __str__(self):
        return str.__str__(self)

class DBMode(Enum):
    # update the existing table, create if none exists
    UPDATE = "update"
    # create new table, drop the existing one if exists
    CREATE = "create"

class ExpConfig:
    def __init__(self, name, db_path):
        self.name = name

        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at most
        self.max_mutants = 60

        # how long do we wait? (seconds)
        self.timeout = 60

        # what mutations do we use?
        self.enabled_muts = [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RSEED]

        # how many processes do we use?
        self.num_procs = 7
        
        # do we remove the mutants after running?
        self.remove_mut = True
        
        # where do we store the db?
        self.db_path = db_path

        # what to do with existing table?
        self.db_mode = DBMode.UPDATE
        
        # use a start seed if provided
        self.init_seed = None

    def get_exp_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_exp"

    def get_sum_name(self, project, solver):
        return f"{self.name}_{project.name}_{str(solver)}_sum"
