from configs.projects import *

DB_PATH = "data/mariposa.db"

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    # SSEED = "sseed"
    # SMT_SEED = "smt_seed"
    # SAT_SEED = "sat_seed"
    RSEED = "rseed"
    LOWER_SHUFFLE = "lower_shuffle"

    def __str__(self):
        return str.__str__(self)

class QueryExpConfig:
    def __init__(self, name, project, db_path):
        self.name = name

        self.project = project
        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at most
        self.max_mutants = 60

        # how long do we wait? (seconds)
        self.timeout = 60

        self.enabled_muts = [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RSEED]

        self.db_path = db_path

        self.num_procs = 7
        
        self.remove_mut = True
        
        self.overwrite = False
        
    def get_solver_table_name(self, solver):
        # assert (solver in self.samples)
        return f"{self.name}_{str(solver)}"

    def get_solver_summary_table_name(self, solver):
        return self.get_solver_table_name(solver) + "_summary"
