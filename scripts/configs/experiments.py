from configs.projects import *

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
    def __init__(self, name, project):
        self.name = name

        assert isinstance(project, ProjectConfig)

        self.project = project

        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at least
        self.min_mutants = 10

        # how many mutants to generate at most
        self.max_mutants = 50

        # how long do we wait? (seconds)
        self.timeout = 40

        # margin of error in time (seconds)
        # self.time_moe_limit = 3

        # margin of error in success rate (0.0 - 1.0)
        self.res_moe_limit = 0.05

        # confidence level
        self.confidence_level = 0.95

        self.enabled_muts = [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RSEED]

    def get_solver_table_name(self, solver):
        # assert (solver in self.samples)
        return f"{self.name}_{str(solver)}"

class ExpConfig:
    def __init__(self, name, project, solvers, count=None):
        self.qcfg = QueryExpConfig(name, project)
        for s in solvers:
            assert isinstance(s, SolverInfo)
        # how many solver processes to run in parallel?
        self.num_procs = 8

        # these are the enabled solvers and their sampled queries
        self.samples = project.get_samples(solvers, count)

    def get_summary_table_name(self):
        return self.qcfg.name + "_summary"

    def get_project_name(self):
        return self.qcfg.project.name

    def empty_muts_map(self, init=[]):
        m = {str(mut): init.copy() for mut in self.qcfg.enabled_muts}
        return m

    # def _check_queries_exist(self):
    #     dirs = [self.project.clean_dirs[str(solver)] for solver in self.solvers]
    #     enabled_dirs = set(dirs)
    #     for dir in enabled_dirs:
    #         for query in self.queries:
    #             print(dir + query)
    #             assert (os.path.exists(dir + query))
