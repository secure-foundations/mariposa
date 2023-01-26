from configs.projects import *

class ExpConfig:
    def __init__(self, name, project, samples):
        self.name = name

        assert isinstance(project, ProjectConfig)

        self.project = project

        for s in samples:
            assert isinstance(s, SolverInfo)

        # these are the enabled solvers and their sampled queries
        self.samples = samples

        # how many times do we run each query? default=1
        self.trials = 1

        # how many mutants to generate at least
        self.min_mutants = 10

        # how many mutants to generate at most
        self.max_mutants = 50

        # how long do we wait? (seconds)
        self.timeout = 30

        # how many solver processes to run in parallel?
        self.num_procs = 8

        self.table_name = self.name + "_results"

        # margin of error in time (seconds)
        # self.time_moe_limit = 3

        # margin of error in success rate (0.0 - 1.0)
        self.res_moe_limit = 0.05

        # confidence level
        self.confidence_level = 0.95

    # def _check_queries_exist(self):
    #     dirs = [self.project.clean_dirs[str(solver)] for solver in self.solvers]
    #     enabled_dirs = set(dirs)
    #     for dir in enabled_dirs:
    #         for query in self.queries:
    #             print(dir + query)
    #             assert (os.path.exists(dir + query))
