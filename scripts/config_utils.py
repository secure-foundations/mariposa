# def load_seeds_file(path):
#     seeds = open(path).read()
#     assert(seeds[0] == "[")
#     assert(seeds[-1] == "]")
#     seeds = eval(seeds)
#     assert(isinstance(seeds, list))
#     for s in seeds:
#         assert(isinstance(s, int))
#         assert(s >= 0)
#     return seeds

class Config:
    def __init__(self, qlist, trials, seeds, timeout, procs, prefix):
        self.qlist_path = qlist
        self.trials = trials
        self.seeds = seeds
        self.timeout = timeout
        self.procs = procs
        self.prefix = prefix

    def __str__(self):
        return f"""qlist path: {self.qlist_path}
trials per query: {self.trials}
seeds used: {self.seeds}
timeout used (seconds): {self.timeout}
dir prefix: {self.prefix}
"""

DEFAULT_3_SEEDS = [10615679144982909142, 16335111916646947812, 9748429691088265249]

CONSISTENCY_EXP_CONFIG = Config(
    "data/qlists/smtlib_rand1K_known",
    4, # run 4 trails each query
    [], # no seeds needed (no mutation)
    30, # 30 seconds timeout,
    8, # run with 8 procs
    "gen/consistency/")

TIME_RLIMIT_CORRELATION_CONFIG = Config(
    "data/qlists/smtlib_rand10K",
    1,
    [],
    180,
    8,
    "gen/correlate/")

DFY100_STABLE_EXP_CONFIG =  Config(
    "data/qlists/dafny_rand100",
    1,
    DEFAULT_3_SEEDS, # 3 mutations per class
    30, # 30 seconds timeout
    8, # run with 8 procs
    "gen/dfy100_stable/")

