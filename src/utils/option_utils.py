import os
from base.defs import MAGIC_IGNORE_SEED
from base.project import Partition
from base.query_analyzer import Stability
from utils.query_utils import Mutation
from utils.system_utils import file_exists, log_check

def add_input_query_option(parser):
    parser.add_argument("-i", "--input-query-path", required=True, help="the input query path")

def add_input_log_option(parser):
    parser.add_argument("--input-log-path", required=True, help="the input log")

def add_output_query_option(parser):
    parser.add_argument("-o", "--output-query-path", required=True, help="the output query path")

def add_timeout_option(parser):
    parser.add_argument("--timeout", default=60, help="the timeout (seconds) for the solver")

def add_output_log_option(parser):
    parser.add_argument("-o", "--output-log-path", required=True, help="the output log path")

def add_restart_option(parser):
    parser.add_argument("--restarts", default=60, required=False, help="the number of restarts")

def add_solver_option(parser):
    parser.add_argument("-s", "--solver", default="z3_4_13_0", help="the solver name (from solvers.json) to use")

def add_analysis_options(parser):
    parser.add_argument("-e", "--exp-config", default="default", help="the experiment configuration name (from exps.json)")
    add_solver_option(parser)
    parser.add_argument("--analyzer", default="default", help="the analyzer name (from config/expers.json) to use")
    parser.add_argument("-cv", "--category-verbosity", type=int, default=0, help="level of verbosity for categories in the analysis")
    parser.add_argument("--category", type=str, default="none", help="if specified, only analyze the specified category")
    parser.add_argument("-qv", "--query-verbosity", type=int, default=0, help="level of verbosity for each query in the analysis")

def add_experiment_options(parser):
    add_analysis_options(parser)
    add_clear_option(parser)

def add_new_project_option(parser):
    parser.add_argument("--new-project-name", required=True, help="the project group name to be created under data/projects/ (only for preprocess!)")

def add_input_dir_option(parser, is_known=True, is_group=False):
    parser.add_argument("-i", "--input-dir", required=True, help="the input directory")
    parser.add_argument("--part", default="1/1", help="which part of the project to run mariposa on (probably should not be specified manually)")
    parser.add_argument("--is-known-project", default=is_known, action='store_true', help="allow a directory but not define a project")
    parser.add_argument("--is-group", default=is_group, action='store_true', help="the input directory is a group")

def add_output_dir_option(parser):
    parser.add_argument("-o", "--output-dir", required=False, help="the output directory")

def add_clear_option(parser):
    parser.add_argument("--clear-existing", default=False, action='store_true', help="clear the existing experiment directory and database")

def add_debug_option(parser):
    parser.add_argument("--debug", default=False, action='store_true', help="run in debug mode")

def add_authkey_option(parser):
    parser.add_argument("--authkey", required=True, help="the authkey to use for the server pool")

def add_ninja_log_option(parser):
    parser.add_argument("--record-build-stats", default=False, action='store_true', help="parse and keep the build stat")
    parser.add_argument("--no-build", default=False, action='store_true', help="stop after creating the ninja")

def add_incremental_option(parser):
    parser.add_argument("--incremental", default=False, action='store_true', help="run the solver in incremental mode")

def deep_parse_args(args):
    from base.factory import FACT

    if hasattr(args, "solver"):
        args.solver = FACT.get_solver(args.solver)

    if hasattr(args, "part"):
        args.part = Partition.from_str(args.part)
    else:
        args.part = Partition(1, 1)

    if hasattr(args, "category"):
        if args.category == "none":
            args.category = None
        else:
            args.category = Stability(args.category)

    if hasattr(args, "analyzer"):
        args.analyzer = FACT.get_analyzer(args.analyzer)

    if hasattr(args, "input_dir") and args.is_known_project:
        if args.is_group:
            args.input_group = FACT.get_group_by_path(args.input_dir)
        else:
            args.input_proj = FACT.get_project_by_path(args.input_dir)
            args.input_proj.part = args.part
    else:
        args.is_group = False

    if hasattr(args, "seed"):
        if int(args.seed) == MAGIC_IGNORE_SEED:
            args.seed = None

    if hasattr(args, "input_query_path"):
        log_check(file_exists(args.input_query_path), 
                  "input query does not exist or not a file")

    if hasattr(args, "mutation"):
        args.mutation = Mutation(args.mutation)

    single = args.sub_command in {"single", "trace-diff"}

    if hasattr(args, "exp_config") and not args.is_group:
        args.exp_config = FACT.get_config(args.exp_config)

        if args.sub_command == "offload-single":
            return args

        if single:
            args.experiment = FACT.get_single_exper(
                args.input_query_path, args.exp_config, args.solver, clear=args.clear_existing)
        else:
            args.experiment = FACT.get_exper(
                args.input_proj, args.exp_config, args.solver, build=True)

    if hasattr(args, "timeout"):
        args.timeout = int(args.timeout)

    if hasattr(args, "restarts"):
        args.restarts = int(args.restarts)

    if hasattr(args, "incremental"):
        args.incremental = bool(args.incremental)

    return args