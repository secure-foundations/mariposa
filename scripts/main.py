import argparse
from basics.project import PM, Partition, QueryType
from basics.solver import Solver
from query.analyzer import QueryAnalyzer
from utils.option_utils import *
# from cluster_modes import worker_mode, manager_mode, recovery_mode
# from local_modes import single_mode, multi_mode, preprocess_mode, analysis_mode

# def update_mode(args):
#     c = Configer()
#     exp = c.load_known_experiment(args.experiment)
#     solver = c.load_known_solver(args.solver)
#     project = c.load_known_project(args.project)

#     sanity = args.query.startswith(project.clean_dir)
#     message = f"[ERROR] query {args.query} does not belong to project {project.clean_dir}"
#     san_check(sanity, message)
#     r = Runner(exp)
#     r.update_project(project, solver, args.query)

def setup_manager(subparsers):
    p = subparsers.add_parser('manager', help='sever pool manager mode.')
    add_project_option(p)
    add_solver_option(p)
    add_experiment_option(p)
    add_clear_option(p)
    add_authkey_option(p)
    p.add_argument("--total-parts", type=int, required=True, help="number of parts to split the project into")

def setup_worker(subparsers):
    p = subparsers.add_parser('worker', help='server pool worker mode.')
    add_authkey_option(p)
    p.add_argument("--manager-addr", required=True, help="the address of the manager node")

def setup_recovery(subparsers):
    p = subparsers.add_parser('recovery', help='recovery mode. recover an existing experiment by (adding) a single query.')
    add_project_option(p)
    add_solver_option(p)
    add_experiment_option(p)

# def setup_analysis(subparsers):
#     p = subparsers.add_parser('analysis', help='analyze the results of experiments')
#     add_project_option(p)
#     add_experiment_option(p)
#     add_solver_option(p)
#     add_analyzer_option(p)
#     p.add_argument("--verbose", type=int, default=0, help="level of verbosity for the analysis")

