import argparse
from basics.project import PM, Partition, QueryType
from basics.solver import Solver
from analysis.query_analyzer import QueryAnalyzer
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

# def setup_preprocess(subparsers):
#     p = subparsers.add_parser('preprocess', help='preprocess mode. (recursively) traverse the input directory and split all queries with ".smt2" file extension, the split queries will be stored under the output directory.')
#     p.add_argument("--in-dir", required=True, help='the input directory with ".smt2" files')
#     p.add_argument("--out-dir", required=True, help="the output directory to store preprocessed files, flattened and split")
#     p.add_argument("--clean-debug", required=False, help="if queries fail during the verification process, remove the debug queries that arise during error localization", action='store_true')

def setup_single(subparsers):
    p = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')
    add_query_option(p)
    add_solver_option(p)
    add_analyzer_option(p)
    add_clear_option(p)
    p.add_argument("-e", "--experiment", default="single", help="the experiment configuration name in configs.json")

def setup_multi(subparsers):
    p = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver')
    add_project_option(p)
    add_solver_option(p)
    add_experiment_option(p)
    add_clear_option(p)

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

# def single_mode(args):
#     exp = Experiment.single_mode_exp(args.query, args.solver)

#     proj_root = exp.proj.root_dir
#     dir_exists = os.path.exists(proj_root)

#     if dir_exists:
#         if args.clear:
#             print(f"[INFO] experiment dir {proj_root} exists, removing")
#             shutil.rmtree(proj_root, ignore_errors=True)
#         else:
#             print(f"[INFO] experiment dir {proj_root} exists")
#             BasicAnalyzer(exp, args.analyzer).print_detailed_status()
#             return

#     os.makedirs(proj_root)

#     command = f"./target/release/mariposa -i '{args.query}' --chop -o '{proj_root}/split.smt2'"
#     result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
#     print(result.stdout.decode('utf-8'), end="")
#     san_check(result.returncode == 0, "split failed")

#     r = Runner()
#     r.run_project(exp, args.clear)

#     BasicAnalyzer(exp, args.analyzer).print_detailed_status()

# def multi_mode(args):
#     exp = Experiment(args.experiment, 
#             args.project, 
#             args.solver)
#     r = Runner()
#     r.run_project(exp, args.clear)
#     return (exp.db_path, args.part)

# def setup_analysis(subparsers):
#     p = subparsers.add_parser('analysis', help='analyze the results of experiments')
#     add_project_option(p)
#     add_experiment_option(p)
#     add_solver_option(p)
#     add_analyzer_option(p)
#     p.add_argument("--verbose", type=int, default=0, help="level of verbosity for the analysis")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    setup_single(subparsers)
    setup_multi(subparsers)
    setup_manager(subparsers)
    setup_worker(subparsers)
    setup_recovery(subparsers)

    subparsers.add_parser('info', help='print information about the current configuration or experiments')

    # update_parser = subparsers.add_parser('update', help='update mode. update an existing experiment by (adding) a single query.')

    args = parser.parse_args()

    if hasattr(args, "solver"):
        args.solver = Solver(args.solver)
    if hasattr(args, "part"):
        args.part = Partition.from_str(args.part)
    else:
        args.part = Partition(1, 1)
    if hasattr(args, "ptype"):
        args.ptype = QueryType(args.ptype)
    if hasattr(args, "project"):
        args.project = PM.load_project(args.project, args.ptype)
        args.project.set_partition(args.part)
    if hasattr(args, "analyzer"):
        args.analyzer = QueryAnalyzer(args.analyzer)

    if args.sub_command == "single":
        single_mode(args)
    elif args.sub_command == "multiple":
        multi_mode(args)
    elif args.sub_command == "manager":
        manager_mode(args)
    elif args.sub_command == "worker":
        worker_mode(args)
    elif args.sub_command == "recovery":
        recovery_mode(args)
    # elif args.sub_command == "update":
    #     update_mode(args)
    elif args.sub_command is None:
        parser.print_help()
