import argparse
from configure.project import ProjectManager, Partition
from configure.solver import SolverInfo
from analysis.analyzer import Analyzer
from cluster_modes import worker_mode, manager_mode, recovery_mode
from local_modes import single_mode, multi_mode, preprocess_mode

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

def load_project(project_name):
    m = ProjectManager()
    return m.load_project(project_name)

def print_info():
    m = ProjectManager()
    m.print_available_projects()

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    subparsers.add_parser('info', help='print information about the current configuration or experiments')

    update_parser = subparsers.add_parser('update', help='update mode. update an existing experiment by (adding) a single query.')
    single_parser = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')

    for sp in [update_parser, single_parser]:
        sp.add_argument("-q", "--query", required=True, help="the input query")

    single_parser.add_argument("-e", "--experiment", default="single", help="the experiment configuration name in configs.json")

    multi_parser = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver. the project is specified by a python expression that evaluates to a ProjectInfo object. ')

    multi_parser.add_argument("--part", default="1/1", help="which part of the project to run mariposa on (probably should not be specified manually)")

    manager_parser = subparsers.add_parser('manager', help='sever pool manager mode.')
    manager_parser.add_argument("--total-parts", type=int, required=True, help="number of parts to split the project into")

    recovery_parser = subparsers.add_parser('recovery', help='recovery mode. recover the database from a crashed run (do not use unless on s190x cluster).')

    for sp in [single_parser, multi_parser, manager_parser]:
        sp.add_argument("--clear", default=False, action='store_true', help="clear the existing experiment directory and database")

    for sp in [multi_parser, manager_parser, recovery_parser, update_parser]:
        sp.add_argument("-p", "--project", required=True, help="the project name (from configs.json) to run mariposa on")
        sp.add_argument("-e", "--experiment", required=True, help="the experiment configuration name (from configs.json)")

    for sp in [single_parser, multi_parser, manager_parser, recovery_parser, update_parser]:
        sp.add_argument("-s", "--solver", required=True, help="the solver name (from configs.json) to use")
        if sp == recovery_parser:
            continue
        sp.add_argument("--analysis-only", default=False, action='store_true', help="do not perform experiments, only analyze existing data")
        sp.add_argument("--analysis-skip", default=False, action='store_true', help="skip analysis")
        sp.add_argument("--analyzer", default="default", help="the analyzer name (from configs.json) to use")

    worker_parser = subparsers.add_parser('worker', help='sever pool worker mode.')
    worker_parser.add_argument("--manager-addr", required=True, help="the manager address for the server pool")

    for sp in [worker_parser, manager_parser]:
        sp.add_argument("--authkey", required=True, help="the authkey to use for the server pool")

    preprocess_parser = subparsers.add_parser('preprocess', help='preprocess mode. (recursively) traverse the input directory and split all queries with ".smt2" file extension, the split queries will be stored under the output directory.')
    preprocess_parser.add_argument("--in-dir", required=True, help='the input directory with ".smt2" files')
    preprocess_parser.add_argument("--out-dir", required=True, help="the output directory to store preprocessed files, flattened and split")

    preprocess_parser.add_argument("--clean-debug", required=False, help="if queries fail during the verification process, remove the debug queries that arise during error localization", action='store_true')

    args = parser.parse_args()

    if hasattr(args, "solver"):
        args.solver = SolverInfo(args.solver)
    if hasattr(args, "part"):
        args.part = Partition.from_str(args.part)
    if hasattr(args, "project"):
        args.project = load_project(args.project)
    if hasattr(args, "analyzer"):
        args.analyzer = Analyzer(args.analyzer)

    if args.sub_command == "preprocess":
        preprocess_mode(args)
    elif args.sub_command == "single":
        single_mode(args)
    elif args.sub_command == "multiple":
        multi_mode(args)
    elif args.sub_command == "manager":
        manager_mode(args)
    elif args.sub_command == "worker":
        worker_mode(args)
    elif args.sub_command == "recovery":
        recovery_mode(args)
    elif args.sub_command == "update":
        update_mode(args)
    elif args.sub_command == "info":
        print_info()
    elif args.sub_command is None:
        parser.print_help()
