#!/usr/bin/env python3.8

import argparse
from analysis.basic_analyzer import BasicAnalyzer
from base.exper import Experiment
from base.project import Partition
from base.runner import MARIPOSA, Runner
from base.solver import SolverRunner
from query.analyzer import QueryAnalyzer
from utils.option_utils import *
from utils.system_utils import list_smt2_files
from project_wizard import *

def setup_single(subparsers):
    p = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')
    add_input_query_option(p)
    add_solver_option(p)
    add_analyzer_option(p)
    add_clear_option(p)
    p.add_argument("-e", "--experiment", default="single")

def run_single(args):
    in_query = args.input_query_path
    exp = Experiment.single_mode_exp(in_query, args.solver)
    output_dir = exp.proj.sub_root

    if not can_overwrite_dir(output_dir):
        if args.clear:
            log_info(f"clearing output directory {output_dir}")
            shutil.rmtree(output_dir)
        else:
            log_info(f"output directory {output_dir} already exists")
            BasicAnalyzer(exp, args.analyzer).print_detailed_status()
            return
    
    create_output_dir(output_dir, args.clear)

    command = f"{MARIPOSA} -i {in_query} -o {exp.proj.sub_root}/split.smt2 -a split"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    # print(result.stdout.decode('utf-8'), end="")
    san_check(result.returncode == 0, "single mode split failed!")

    if list_smt2_files(output_dir) == []:
        log_info(f"no queries were generated from {in_query}")
        sys.exit(0)

    r = Runner()
    r.run_project(exp, args.clear)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    setup_single(subparsers)
    # setup_multi(subparsers)
    # setup_manager(subparsers)
    # setup_worker(subparsers)
    # setup_recovery(subparsers)
    args = parser.parse_args()

    if hasattr(args, "solver"):
        args.solver = SolverRunner.get_runner(args.solver)

    if hasattr(args, "part"):
        args.part = Partition.from_str(args.part)
    else:
        args.part = Partition(1, 1)

    if hasattr(args, "analyzer"):
        args.analyzer = QueryAnalyzer(args.analyzer)
    
    if args.sub_command == "single":
        run_single(args)


