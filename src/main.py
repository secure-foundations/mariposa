#!/usr/bin/env python3.8

import argparse
from analysis.basic_analyzer import BasicAnalyzer
from base.exper import Experiment
from base.project import Partition
from base.runner import Runner
from base.defs import MARIPOSA
from utils.option_utils import *
from utils.system_utils import list_smt2_files
from project_wizard import *

def setup_single(subparsers):
    p = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')
    add_input_query_option(p)
    add_solver_option(p)
    add_experiment_option(p)
    add_clear_option(p)

    add_analyzer_option(p)
    add_verbose_option(p)

def run_single(args):
    in_query = args.input_query_path
    exp = Experiment.single_mode_exp(in_query, args.solver)
    output_dir = exp.proj.sub_root

    if os.path.exists(output_dir) and not args.clear:
        log_info(f"output directory {output_dir} already exists")
        BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return
    
    overwrite_dir(output_dir, args.clear)
    command = f"{MARIPOSA} -i {in_query} -o {exp.proj.sub_root}/split.smt2 -a split"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    # print(result.stdout.decode('utf-8'), end="")
    log_check(result.returncode == 0, "single mode split failed!")

    if list_smt2_files(output_dir) == []:
        log_info(f"no queries were generated from {in_query}")
        sys.exit(0)

    r = Runner()
    r.run_project(exp, args.clear)

    BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)

def setup_multi(subparsers):
    p = subparsers.add_parser('multi', help='multiple query mode. test an existing (preprocessed) project using the specified solver')
    add_input_dir_option(p)
    add_solver_option(p)
    add_experiment_option(p)
    add_clear_option(p)

    add_analyzer_option(p)

def run_multi(args):
    proj = PM.get_project_by_path(args.input_dir)
    exp = Experiment(args.experiment, proj, args.solver)
    r = Runner()
    r.run_project(exp, args.clear)
    BasicAnalyzer(exp, args.analyzer).print_status(0)

    return (exp.db_path, args.part)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    setup_single(subparsers)
    setup_multi(subparsers)
    # setup_manager(subparsers)
    # setup_worker(subparsers)
    # setup_recovery(subparsers)

    args = deep_parse_args(parser)

    if args.sub_command == "single":
        run_single(args)
    elif args.sub_command == "multi":
        run_multi(args)

