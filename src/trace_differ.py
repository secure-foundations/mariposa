#!/usr/bin/env python3

import argparse
from analysis.basic_analyzer import BasicAnalyzer
from utils.local_utils import handle_single
from utils.option_utils import *
from utils.system_utils import log_check

def set_up_query(subparsers):
    p = subparsers.add_parser('query', help='query mode, this WILL call the single mode of experiment wizard')
    add_input_query_option(p)
    add_experiment_options(p)

def handle_diff_query(args):
    handle_single(args)

def set_up_project(subparsers):
    p = subparsers.add_parser('project', help='experiment with trace from an existing experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_diff_project(args):
    exp = args.experiment
    log_check(exp.sum_table_exists(), "experiment results do not exist")
    ba = BasicAnalyzer(exp, args.analyzer)
    ba.do_stuff()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Trace Differ is a tool to compare the traces from the successful and failed mutants")

    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    set_up_query(subparsers)
    set_up_project(subparsers)

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "query":
        handle_diff_query(args)
    elif args.sub_command == "project":
        handle_diff_project(args)
    else:
        parser.print_help()
