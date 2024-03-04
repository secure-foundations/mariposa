#!/usr/bin/env python3

import argparse
from analysis.basic_analyzer import BasicAnalyzer
from utils.option_utils import *
from proj_wizard import *

def set_up_basic(subparsers):
    p = subparsers.add_parser('basic', help='analyze the results of an existing experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_basic(args):
    args = deep_parse_args(args)
    exp = args.experiment
    log_check(exp.sum_table_exists(), "experiment results do not exist")
    ba = BasicAnalyzer(exp, args.analyzer)
    ba.print_status(args.verbose)
    
def set_up_info(subparsers):
    p = subparsers.add_parser('info', help='list available experiments')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Mariposa Analysis Wizard is a tool to analyze Mariposa experiment results. ")
    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run analysis in")

    set_up_basic(subparsers)
    set_up_info(subparsers)

    args = parser.parse_args()

    if args.sub_command == "basic":
        handle_basic(args)
    # elif args.sub_command == "info":
    #     list_available_experiments()
    else:
        parser.print_help()
