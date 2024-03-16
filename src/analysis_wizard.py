#!/usr/bin/env python3

import argparse
from analysis.basic_analyzer import BasicAnalyzer
from analysis.inst_analyzer import InstAnalyzer
from analysis.perf_analyzer import PrefAnalyzer
from utils.option_utils import *
from proj_wizard import *

def set_up_basic(subparsers):
    p = subparsers.add_parser('basic', help='analyze the results of an existing experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_basic(args):
    exp = args.experiment
    log_check(exp.sum_table_exists(), "experiment results do not exist")
    ba = BasicAnalyzer(exp, args.analyzer)
    ba.print_status(args.verbose)

def set_up_cvc5_perf(subparsers):
    p = subparsers.add_parser('perf', help='analyze the raw performance of cvc5/z3 on a project group')
    add_input_dir_option(p, is_group=True)

def set_up_cvc5_inst(subparsers):
    p = subparsers.add_parser('inst', help='analyze the instantiation logs from cvc5')
    add_input_dir_option(p)

def set_up_stuff(subparsers):
    p = subparsers.add_parser('stuff', help='place holder for analysis work in progress')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_stuff(args):
    exp = args.experiment
    log_check(exp.sum_table_exists(), "experiment results do not exist")
    ba = BasicAnalyzer(exp, args.analyzer)
    ba.do_stuff()

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Mariposa Analysis Wizard is a tool to analyze Mariposa experiment results. ")
    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run analysis in")

    set_up_basic(subparsers)
    set_up_cvc5_perf(subparsers)
    set_up_cvc5_inst(subparsers)
    set_up_stuff(subparsers)

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "basic":
        handle_basic(args)
    elif args.sub_command == "perf":
        PrefAnalyzer(args.input_group)
    elif args.sub_command == "inst":
        InstAnalyzer(args.input_proj)
    elif args.sub_command == "stuff":
        handle_stuff(args)
    else:
        parser.print_help()
