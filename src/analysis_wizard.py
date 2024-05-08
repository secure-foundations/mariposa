#!/usr/bin/env python3

import argparse
from analysis.core_analyzer import CoreAnalyzer
from base.exper_analyzer import ExperAnalyzer
from analysis.inst_analyzer import InstAnalyzer
from analysis.perf_analyzer import PrefAnalyzer
from analysis.shake_analyzer import ShakeAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.factory import FACT
from base.query_analyzer import Stability
from utils.option_utils import *
from proj_wizard import *

def set_up_basic(subparsers):
    p = subparsers.add_parser('basic', help='analyze the results of an existing experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_basic(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_status(args.category_verbosity, args.query_verbosity)

def set_up_verify(subparsers):
    p = subparsers.add_parser('verify', help='analyze the verification performance only')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_verify(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_plain_status()

def set_up_cvc5_perf(subparsers):
    p = subparsers.add_parser('perf', help='analyze the raw performance of cvc5/z3 on a project group')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def set_up_cvc5_inst(subparsers):
    p = subparsers.add_parser('inst', help='analyze the instantiation logs from cvc5')
    add_input_dir_option(p)

def set_up_unstable(subparsers):
    p = subparsers.add_parser('unstable', help='analyze the unstable reasons of an experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_unstable(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.get_failure_types().print_status()

def set_up_core(subparsers):
    p = subparsers.add_parser('core', help='analyze the core')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def set_up_shake(subparsers):
    p = subparsers.add_parser('shake', help='analyze shake')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def handle_shake(args):
    group = args.input_group
    shake = ShakeAnalyzer(group, args.analyzer)

def set_up_wombo(subparsers):
    p = subparsers.add_parser('wombo', help='no help is coming')
    add_input_dir_option(p, is_group=True)

def find_oracle_path(qid):
    for group in "fs_dice", "d_fvbkv", "d_lvbkv", "d_komodo", "fs_vwasm":
        if qid.startswith(group):
            actual = qid[len(group)+2:]
            return f"data/projs/{group}/shko.cvc5/{actual}.smt2"
    assert False

def handle_special():
    proj = FACT.get_project_by_path("data/projs/pre_cvc5/base.cvc5")
    ana = FACT.get_analyzer("60nq")
    exp = FACT.load_any_analysis(proj, ana)

    eta = 0

    for qid in exp.stability_categories[Stability.STABLE].items:
        qr = exp[qid]
        mt, std = qr.get_mean_time()
        if std/1000 < 1:
            continue

        os.system(f"cp {find_oracle_path(qid)} data/projs/bench_unstable_cvc5/shko.cvc5/{qid}.smt2")
        
        eta += mt

    for qid in exp.stability_categories[Stability.UNSTABLE].items:
        qr = exp[qid]
        mt, std = qr.get_mean_time()
        eta += mt
        os.system(f"cp {find_oracle_path(qid)} data/projs/bench_unstable_cvc5/shko.cvc5/{qid}.smt2")
        # print(find_oracle_path(qid))
        # os.system(f"cp {qr.query_path} data/projs/bench_unstable_cvc5/base.cvc5")

    # eta = eta * 180 / 1000 / 60 / 60 
    # print(f"ETA: {eta} cpu hours")
    # print(f"ETA: {eta/ 42} hours")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Mariposa Analysis Wizard is a tool to analyze Mariposa experiment results. ")
    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run analysis in")

    set_up_basic(subparsers)
    set_up_verify(subparsers)
    set_up_cvc5_perf(subparsers)
    set_up_cvc5_inst(subparsers)
    set_up_unstable(subparsers)
    set_up_core(subparsers)
    set_up_shake(subparsers)
    set_up_wombo(subparsers)
    p = subparsers.add_parser('special', help='placeholder for special analysis')

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "basic":
        handle_basic(args)
    elif args.sub_command == "verify":
        handle_verify(args)
    elif args.sub_command == "perf":
        PrefAnalyzer(args.input_group, args.analyzer)
    elif args.sub_command == "inst":
        InstAnalyzer(args.input_proj)
    elif args.sub_command == "unstable":
        handle_unstable(args)
    elif args.sub_command == "core":
        ca = CoreAnalyzer(args.input_group)
        ca.print_status()
    elif args.sub_command == "shake":
        handle_shake(args)
    elif args.sub_command == "wombo":
        WomboAnalyzer(args.input_group)
    elif args.sub_command == "special":
        handle_special()
    else:
        parser.print_help()
