#!/usr/bin/env python3

import argparse
import random
from analysis.core_analyzer import CoreAnalyzer
from analysis.debug_analyzer import analyze_debug
from analysis.singleton_analyzer import SingletonAnalyzer
from analysis.trace_analyzer import TraceAnalyzer
from base.defs import MARIPOSA_GROUPS
from base.exper_analyzer import ExperAnalyzer
from analysis.inst_analyzer import InstAnalyzer
from analysis.perf_analyzer import PrefAnalyzer
from analysis.shake_analyzer import ShakeAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.factory import FACT
from base.query_analyzer import Stability
from utils.option_utils import *
from proj_wizard import *
from utils.plot_utils import *
from utils.shake_utils import parse_shake_log, load_query_cids
from base.query_analyzer import Stability as STB


def set_up_basic(subparsers):
    p = subparsers.add_parser(
        "basic", help="analyze the results of an existing experiment"
    )
    add_input_dir_option(p)
    add_analysis_options(p)


def set_up_singleton(subparsers):
    p = subparsers.add_parser("filter", help="create filtered project")
    add_input_dir_option(p)
    add_analysis_options(p)


def set_up_stable(subparsers):
    p = subparsers.add_parser("stable", help="analyze the stable queries")
    add_input_dir_option(p)
    add_analysis_options(p)


def handle_basic(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_status(category_verbosity=args.category_verbosity, query_verbosity=args.query_verbosity, category=args.category)


def set_up_verify(subparsers):
    p = subparsers.add_parser(
        "verify", help="analyze the verification performance only"
    )
    add_input_dir_option(p)
    add_analysis_options(p)


def handle_verify(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_plain_status()


def set_up_cvc5_perf(subparsers):
    p = subparsers.add_parser(
        "perf", help="analyze the raw performance of cvc5/z3 on a project group"
    )
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)


def set_up_cvc5_inst(subparsers):
    p = subparsers.add_parser("inst", help="analyze the instantiation logs from cvc5")
    add_input_dir_option(p)


def set_up_unstable(subparsers):
    p = subparsers.add_parser(
        "unstable", help="analyze the unstable reasons of an experiment"
    )
    add_input_dir_option(p)
    add_analysis_options(p)


def handle_unstable(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.get_failure_types().print_status()


def set_up_core(subparsers):
    p = subparsers.add_parser("core", help="analyze the core")
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)


def set_up_shake(subparsers):
    p = subparsers.add_parser("shake", help="analyze shake")
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)


def handle_shake(args):
    group = args.input_group
    shake = ShakeAnalyzer(group)


def set_up_wombo(subparsers):
    p = subparsers.add_parser("wombo", help="no help is coming")
    add_input_dir_option(p, is_group=True)


def set_up_trace(subparsers):
    p = subparsers.add_parser("trace", help="no help is coming")
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)


def find_oracle_path(qid):
    for group in "fs_dice", "d_fvbkv", "d_lvbkv", "d_komodo", "fs_vwasm":
        if qid.startswith(group):
            actual = qid[len(group) + 2 :]
            return f"data/projs/{group}/shko.cvc5/{actual}.smt2"
    assert False


def valid_max(scores):
    return max([s for s in scores if not np.isnan(s)])


def handle_debug():
    analyze_debug()


def handle_special():
    pass


def handle_filter(args):
    exp: Experiment = args.experiment

    if not exp.is_done():
        log_warn("experiment results do not exist, run the following command:")
        print(f"./src/exper_wizard.py manager -e verify --total-parts 30 -s z3_4_13_0 -i {exp.proj.sub_root} --clear")
        return

    ba = SingletonAnalyzer(exp, args.analyzer)
    ba.create_filtered_project()

def setup_carve(subparsers):
    p = subparsers.add_parser("carve", help="carve to only stable queries")
    add_input_dir_option(p)
    add_analysis_options(p)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Mariposa Analysis Wizard is a tool to analyze Mariposa experiment results. "
    )
    subparsers = parser.add_subparsers(
        dest="sub_command", help="mode to run analysis in"
    )

    set_up_basic(subparsers)
    set_up_verify(subparsers)
    set_up_singleton(subparsers)
    set_up_cvc5_perf(subparsers)
    set_up_cvc5_inst(subparsers)
    set_up_unstable(subparsers)
    set_up_core(subparsers)
    set_up_shake(subparsers)
    set_up_wombo(subparsers)
    set_up_trace(subparsers)
    set_up_stable(subparsers)
    setup_carve(subparsers)

    p = subparsers.add_parser("debug", help="no help is coming")
    p = subparsers.add_parser("special", help="placeholder for special analysis")
    args = parser.parse_args()

    if args.sub_command == "filter":
        # override the exp_config
        args.exp_config = "verify"

    args = deep_parse_args(args)

    if args.sub_command == "basic":
        handle_basic(args)
    elif args.sub_command == "verify":
        handle_verify(args)
    elif args.sub_command == "filter":
        handle_filter(args)
    elif args.sub_command == "perf":
        PrefAnalyzer(args.input_group, args.analyzer)
    elif args.sub_command == "inst":
        InstAnalyzer(args.input_proj)
    elif args.sub_command == "unstable":
        handle_unstable(args)
    elif args.sub_command == "core":
        ca = CoreAnalyzer(args.input_group, args.analyzer)
        ca.print_status()
    elif args.sub_command == "shake":
        handle_shake(args)
    elif args.sub_command == "wombo":
        WomboAnalyzer(args.input_group)
    elif args.sub_command == "trace":
        TraceAnalyzer(args.input_group)
    elif args.sub_command == "debug":
        handle_debug()
    elif args.sub_command == "stable":
        ba = ExperAnalyzer(args.experiment, args.analyzer)
        ba.print_stabilized_queries()
    elif args.sub_command == "carve":
        ba = ExperAnalyzer(args.experiment, args.analyzer)
        ba.carve_non_stable_queries()
    elif args.sub_command == "special":
        handle_special()
    else:
        parser.print_help()
