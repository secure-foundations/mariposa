#!/usr/bin/env python3

import argparse
import os
from analysis.expr_analyzer import ExprAnalyzer
from base.project import KnownExt
from query.analyzer import UnstableReason
from utils.local_utils import handle_single
from utils.option_utils import *
from utils.system_utils import log_check, print_banner

def set_up_query(subparsers):
    p = subparsers.add_parser('query', help='query mode, this WILL call the single mode of experiment wizard')
    add_input_query_option(p)
    add_experiment_options(p)

def handle_diff_query(args):
    handle_single(args)

def set_up_project(subparsers):
    p = subparsers.add_parser('project', help='experiment with trace from an existing experiment')
    p.add_argument("--reuse-mutant", default=False, action='store_true', help="reuse the mutant from the previous experiment")
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_diff_project(args):
    exp = args.experiment
    log_check(exp.sum_table_exists(), "experiment results do not exist")
    ba = ExprAnalyzer(exp, args.analyzer)
    reasons = ba.get_unstable_reasons()
    reasons.print_status()
    for qid in reasons[UnstableReason.TIMEOUT]:
        print(ba[qid].query_path)

    # output_dir = exp.proj.get_log_dir(KnownExt.Z3_TRACE)
    # for i, (qr, pms, fms) in enumerate(unstables):
    #     print_banner("Query:")
    #     print(qr.query_path)
    #     print_banner("Passed Mutants:")
    #     for (m, s, _) in pms:
    #         out_path = os.path.join(output_dir, f"{qr.qid}.{m}.{s}.{KnownExt.Z3_TRACE}")
    #         print("../axiom-profiler-2/target/release/smt-log-parser " + out_path + " > passed")
    #     print_banner("Failed Mutants:")
    #     for (m, s, rc) in fms:
    #         out_path = os.path.join(output_dir, f"{qr.qid}.{m}.{s}.{KnownExt.Z3_TRACE}")
    #         print("../axiom-profiler-2/target/release/smt-log-parser " + out_path + " > failed")
    #         print(rc)
    #     print("")

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
