#!/usr/bin/env python3

import argparse
import z3
from debugger.debugger_options import DebugOptions
from debugger.debugger import DbgMode, get_debugger


def main():
    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "-m",
        "--mode",
        default="auto",
        choices=["auto", "singleton", "doubleton", "fast_fail", "timeout"],
        help="the mode to operate on",
    )
    parser.add_argument(
        "--collect-garbage",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--print-report",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--build-report",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--clear-report-cache",
        default=False,
        action="store_true",
    )
    parser.add_argument(
        "--reset-project",
        default=False,
        action="store_true",
        help="reset the project",
    )
    parser.add_argument(
        "--create-project",
        default=False,
        action="store_true",
        help="create the project",
    )
    parser.add_argument(
        "--build-trace-graph",
        default=False,
        action="store_true",
        help="build trace graph",
    )
    parser.add_argument(
        "--build-ratios",
        default=False,
        action="store_true",
        help="build sub ratios",
    )
    parser.add_argument(
        "--skip-core",
        default=False,
        action="store_true",
        help="skip core",
    )

    args = parser.parse_args()
    options = DebugOptions()
    # verbose if from commandline
    options.verbose = True
    options.skip_core = args.skip_core

    mode = DbgMode(args.mode)

    dbg = get_debugger(args.input_query_path, mode, options)

    if args.collect_garbage:
        dbg.collect_garbage()

    if args.build_report:
        if dbg.report is None:
            print("no report available...")

    if args.clear_report_cache:
        dbg.clear_report_cache()

    if args.print_report:
        if r := dbg.report:
            r.print_stabilized()
        else:
            print("no report available...")

    if args.reset_project:
        dbg.reset_project()

    if args.create_project:
        dbg.create_project()

    if args.build_trace_graph:
        dbg.get_trace_graph()

    if args.build_ratios:
        dbg.get_trace_graph_ratios(True)


if __name__ == "__main__":
    main()
