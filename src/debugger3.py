#!/usr/bin/env python3

import argparse
from debugger.options import DebugOptions
from debugger.factory import DbgMode, get_debugger


def main():
    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "-m",
        "--mode",
        default="auto",
        choices=[m.lower() for m in DbgMode.__members__.keys()],
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
    parser.add_argument(
        "--retry",
        default=False,
        action="store_true",
        help="retry",
    )
    parser.add_argument(
        "--verus",
        default=False,
        action="store_true",
        dest="is_verus",
        help="set if this is a verus query",
    )

    args = parser.parse_args()
    options = DebugOptions()
    options.retry_failed = args.retry
    options.skip_core = args.skip_core
    options.mode = DbgMode(args.mode)
    options.is_verus = args.is_verus

    # verbose if from commandline
    options.verbose = True
    # build proof if from commandline
    options.build_proof = True

    dbg = get_debugger(args.input_query_path, options)

    if args.collect_garbage:
        dbg.collect_garbage()

    if args.build_report:
        if dbg.report is None:
            print("no report available...")

    if args.clear_report_cache:
        dbg.clear_report_cache()

    if args.print_report:
        print("status", dbg.status)
        if r := dbg.report:
            r.print_stabilized()
        else:
            print("no report available...")

    if args.reset_project:
        dbg.reset_project()

    if args.create_project:
        dbg.create_project()

    if args.build_trace_graph:
        dbg.tracker.get_trace_graph()

    if args.build_ratios:
        dbg.tracker.get_trace_graph_ratios(True)


if __name__ == "__main__":
    main()
