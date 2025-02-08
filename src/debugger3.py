#!/usr/bin/env python3

import argparse
import z3 
from debugger.debugger import Debugger3

def main():
    z3.set_param(proof=True)

    parser = argparse.ArgumentParser(description="Mariposa Debugger. ")
    parser.add_argument(
        "-i", "--input-query-path", required=True, help="the input query path"
    )
    parser.add_argument(
        "--skip-core",
        default=False,
        action="store_true",
        help="skip building cores",
    )
    parser.add_argument(
        "--retry-failed",
        default=False,
        action="store_true",
        help="retry failed experiments",
    )
    parser.add_argument(
        "--clear-all",
        default=False,
        action="store_true",
        help="clear all existing data",
    )
    parser.add_argument(
        "--clear-traces",
        default=False,
        action="store_true",
        help="clear existing traces",
    )
    parser.add_argument(
        "--clear-cores",
        default=False,
        action="store_true",
        help="clear existing cores",
    )
    parser.add_argument(
        "--clear-edits",
        default=False,
        action="store_true",
        help="clear existing edits",
    )
    parser.add_argument(
        "--clear-proofs",
        default=False,
        action="store_true",
        help="clear existing proofs",
    )
    parser.add_argument(
        "--create-singleton",
        default=False,
        action="store_true",
        help="create singleton edit project",
    )
    parser.add_argument(
        "--analyze-singleton",
        default=False,
        action="store_true",
        help="analyze singleton edit project",
    )
    parser.add_argument(
        "--fix-missing-edits",
        default=False,
        action="store_true",
        help="fix missing queries in singleton project",
    )
    parser.add_argument(
        "--print-status",
        default=False,
        action="store_true",
        help="print the current status",
    )
    parser.add_argument(
        "--reroll",
        default=False,
        action="store_true",
        help="(maybe) change the proof and trace",
    )
    parser.add_argument(
        "--reset-proof-cache",
        default=False,
        action="store_true",
        help="reset the proof analyzer CACHE",
    )
    parser.add_argument(
        "--collect-garbage",
        default=False,
        action="store_true",
        help="collect garbage",
    )
    args = parser.parse_args()

    dbg = Debugger3(
        args.input_query_path,
        retry_failed=args.retry_failed,
        clear_all=args.clear_all,
        clear_edits=args.clear_edits,
        clear_traces=args.clear_traces,
        clear_cores=args.clear_cores,
        clear_proofs=args.clear_proofs,
        skip_core=args.skip_core,
    )

    if args.print_status:
        dbg.print_status()
        return

    if args.create_singleton:
        dbg.create_singleton(args.fix_missing_edits)
        return

    if args.reroll:
        dbg.set_proof()
        return

    if args.collect_garbage:
        dbg.collect_garbage()
        return

    if args.reset_proof_cache:
        dbg.reset_proof_cache()
        return

    dbg.print_status()

if __name__ == "__main__":
    main()
