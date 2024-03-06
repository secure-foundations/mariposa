#!/usr/bin/env python3

import argparse, os
from utils.option_utils import *
from query.core_builder import BasicCoreBuilder
from query.proof_builder import ProofBuilder
from utils.query_utils import convert_verus_smtlib, emit_quake_query

def setup_build_core(subparsers):
    p = subparsers.add_parser('build-core', help='create core query form a given query')
    add_input_query_option(p)
    add_output_query_option(p)
    add_solver_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def setup_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format')
    add_input_query_option(p)
    add_output_query_option(p)

def setup_get_proof(subparsers):
    p = subparsers.add_parser('get-proof', help='get lfsc proof from a query with cvc5')
    add_input_query_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def setup_emit_quake(subparsers):
    p = subparsers.add_parser('emit-quake', help='emit quake file')
    add_input_query_option(p)
    add_output_query_option(p)
    add_timeout_option(p)
    parser.add_argument("--quake-count", default=4, help="number of iterations to perform quake")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Query Wizard operates on the single-query level. Typically, the input is a single smt2 query, and the output is a new query and/or a log file. Please note there are operations that in the Rust codebase that are not exposed here. Instead, use the built binary directly.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    setup_build_core(subparsers)
    setup_convert_smt_lib(subparsers)
    setup_get_proof(subparsers)
    setup_emit_quake(subparsers)

    args = parser.parse_args()
    args = deep_parse_args(args)

    if hasattr(args, "output_query_path"):
        directory = os.path.dirname(args.output_query_path)
        if directory != "" and not os.path.exists(directory):
            os.makedirs(directory)

    if args.sub_command == "build-core":
        BasicCoreBuilder(args.input_query_path,
                         args.solver, 
                         args.output_query_path, 
                         args.timeout, 
                         args.clear_existing).run()
    elif args.sub_command == "convert-smtlib":
        convert_verus_smtlib(args.input_query_path, 
                             args.output_query_path)
    elif args.sub_command == "get-proof":
        ProofBuilder(args.input_query_path, 
                     args.output_log_path,
                     args.timeout, 
                     args.clear_existing).run()
    elif args.sub_command == "emit-quake":
        emit_quake_query(args.input_query_path, 
                         args.output_query_path, 
                         args.timeout, 
                         args.quake_count)
    else:
        parser.print_help()
