#!/usr/bin/env python3

import argparse, os

from query.combo_builder import handle_inst_z3, handle_trace_z3
from query.core_completer import CoreCompleter
from query.inst_builder import InstBuilder
from utils.option_utils import *
from query.core_builder import CompleteCoreBuilder, MutCoreBuilder
from query.proof_builder import ProofBuilder, check_lfsc_proof
from utils.query_utils import convert_smtlib, emit_quake_query, is_assertion_subset
from utils.shake_utils import create_shake_query_from_log, debug_shake
from utils.system_utils import log_check

def setup_build_core(subparsers):
    p = subparsers.add_parser('build-core', help='create core query form a given query (by performing mutations)')
    add_input_query_option(p)
    add_output_query_option(p)
    add_restart_option(p)
    add_solver_option(p)
    add_timeout_option(p)
    p.add_argument("--complete", default=False, action="store_true", help="try to complete the core query after building it")
    p.add_argument("--ids-available", default=False, action="store_true", help="whether ids are available in the query")

def setup_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format')
    add_input_query_option(p)
    add_output_query_option(p)
    add_incremental_option(p)

def setup_get_lfsc(subparsers):
    p = subparsers.add_parser('get-lfsc', help='get lfsc proof from a query with cvc5')
    add_input_query_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def setup_get_inst(subparsers):
    p = subparsers.add_parser('get-inst', help='get instantiations from a query (using cvc5)')
    add_input_query_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)
    
def setup_check_lfsc(subparsers):
    p = subparsers.add_parser('check-lfsc', help='check lfsc proof')
    add_input_log_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def setup_trace_z3(subparsers):
    p = subparsers.add_parser('trace-z3', help='get trace from z3')
    add_input_query_option(p)
    p.add_argument("--search", default=False, action="store_true", help="search for a (shuffled) mutant that would produce unsat, output the trace of the mutant, otherwise, output the trace of the original query, regardless of unsat or not")
    add_restart_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def setup_emit_quake(subparsers):
    p = subparsers.add_parser('emit-quake', help='emit quake file')
    add_input_query_option(p)
    add_output_query_option(p)
    add_timeout_option(p)
    parser.add_argument("--quake-count", default=4, help="number of iterations to perform quake")

def setup_check_subset(subparsers):
    p = subparsers.add_parser('check-subset', help='check if a query is a subset of another')
    add_input_query_option(p)
    p.add_argument("--subset-query", required=True, help="the query that is supposed to be a subset")

def setup_complete_core(subparsers):
    p = subparsers.add_parser('complete-core', help='complete core query')
    add_input_query_option(p)
    p.add_argument("--core-query-path", required=True, help="the core query")
    add_output_query_option(p)
    add_solver_option(p)
    add_timeout_option(p)

def setup_debug_shake(subparsers):
    p = subparsers.add_parser('debug-shake', help='debug shake')
    add_input_query_option(p)
    add_input_log_option(p)
    p.add_argument("--core-query-path", required=True, help="the core query")

def setup_create_shake(subparsers):
    p = subparsers.add_parser('create-shake', help='create shake query')
    add_input_query_option(p)
    add_input_log_option(p)
    add_output_query_option(p)
    p.add_argument("--max-score", required=True, help="the maximum score")

def setup_inst_z3(subparsers):
    p = subparsers.add_parser('inst-z3', help='use trace and core to build a reduced query')
    add_input_query_option(p)
    add_output_query_option(p)
    add_restart_option(p)
    add_timeout_option(p)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Query Wizard operates on the single-query level. Typically, the input is a single smt2 query, and the output is a new query and/or a log file. Please note there are operations that in the Rust codebase that are not exposed here. Instead, use the built binary directly.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    setup_build_core(subparsers)
    setup_convert_smt_lib(subparsers)
    setup_get_lfsc(subparsers)
    setup_get_inst(subparsers)
    setup_check_lfsc(subparsers)
    setup_emit_quake(subparsers)
    setup_trace_z3(subparsers)
    setup_check_subset(subparsers)
    setup_complete_core(subparsers)
    setup_debug_shake(subparsers)
    setup_create_shake(subparsers)
    setup_inst_z3(subparsers)

    args = parser.parse_args()
    args = deep_parse_args(args)

    if hasattr(args, "output_query_path"):
        directory = os.path.dirname(args.output_query_path)
        if directory != "" and not os.path.exists(directory):
            os.makedirs(directory)

    if args.sub_command == "build-core":
        if args.complete:
            CompleteCoreBuilder(args.input_query_path,
                        args.output_query_path, 
                        args.solver, 
                        args.timeout,
                        args.ids_available,
                        args.restarts)
        else:
            m = MutCoreBuilder(args.input_query_path,
                        args.output_query_path, 
                        args.solver, 
                        args.timeout,
                        args.ids_available,
                        args.restarts)
            m.run()
    elif args.sub_command == "convert-smtlib":
        convert_smtlib(args.input_query_path, 
                        args.output_query_path,
                        args.incremental)
    elif args.sub_command == "get-lfsc":
        ProofBuilder(args.input_query_path, 
                     args.output_log_path,
                     args.timeout, 
                     args.clear_existing).run()
    elif args.sub_command == "check-lfsc":
        check_lfsc_proof(args.input_log_path, 
                     args.output_log_path,
                     args.timeout, 
                     args.clear_existing)
    elif args.sub_command == "get-inst":
        InstBuilder(args.input_query_path, 
                    args.output_log_path, 
                    args.timeout, 
                    args.clear_existing)
    elif args.sub_command == "trace-z3":
        handle_trace_z3(args.input_query_path, 
                    args.output_log_path, 
                    args.search,
                    args.timeout,
                    args.restarts)
    elif args.sub_command == "emit-quake":
        emit_quake_query(args.input_query_path, 
                         args.output_query_path, 
                         args.quake_count)
    elif args.sub_command == "complete-core":
        CoreCompleter(args.input_query_path, 
                      args.core_query_path, 
                      args.solver,
                      args.output_query_path, 
                      args.timeout)
    elif args.sub_command == "check-subset":
        log_check(is_assertion_subset(args.input_query_path, args.subset_query), 
                  f"{args.subset_query} is not a subset of {args.input_query_path}")
    elif args.sub_command == "debug-shake":
        debug_shake(args.input_query_path, 
                    args.core_query_path, 
                    args.input_log_path)
    elif args.sub_command == "create-shake":
        create_shake_query_from_log(args.input_query_path, 
                                    args.input_log_path, 
                                    int(args.max_score),
                                    args.output_query_path)
    elif args.sub_command == "inst-z3":
        handle_inst_z3(args.input_query_path, 
                              args.output_query_path, 
                              args.timeout, 
                              args.restarts)
    else:
        parser.print_help()
