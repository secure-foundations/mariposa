#!/usr/bin/env python3

import argparse, os
from base.defs import GEN_ROOT
from base.factory import FACT
from base.solver import Z3Solver
from query.core_completer import CoreCompleter
from query.inst_builder import InstBuilder
from utils.option_utils import *
from query.core_builder import MutCoreBuilder
from query.proof_builder import ProofBuilder, check_lfsc_proof
from utils.query_utils import convert_verus_smtlib, emit_mutant_query, emit_quake_query, is_assertion_subset
from utils.system_utils import get_name_hash, log_check, remove_file

def setup_build_core(subparsers):
    p = subparsers.add_parser('build-core', help='create core query form a given query by performing mutations')
    add_input_query_option(p)
    add_output_query_option(p)
    add_solver_option(p)
    add_timeout_option(p)

def setup_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format')
    add_input_query_option(p)
    add_output_query_option(p)

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
    p.add_argument("--mutation", default="none", help="the mutation to perform before tracing")
    p.add_argument("--seed", default=MAGIC_IGNORE_SEED, help="the seed to use")
    add_input_query_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def handle_trace_z3(input_query, output_trace, mutation, seed, timeout):
    solver: Z3Solver = FACT.get_solver_by_name("z3_4_12_5")
    remove_file(output_trace)
    
    if mutation not in {Mutation.NONE, Mutation.RESEED}:
        name_hash = get_name_hash(input_query)
        actual_query = f"{GEN_ROOT}/{name_hash}.{mutation}.{seed}.smt2"
        remove_file(actual_query)
        emit_mutant_query(input_query, actual_query, mutation, seed)
        seed = None
    else:
        actual_query = input_query

    solver.trace(actual_query, timeout, output_trace, seeds=seed)

    if actual_query != input_query:
        remove_file(actual_query)

    log_check(os.path.exists(output_trace), f"failed to create {output_trace}")

def setup_emit_quake(subparsers):
    p = subparsers.add_parser('emit-quake', help='emit quake file')
    add_input_query_option(p)
    add_output_query_option(p)
    add_timeout_option(p)
    parser.add_argument("--quake-count", default=4, help="number of iterations to perform quake")

def setup_verify(subparsers):
    p = subparsers.add_parser('verify', help='run verification on a query')
    add_input_query_option(p)
    add_output_log_option(p)
    add_solver_option(p)
    add_timeout_option(p)

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

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Query Wizard operates on the single-query level. Typically, the input is a single smt2 query, and the output is a new query and/or a log file. Please note there are operations that in the Rust codebase that are not exposed here. Instead, use the built binary directly.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    setup_build_core(subparsers)
    setup_convert_smt_lib(subparsers)
    setup_get_lfsc(subparsers)
    setup_get_inst(subparsers)
    setup_check_lfsc(subparsers)
    setup_emit_quake(subparsers)
    setup_verify(subparsers)
    setup_trace_z3(subparsers)
    setup_check_subset(subparsers)
    setup_complete_core(subparsers)

    args = parser.parse_args()
    args = deep_parse_args(args)

    if hasattr(args, "output_query_path"):
        directory = os.path.dirname(args.output_query_path)
        if directory != "" and not os.path.exists(directory):
            os.makedirs(directory)

    if args.sub_command == "build-core":
        MutCoreBuilder(args.input_query_path,
                         args.solver, 
                         args.output_query_path, 
                         args.timeout)
    elif args.sub_command == "convert-smtlib":
        convert_verus_smtlib(args.input_query_path, 
                             args.output_query_path)
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
                    args.mutation,
                    args.seed,
                    args.timeout)
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
    elif args.sub_command == "verify":
        ver = args.solver.verify(args.input_query_path, args.timeout)
        log_check(ver, f"verification failed")
        open(args.output_log_path, "w+").write("verified")
    elif args.sub_command == "check-subset":
        log_check(is_assertion_subset(args.input_query_path, args.subset_query), f"{args.subset_query} is not a subset of {args.input_query_path}")
    else:
        parser.print_help()
