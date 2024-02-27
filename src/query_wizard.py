import argparse
from utils.option_utils import *
from query.core_builder import BasicCoreBuilder
from query.proof_builder import ProofBuilder
from query.query_utils import convert_verus_smtlib
from solver.runner import SolverRunner

def add_timeout_option(parser):
    parser.add_argument("--timeout", default=150, help="the timeout (seconds) for the solver")

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
    p = subparsers.add_parser('get-proof', help='get lfcs proof from a query with cvc5')
    add_input_query_option(p)
    add_output_log_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def run_build_core(args):
    BasicCoreBuilder(args.input_query_path, args.solver, args.output_query_path, args.timeout, args.clear).run()

def run_get_proof(args):
    ProofBuilder(args.input_query_path, args.output_log_path,  args.timeout, args.clear).run()

# def setup_quake(subparsers):
#     p = subparsers.add_parser('quake', help='emit quake file')
#     add_input_option(p)
#     add_output_option(p)
#     parser.add_argument("--quake-count", default=4, help="number of times to perform quake")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Query Wizard operates on the single-query level. Typically, the input is a single smt2 query, and the output is a new query and/or a log file.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    setup_build_core(subparsers)
    setup_convert_smt_lib(subparsers)
    setup_get_proof(subparsers)

    args = parser.parse_args()

    if hasattr(args, "solver"):
        args.solver = SolverRunner(args.solver)

    if args.sub_command == "build-core":
        run_build_core(args)
    elif args.sub_command == "convert-smtlib":
        convert_verus_smtlib(args.input, args.output)
    elif args.sub_command == "get-proof":
        run_get_proof(args)
    else:
        parser.print_help()


