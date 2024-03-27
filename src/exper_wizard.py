#!/usr/bin/env python3

import argparse
import copy
from utils.cluster_utils import handle_code_sync, handle_data_sync, handle_manager, handle_recovery, handle_code_sync, handle_worker
from utils.local_utils import handle_single, handle_multiple, handle_info, handle_update
from utils.option_utils import *
from proj_wizard import *

def set_up_single(subparsers):
    p = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')
    add_input_query_option(p)
    add_experiment_options(p)

def set_up_multi(subparsers):
    p = subparsers.add_parser('multiple', help='multiple query (project) mode. experiment with an existing (preprocessed) project using the specified solver')
    add_input_dir_option(p)
    add_experiment_options(p)
    p.add_argument("--fix-missing", default=False, action="store_true", help="the input query")

def set_up_update(subparsers):
    p = subparsers.add_parser('update', help='add a new query to existing experiment OR re-run the experiment on the specified query and update the existing database.')
    add_input_dir_option(p)
    p.add_argument("--input-query-path", required=True, help="the input query")
    add_experiment_options(p)

def set_up_manager(subparsers):
    p = subparsers.add_parser('manager', help='sever pool manager mode.')
    add_input_dir_option(p)
    add_experiment_options(p)
    add_authkey_option(p)
    p.add_argument("--total-parts", type=int, required=True, help="number of parts to split the project into")

def set_up_worker(subparsers):
    p = subparsers.add_parser('worker', help='server pool worker mode.')
    add_authkey_option(p)
    p.add_argument("--manager-addr", required=True, help="the address of the manager node")

def set_up_recovery(subparsers):
    p = subparsers.add_parser('recovery', help='recovery mode. recover an existing experiment by (adding) a single query.')
    add_input_dir_option(p)
    add_experiment_options(p)

def set_up_data_sync(subparsers):
    p = subparsers.add_parser('data-sync', help='sync a project to another server (only for serenity)')
    add_input_dir_option(p)
    add_clear_option(p)

def set_up_info(subparsers):
    p = subparsers.add_parser('info', help='list available projects and experiment results')

def set_up_code_sync(subparsers):
    p = subparsers.add_parser('code-sync', help='update the cluster')

def set_up_stop_all(subparsers):
    p = subparsers.add_parser('stop-all', help='stop all workers and manager on the cluster')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Mariposa Experiment Wizard is a tool for testing SMT proof stability. this is the main tool to run experiments.")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    set_up_single(subparsers)
    set_up_multi(subparsers)
    set_up_info(subparsers)
    set_up_manager(subparsers)
    set_up_worker(subparsers)
    set_up_data_sync(subparsers)
    set_up_code_sync(subparsers)
    set_up_recovery(subparsers)
    set_up_update(subparsers)
    set_up_stop_all(subparsers)

    args = parser.parse_args()
    wargs = copy.deepcopy(args)
    args = deep_parse_args(args)

    if args.sub_command == "single":
        handle_single(args)
    elif args.sub_command == "multiple":
        handle_multiple(args)
    elif args.sub_command == "update":
        handle_update(args)
    elif args.sub_command == "info":
        handle_info(args)
    elif args.sub_command == "manager":
        handle_manager(args, wargs)
    elif args.sub_command == "worker":
        handle_worker(args)
    elif args.sub_command == "data-sync":
        handle_data_sync(args.input_dir, args.clear_existing)
    elif args.sub_command == "code-sync":
        handle_code_sync()
    elif args.sub_command == "recovery":
        handle_recovery(args)
    elif args.sub_command == "stop-all":
        handle_stop()
    else:
        parser.print_help()
