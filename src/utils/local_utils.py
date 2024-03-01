import subprocess
import sys
from analysis.basic_analyzer import BasicAnalyzer
from base.defs import MARIPOSA
from base.runner import Runner

from utils.option_utils import deep_parse_args
from utils.system_utils import list_smt2_files, log_check, log_info, log_warn, reset_dir

def handle_single(args):
    args = deep_parse_args(args)

    in_query = args.input_query_path
    exp = args.experiment
    output_dir = exp.proj.sub_root

    if exp.sum_table_exists() and args.clear == False:
        log_warn(f"experiment results already exists for {output_dir}")
        BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    reset_dir(output_dir, args.clear)
    command = f"{MARIPOSA} -i {in_query} -o {exp.proj.sub_root}/split.smt2 -a split"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    log_check(result.returncode == 0, "single mode split failed!")

    if list_smt2_files(output_dir) == []:
        log_info(f"no queries were generated from {in_query}")
        sys.exit(0)

    r = Runner()
    r.run_project(exp, args.clear)
    BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)

def handle_multiple(args):
    args = deep_parse_args(args)
    exp = args.experiment

    if exp.sum_table_exists() and args.clear == False:
        log_warn(f"experiment results already exists for {exp.proj.sub_root}")
        BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    r = Runner()
    r.run_project(exp, args.clear)
    BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)
    return (exp.db_path, args.part)
