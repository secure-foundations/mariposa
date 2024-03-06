#!/usr/bin/env python3

import argparse, time, pickle
from base.project import Project
from base.defs import MARIPOSA, NINJA_BUILD_FILE, NINJA_LOG_FILE, NINJA_REPORTS_DIR, QUERY_WIZARD
from utils.option_utils import *
from utils.system_utils import *

NINJA_BUILD_RULES = f"""
rule split
    command = {MARIPOSA} -i $in -o $out -a split --convert-comments

rule format
    command = {MARIPOSA} -i $in -o $out -a format

rule shake
    command = {MARIPOSA} -i $in -o $out -a shake --shake-log-path $log

rule build-core
    command = {QUERY_WIZARD} build-core -i $in -o $out --timeout 150
    
rule convert-smtlib
    command = {QUERY_WIZARD} convert-smtlib -i $in -o $out

rule get-proof
    command = {QUERY_WIZARD} get-proof -i $in --output-log-path $out --timeout 30 $clear


"""

# rule instantiate
#     command = ./target/release/mariposa -i $in --trace-log $log -o $out

# rule z3-trace
#     command = ./solvers/z3-4.12.2 $in -T:150 trace=true trace_file_name=$out

# rule shake-special
#     command = {MARIPOSA} -i $in -o $out -m tree-shake --shake-log-path $log --shake-max-symbol-frequency 25

# rule shake-partial
#     command = python3 scripts/run_shake.py partial $out $in $full $log

# rule strip
#     command = ./target/release/mariposa -i $in -o $out -m remove-unused

# rule complete-mini-query
#     command = python3 scripts/unsat_core_search.py complete $in $hint $out > $out.log

# rule reduce-query
#     command = python3 scripts/unsat_core_search.py reduce $in $out > $out.log

# rule iterate-reduce-query
#     command = python3 scripts/unsat_core_search.py reduce $in $in > $out

# rule check-subset
#     command = python3 scripts/diff_smt.py subset-check $in $sub && touch $out

def set_up_create(subparsers):
    p = subparsers.add_parser('create', help='create a new project')
    add_input_dir_option(p, False)
    add_new_project_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_build_core(subparsers):
    p = subparsers.add_parser('build-core', help='create unsat core project form a base project. the output directory is set using the project manager conventions.')
    add_input_dir_option(p)
    add_solver_option(p)
    add_timeout_option(p)
    add_clear_option(p)

def set_up_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format, by default, the output directory is set using the project manager conventions')
    add_input_dir_option(p)
    add_clear_option(p)

def set_up_get_proof(subparsers):
    p = subparsers.add_parser('get-proof', help='get lfcs proof from a query with cvc5')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)
    
def set_up_load_stat(subparsers):
    p = subparsers.add_parser('load-stat', help='load build stats from a previous run')
    p.add_argument("-i", "--input-log-file", required=True, help="the input file (.pkl) to load")

class NinjaPasta:
    def __init__(self, args, cmd):
        self.start_time = int(time.time())
        self.ninja_stuff = []
        self.target_count = 0

        self.output_dir = None
        self.clear = args.clear_existing
        
        self.saved_cmd = cmd
        
        self.record = args.record_build_stats

        if args.sub_command == "load-stat":
            self.print_build_stats(args.input_log_file)
            return

        if args.sub_command == "create":
            self.handle_create(args.new_project_name)
        elif args.sub_command == "build-core":
            self.handle_build_core(args.input_proj)
        elif args.sub_command == "convert-smtlib":
            self.handle_convert_smt_lib(args.input_proj)
        elif args.sub_command == "get-proof":
            self.handle_get_proof()
        else:
            parser.print_help()

        self.finalize()

    def handle_create(self, new_project_name):
        import re

        log_check(re.match("^[a-z0-9_]*$", new_project_name),
                    "invalid project name in preprocess")

        out_proj = Project(new_project_name)
        output_dir = out_proj.sub_root
        log_info(f"output directory is set to {output_dir}")

        for in_path in list_smt2_files(args.input_dir):
            out_path = convert_path(in_path, args.input_dir, output_dir)
            self.ninja_stuff += [f"build {out_path}: split {in_path}\n"]
            self.target_count += 1

    def handle_build_core(self, args, in_proj):
        out_proj = FACT.get_core_project(in_proj, build=True)

        output_dir = out_proj.sub_root
        self.output_dir = output_dir
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(args.input_dir):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(output_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: build-core {in_path}\n"]
            self.target_count += 1

    def handle_convert_smt_lib(self, in_proj):
        out_proj = FACT.get_cvc5_counterpart(in_proj, build=True)

        log_info(f"converting queries in {self.in_proj.sub_root}")

        self.output_dir = out_proj.sub_root
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(self.in_proj.sub_root):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(self.output_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: convert-smtlib {in_path}\n"]
            self.target_count += 1

    def handle_get_proof(self, in_proj):
        mapping = in_proj.map_to_lfscs()
        self.output_dir = in_proj.log_dir

        for (i, o) in mapping.items():
            self.ninja_stuff += [f"build {o}: get-proof {i}\n"]
            if self.clear:
                self.ninja_stuff += [f"    clear=--clear-existing\n\n"]
            self.target_count += 1

    def finalize(self):
        if len(self.ninja_stuff) == 0:
            log_info("no targets to build")
            return
        reset_dir(self.output_dir, self.clear)

        ninja_stuff = [NINJA_BUILD_RULES] + self.ninja_stuff
        self.ninja_stuff = "".join(ninja_stuff) 

        with open(NINJA_BUILD_FILE, "w+") as f:
            f.write(self.ninja_stuff)

        log_info(f"generated {self.target_count} targets in {NINJA_BUILD_FILE}")

        confirm_input(f"run `ninja -j 6 -k 0` to start building?")

        if os.path.exists(NINJA_LOG_FILE):
            os.remove(NINJA_LOG_FILE)

        os.system("ninja -j 6 -k 0")

        if self.record:
            self.save_build_stats()

    def save_build_stats(self):
        ninja_log = open(NINJA_LOG_FILE).readlines()
        count = 0

        targets = dict()
        for line in ninja_log[1:]:
            line = line.strip().split("\t")
            elapse = (int(line[1]) - int(line[0])) / 1000
            targets = {line[3]: elapse}
            count += 1

        metadata = dict()
        metadata = {"cmd": self.saved_cmd,
                "ninja_stuff": self.ninja_stuff,
                "targets": targets}
        
        out_path = os.path.join(NINJA_REPORTS_DIR, str(self.start_time), ".pkl")

        with open(out_path, "wb") as f:
            pickle.dump(metadata, f)
            
        self.print_build_stats(out_path)

    def print_build_stats(self, input_log_file):
        with open(input_log_file, "rb") as f:
            metadata = pickle.load(f)
        print(metadata["cmd"])

        for k, v in metadata["targets"].items():
            print(f"{k}: {v}ms")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Project Wizard operates on the single-project level. Typically, the input is a project/directory (containing a set of queries), and the output is another project (with a set of queries), or with a set of log files. Project Wizard is a thin wrapper around the Query Wizard and the Rust code base.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    set_up_create(subparsers)
    set_up_build_core(subparsers)
    set_up_convert_smt_lib(subparsers)
    set_up_get_proof(subparsers)
    set_up_load_stat(subparsers)
    
    cmd = " ".join(sys.argv)

    args = parser.parse_args()
    args = deep_parse_args(args)

    ninja = NinjaPasta(args, cmd)
