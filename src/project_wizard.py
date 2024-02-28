#!/usr/bin/env python3.8

import argparse, shutil
from base.project import PM, Project, ProjectType
from utils.option_utils import *
from utils.system_utils import *

MARIPOSA = "./src/smt2action/target/release/mariposa"
QUERY_WIZARD = "./src/query_wizard.py"

NINJA_BUILD_RULES = f"""
rule split
    command = {MARIPOSA} -i $in -o $out -a split

rule format
    command = {MARIPOSA} -i $in -o $out -a format

rule shake
    command = {MARIPOSA} -i $in -o $out -a shake --shake-log-path $log

rule build-core
    command = {QUERY_WIZARD} build-core -i $in -o $out
    
rule convert-smtlib
    command = {QUERY_WIZARD} convert-smtlib -i $in -o $out

rule get-proof
    command = {QUERY_WIZARD} get-proof -i $in -o $out
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

def set_up_known_project(p):
    add_project_option(p, required=False)
    add_input_dir_option(p)
    add_clear_option(p)

def set_up_preprocess(subparsers):
    p = subparsers.add_parser('preprocess', help='preprocess the project')
    add_input_dir_option(p)
    add_output_dir_option(p)
    add_project_option(p, required=False)

def set_up_build_core(subparsers):
    p = subparsers.add_parser('build-core', help='create unsat core project form a base project')
    set_up_known_project(p)
    add_solver_option(p)
    add_timeout_option(p)

def set_up_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format')
    set_up_known_project(p)

class NinjaPasta:
    def __init__(self, args):
        self.ninja_stuff = []
        self.target_count = 0

        self.out_dir = None
        self.clear = args.clear
        
        if args.sub_command == "preprocess":
            self.handle_preprocess(args)
            return

        proj = load_known_input_project(args)

        if args.sub_command == "build-core":
            self.handle_build_core(args)
        elif args.sub_command == "convert-smtlib":
            self.handle_convert_smt_lib(args)
        elif args.sub_command == "info-proj":
            PM.list_projects()
        else:
            parser.print_help()

    def handle_preprocess(self, args):
        self.out_dir = args.output_dir

        for in_path in list_smt2_files(args.input_dir):
            out_path = convert_path(in_path, args.input_dir, args.output_dir)
            self.ninja_stuff += [f"build {out_path}: split {in_path}\n"]
            self.target_count += 1

    def handle_build_core(self, args):
        in_proj = load_known_input_project(args)
        out_proj = PM.get_core_project(in_proj, build=True)

        output_dir = out_proj.sub_root
        self.out_dir = output_dir
        log_info(f"output directory is set to {self.out_dir}")

        for in_path in list_smt2_files(args.input_dir):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(output_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: build-core {in_path}\n"]
            self.target_count += 1

    def handle_convert_smt_lib(self, args):
        in_proj = load_known_input_project(args)
        out_proj = PM.get_cvc5_counterpart(in_proj, build=True)

        log_info(f"converting queries in {in_proj.sub_root}")

        self.out_dir = out_proj.sub_root
        log_info(f"output directory is set to {self.out_dir}")

        for in_path in list_smt2_files(in_proj.sub_root):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(self.out_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: convert-smtlib {in_path}\n"]
            self.target_count += 1

    def finalize(self):
        if len(self.ninja_stuff) == 0:
            log_info("no targets to build")
            return

        create_output_dir(self.out_dir, self.clear)

        ninja_stuff = [NINJA_BUILD_RULES] + self.ninja_stuff
        with open("build.ninja", "w+") as f:
            f.write("\n".join(ninja_stuff))

        log_info(f"generated {self.target_count} targets in build.ninja")
        print("run `ninja -j 6` to start building? [Y]", end=" ")

        if input() != "Y":
            print("exiting")
            sys.exit(0)

        os.system("ninja -j 6")

        log_info(f"generated {get_file_count(self.out_dir)} files in {self.out_dir}")

def load_known_input_project(args) -> Project:
    has_in_dir = hasattr(args, "input_dir") and os.path.isdir(args.input_dir)
    has_proj = hasattr(args, "project") and args.project is not None

    san_check(not (has_in_dir and has_proj), "should not specify both an input directory and a project")

    san_check(has_in_dir or has_proj, "must specify either an input directory or a project")

    if has_in_dir:
        return PM.get_project_by_path(args.input_dir)

    return PM.get_project(args.project, args.ptype)

def create_output_dir(out_dir, clear):
    if not can_overwrite_dir(out_dir):
        if not clear:
            print(f"output directory {out_dir} already exists, remove it? [Y]", end=" ")
            san_check(input() == "Y", f"aborting")
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)

def reparse_args(args):
    if hasattr(args, "ptype"):
        args.ptype = ProjectType.from_str(args.ptype)

    return args

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Project Wizard operates on the single-project level. Typically, the input is a project/directory (containing a set of queries), and the output is another project (with a set of queries), or with a set of log files. Project Wizard is a thin wrapper around the Query Wizard and the Rust code base.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    set_up_preprocess(subparsers)
    set_up_build_core(subparsers)
    set_up_convert_smt_lib(subparsers)
    p = subparsers.add_parser('info-proj', help='list known projects (from the current file system)')
    # set_up_get_proof(subparsers)

    args = parser.parse_args()
    args = reparse_args(args)

    # if hasattr(args, "ptype"):
    #     args.ptype = ProjectType.from_str(args.ptype)
    
    ninja = NinjaPasta(args)
    ninja.finalize()
