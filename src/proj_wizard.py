#!/usr/bin/env python3

import argparse, time, pickle, numpy as np
from base.project import KnownExt, Project, ProjectType, full_proj_name, get_qid
from base.defs import MARIPOSA, NINJA_BUILD_FILE, NINJA_LOG_FILE, NINJA_REPORTS_DIR, PROJ_ROOT, QUERY_WIZARD
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

rule get-lfsc
    command = {QUERY_WIZARD} get-lfsc -i $in --output-log-path $out --timeout 30 $clear

rule get-inst
    command = {QUERY_WIZARD} get-inst -i $in --output-log-path $out --timeout 30 

rule verify
    command = {QUERY_WIZARD} verify -i $in --output-log-path $out -s $solver --timeout 30
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
    add_ninja_log_option(p)

def set_up_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format, by default, the output directory is set using the project manager conventions')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_get_proof(subparsers):
    p = subparsers.add_parser('get-lfsc', help='get lfcs proof from a query with cvc5')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)
    
def set_up_get_inst(subparsers):
    p = subparsers.add_parser('get-inst', help='get instantiations from a query using cvc5')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_verify(subparsers):
    p = subparsers.add_parser('verify', help='run verification on a query')
    add_input_dir_option(p)
    add_solver_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_load_stat(subparsers):
    p = subparsers.add_parser('load-stat', help='load build stats from a previous run')
    p.add_argument("-i", "--input-log-file", required=True, help="the input file (.pkl) to load")

class NinjaPasta:
    def __init__(self, args, cmd):
        self.start_time = int(time.time())
        self.ninja_stuff = []
        self.expect_targets = set()

        self.output_dir = None
        self.saved_cmd = cmd

        if args.sub_command == "load-stat":
            self.print_build_stats(args.input_log_file)
            return

        ext = None

        if args.sub_command == "create":
            self.handle_create(args.new_project_name, args.input_dir)
        elif args.sub_command == "build-core":
            self.handle_build_core(args.input_proj)
        elif args.sub_command == "convert-smtlib":
            self.handle_convert_smt_lib(args.input_proj)
        elif args.sub_command == "get-lfsc":
            # always record build stats for proof generation
            args.record_build_stats = True
            ext = self.handle_get_proof(args.input_proj, args.clear_existing)
        elif args.sub_command == "get-inst":
             self.handle_get_inst(args.input_proj, args.clear_existing)
        elif args.sub_command == "verify":
            # always record build stats for verification
            args.record_build_stats = True
            ext = self.handle_verify(args.input_proj, args.solver)
        else:
            parser.print_help()
            return

        self.finalize(args.clear_existing)

        if args.record_build_stats:
            log_check(ext != None, "extension not intended for build stats!")
            build_meta_path = args.input_proj.get_build_meta_path(ext)
            self.save_build_stats(build_meta_path)
        
        count = subprocess_run(f"ls {self.output_dir} | wc -l", shell=True)[0]
        log_info(f"generated {count} files in {self.output_dir}")

    def handle_create(self, gid, input_dir):
        log_check(is_simple_id(gid), 
                  "invalid project name in preprocess")
        self.output_dir = os.path.join(PROJ_ROOT, gid, str(Project.DEFAULT_PTYPE))
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(input_dir):
            out_path = convert_path(in_path, input_dir, self.output_dir)
            self.ninja_stuff += [f"build {out_path}: split {in_path}\n"]
            self.expect_targets.add(out_path)

    def handle_build_core(self, in_proj):
        output_dir = in_proj.get_alt_dir(ProjectType.from_str("core.z3"))

        self.output_dir = output_dir
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(in_proj.sub_root):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(output_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: build-core {in_path}\n"]
            self.expect_targets.add(out_path)

    def handle_convert_smt_lib(self, in_proj):
        output_dir = in_proj.get_alt_dir(in_proj.ptype.switch_solver())
        log_info(f"converting queries in {in_proj.sub_root}")
        self.output_dir = output_dir
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(in_proj.sub_root):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(self.output_dir, base_name)
            self.ninja_stuff += [f"build {out_path}: convert-smtlib {in_path}\n"]
            self.expect_targets.add(out_path)

    def handle_get_proof(self, in_proj, clear):
        ext = KnownExt.LFSC
        self.output_dir = in_proj.get_log_dir(ext)
        for qid in in_proj.qids:
            i = in_proj.get_ext_path(qid)
            o = in_proj.get_ext_path(qid, ext)
            self.ninja_stuff += [f"build {o}: get-lfsc {i}\n"]
            if clear:
                self.ninja_stuff += [f"    clear=--clear-existing\n\n"]
            self.expect_targets.add(o)
        return ext

    def handle_get_inst(self, in_proj, clear):
        ext = KnownExt.CVC_INST
        self.output_dir = in_proj.get_log_dir(ext)
        for qid in in_proj.qids:
            i = in_proj.get_ext_path(qid)
            o = in_proj.get_ext_path(qid, ext)
            self.ninja_stuff += [f"build {o}: get-inst {i}\n\n"]
            self.expect_targets.add(o)
        return ext

    def handle_verify(self, in_proj, solver):
        ext = KnownExt.VERI
        self.output_dir = in_proj.get_log_dir(ext)
        for qid in in_proj.qids:
            i = in_proj.get_ext_path(qid)
            o = in_proj.get_ext_path(qid, ext)
            self.ninja_stuff += [f"build {o}: verify {i}\n",
                                 f"    solver={solver.name}\n\n"]
            self.expect_targets.add(o)
        return ext

    def finalize(self, clear):
        if len(self.ninja_stuff) == 0:
            log_info("no targets to build")
            return
        reset_dir(self.output_dir, clear)

        ninja_stuff = [NINJA_BUILD_RULES] + self.ninja_stuff
        self.ninja_stuff = "".join(ninja_stuff) 

        with open(NINJA_BUILD_FILE, "w+") as f:
            f.write(self.ninja_stuff)

        log_info(f"generated {len(self.expect_targets)} targets in {NINJA_BUILD_FILE}")

        confirm_input(f"run `ninja -j 6 -k 0` to start building?")

        if os.path.exists(NINJA_LOG_FILE):
            os.remove(NINJA_LOG_FILE)

        os.system("ninja -j 6 -k 0")

    def save_build_stats(self, meta_path):
        ninja_log = open(NINJA_LOG_FILE).readlines()

        built_targets = dict()

        for line in ninja_log[1:]:
            line = line.strip().split("\t")
            target = line[3]
            elapse = (int(line[1]) - int(line[0])) / 1000
            if not os.path.exists(target):
                log_warn(f"target {target} does not exist")
            else:
                built_targets[target] = elapse

        metadata = {
            "cmd": self.saved_cmd,
            "ninja_stuff": self.ninja_stuff,
            "expect_targets": self.expect_targets,
            "built_targets": built_targets}

        if not os.path.exists(NINJA_REPORTS_DIR):
            os.makedirs(NINJA_REPORTS_DIR)

        with open(meta_path, "wb") as f:
            pickle.dump(metadata, f)
            f.close()

        self.print_build_stats(meta_path)

    def print_build_stats(self, input_log_file):
        with open(input_log_file, "rb") as f:
            metadata = pickle.load(f)

        print(metadata["cmd"])

        build_times = []
        for k, v in metadata["built_targets"].items():
            build_times.append(v)

        print("proj command:\n\t" + metadata["cmd"])
        print(f"{len(metadata['built_targets'])}/{len(metadata['expect_targets'])} targets built")

        build_times = np.array(build_times)
        print("min: %.2fs" % np.min(build_times))
        print("median: %.2fs" % np.median(build_times))
        print("max: %.2fs" % np.max(build_times))

class NinjaStats:
    def __init__(self, input_log_path):
        with open(input_log_path, "rb") as f:
            metadata = pickle.load(f)

        self.expected = set()
        self.built = dict()

        for k in metadata["expect_targets"]:
            self.expected.add(get_qid(k))

        for k, v in metadata["built_targets"].items():
            k = get_qid(k)
            log_check(k in self.expected, "unexpected built targets")
            self.built[k] = v

        for k in self.expected - set(self.built.keys()):
            self.built[k] = np.nan

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mariposa Project Wizard operates on the single-project level. Typically, the input is a project/directory (containing a set of queries), and the output is another project (with a set of queries), or with a set of log files. Project Wizard is a thin wrapper around the Query Wizard and the Rust code base.")
    subparsers = parser.add_subparsers(dest='sub_command', help="the sub-command to run")

    set_up_create(subparsers)
    set_up_build_core(subparsers)
    set_up_convert_smt_lib(subparsers)
    set_up_get_proof(subparsers)
    set_up_get_inst(subparsers)
    set_up_load_stat(subparsers)
    set_up_verify(subparsers)

    cmd = " ".join(sys.argv)

    args = parser.parse_args()
    args = deep_parse_args(args)

    ninja = NinjaPasta(args, cmd)
