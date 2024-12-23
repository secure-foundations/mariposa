#!/usr/bin/env python3

from os import path
import argparse, time, pickle, numpy as np
from base.exper import Experiment
from base.factory import FACT
from base.project import KnownExt, Project, ProjectType as PT, get_qid
from base.defs import MARIPOSA, NINJA_BUILD_FILE, NINJA_LOG_FILE, NINJA_REPORTS_DIR, PROJ_ROOT, QUERY_WIZARD
from utils.option_utils import *
from utils.system_utils import *

NINJA_BUILD_RULES = f"""
rule split
    command = {MARIPOSA} -i $in -o $out -a split --convert-comments

rule format
    command = {MARIPOSA} -i $in -o $out -a format

rule build-core
    command = {QUERY_WIZARD} build-core -i $in -o $out --timeout 10 -s z3_4_12_5 --ids-available --restarts 10

rule add-ids
    command = {MARIPOSA} -i $in -o $out -a add-ids

rule complete-core
    command = {QUERY_WIZARD} complete-core -i $in -o $out --core-query-path $core 

rule convert-smtlib
    command = {QUERY_WIZARD} convert-smtlib -i $in -o $out $inc

rule get-lfsc
    command = {QUERY_WIZARD} get-lfsc -i $in --output-log-path $out --timeout 60 $clear

rule check-lfsc
    command = {QUERY_WIZARD} check-lfsc --input-log-path $in --output-log-path $out --timeout 30

rule get-inst
    command = {QUERY_WIZARD} get-inst -i $in --output-log-path $out --timeout 30 

rule trace-z3
    command = {QUERY_WIZARD} trace-z3 -i $in --output-log-path $out --timeout $timeout --mutation $mutation --seed $seed

rule check-subset
    command = {QUERY_WIZARD} subset-check $in $sub && touch $out

rule shake
    command = {MARIPOSA} -i $in -o $out -a shake

rule shake-log
    command = {MARIPOSA} -i $in -a shake --shake-log-path $out

rule shake-log-naive
    command = {MARIPOSA} -i $in -a shake-naive --shake-log-path $out

rule pre-inst-z3
    command = {MARIPOSA} -i $in -o $out -a pre-inst-z3

rule inst-z3
    command = {QUERY_WIZARD} inst-z3 -i $in -o $out --timeout 5 --restarts 30

rule query-stat
    command = {MARIPOSA} -a stat -i $in --stat-log-path $out

"""

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

def set_up_build_z3_trace(subparsers):
    p = subparsers.add_parser('build-trace', help='build z3 traces out of unstable queries in a project')
    add_input_dir_option(p)
    add_timeout_option(p)
    add_analysis_options(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_convert_smt_lib(subparsers):
    p = subparsers.add_parser('convert-smtlib', help='convert a verus query to smt-lib standard (cvc5) format, by default, the output directory is set using the project manager conventions')
    add_input_dir_option(p)
    add_clear_option(p)
    add_incremental_option(p)
    add_ninja_log_option(p)

def set_up_get_proof(subparsers):
    p = subparsers.add_parser('get-lfsc', help='get lfcs proof from queries with cvc5')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_get_core_proof(subparsers):
    p = subparsers.add_parser('get-core-lfsc', help='get lfcs proof from core queries with cvc5')
    # TODO: this might get confusing since we are assuming that the core.cvc5 project will be used
    add_input_dir_option(p, is_group=True)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_check_proof(subparsers):
    p = subparsers.add_parser('check-lfsc', help='check lfcs proofs')
    add_input_dir_option(p, is_group=True)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_get_inst(subparsers):
    p = subparsers.add_parser('get-inst', help='get instantiations from a query using cvc5')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_load_stat(subparsers):
    p = subparsers.add_parser('load-stat', help='load build stats from a previous run')
    p.add_argument("-i", "--input-log-file", required=True, help="the input file (.pkl) to load")

def set_up_create_benchmark(subparsers):
    p = subparsers.add_parser('create-benchmark', help='create a benchmark project (do not use this unless you know what you are doing)')
    add_clear_option(p)

def set_up_log_shake(subparsers):
    p = subparsers.add_parser('log-shake', help='create shake logs for a project')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)
    p.add_argument("--frequency", default=100, required=True, help="shake max symbol frequency")

def set_up_log_shake_naive(subparsers):
    p = subparsers.add_parser('log-shake-naive', help='create shake logs for a project')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

def set_up_query_stat(subparsers):
    p = subparsers.add_parser('query-stat', help='query stats')
    add_input_dir_option(p)
    add_clear_option(p)
    add_ninja_log_option(p)

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

        args.record_build_stats = False

        if args.sub_command == "create":
            self.handle_create(args.new_project_name, args.input_dir)
        elif args.sub_command == "build-core":
            self.handle_build_core(args.input_proj)
        elif args.sub_command == "build-trace":
            self.handle_build_z3_trace(args.experiment)
        elif args.sub_command == "convert-smtlib":
            self.handle_convert_smt_lib(args.input_proj)
        elif args.sub_command == "get-lfsc":
            # always record build stats for proof generation
            args.record_build_stats = True
            ext = self.handle_get_proof(args.input_proj, args.clear_existing)
        elif args.sub_command == "get-core-lfsc":
            ext = self.handle_get_core_proof(args.input_group, args.clear_existing)
        elif args.sub_command == "check-lfsc":
            ext = self.handle_check_proof(args.input_group, args.clear_existing)
        elif args.sub_command == "get-inst":
             self.handle_get_inst(args.input_proj, args.clear_existing)
        elif args.sub_command == "create-benchmark":
            self.handle_create_benchmark()
        elif args.sub_command == "log-shake":
            self.handle_create_shake_log(args.input_proj, int(args.frequency))
        elif args.sub_command == "log-shake-naive":
            self.handle_create_naive_shake_log(args.input_proj)
        elif args.sub_command == "time-shake":
            self.handle_time_shake(args.input_proj)
        elif args.sub_command == "query-stat":
            self.handle_create_stat_log(args.input_proj)
        else:
            parser.print_help()
            return

        self.finalize(args.clear_existing, args.no_build)

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
        output_dir = in_proj.get_alt_dir(PT.from_str("core.z3"))

        self.output_dir = output_dir
        log_info(f"output directory is set to {self.output_dir}")

        for in_path in list_smt2_files(in_proj.sub_root):
            base_name = os.path.basename(in_path)
            out_path = os.path.join(output_dir, base_name)
            if os.path.exists(out_path):
                continue
            self.ninja_stuff += [f"build {out_path}: build-core {in_path}\n"]
            self.expect_targets.add(out_path)

    def handle_build_z3_trace(self, exp: Experiment):
        log_check(exp.sum_table_exists(), "experiment results do not exist")
        ba = ExperAnalyzer(exp, args.analyzer)
        unstables = ba.get_unstable_query_mutants()
        self.output_dir = exp.proj.get_log_dir(KnownExt.Z3_TRACE)

        for (qr, pms, fms) in unstables:
            in_path = qr.query_path
            for (m, s, _) in pms + fms:
                out_path = os.path.join(self.output_dir, f"{qr.qid}.{m}.{s}.{KnownExt.Z3_TRACE}")
                self.ninja_stuff += [
                    f"build {out_path}: trace-z3 {in_path}\n"
                    f"    timeout={args.timeout}\n",
                    f"    mutation={m}\n",
                    f"    seed={s}\n"]
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
            if args.incremental:
                self.ninja_stuff += f"    inc=--incremental\n"
            else:
                self.ninja_stuff += f"    inc=\n"
            self.expect_targets.add(out_path)

    def handle_get_proof(self, in_proj, clear):
        ext = KnownExt.LFSC
        self.output_dir = in_proj.get_log_dir(ext)
        for qid in in_proj.qids:
            i = in_proj.get_path(qid)
            o = in_proj.get_path(qid, ext)
            self.ninja_stuff += [f"build {o}: get-lfsc {i}\n"]
            if clear:
                self.ninja_stuff += [f"    clear=--clear-existing\n\n"]
            self.expect_targets.add(o)
        return ext

    def handle_get_core_proof(self, in_group, clear):
        ext = KnownExt.LFSC
        # base_z3 = in_group.get_project(PT.from_str("base.z3"))
        # core_z3 = in_group.get_project(PT.from_str("core.z3"))
        base_cvc5 = in_group.get_project(PT.from_str("base.cvc5"))
        core_cvc5 = in_group.get_project(PT.from_str("core.cvc5"))

        self.output_dir = core_cvc5.get_log_dir(ext)

        for qid in base_cvc5.qids:
            o = base_cvc5.get_path(qid, ext)
            i = core_cvc5.get_path(qid)

            if os.path.exists(o):
                continue

            if not os.path.exists(i):
                log_warn(f"missing core query {i}, skipping...")
                o = core_cvc5.get_path(qid, ext)
                self.ninja_stuff += [f"build {o}: get-lfsc {i}\n"]
                if clear:
                    self.ninja_stuff += [f"    clear=--clear-existing\n\n"]
                self.expect_targets.add(o)

        log_info(f"output directory is set to {self.output_dir}")
        log_info("after the build, you may wish to run the following command to move the proof files:")
        print(f"mv {self.output_dir}/*.lfsc {base_cvc5.get_log_dir(KnownExt.LFSC)}")

    def handle_check_proof(self, in_group, clear):
        in_ext = KnownExt.LFSC
        out_ext = KnownExt.LFSC_CHK
        base_cvc5 = in_group.get_project(PT.from_str("base.cvc5"))
        self.output_dir = base_cvc5.get_log_dir(out_ext)
        for qid in base_cvc5.qids:
            o = base_cvc5.get_path(qid, out_ext)
            i = base_cvc5.get_path(qid, in_ext)
            if not os.path.exists(i):
                log_warn(f"missing input proof {qid}.{in_ext}")
                continue
            self.ninja_stuff += [f"build {o}: check-lfsc {i}\n"]
            
    def handle_get_inst(self, in_proj, clear):
        ext = KnownExt.CVC_INST
        self.output_dir = in_proj.get_log_dir(ext)
        for qid in in_proj.qids:
            i = in_proj.get_path(qid)
            o = in_proj.get_path(qid, ext)
            self.ninja_stuff += [f"build {o}: get-inst {i}\n\n"]
            self.expect_targets.add(o)
        return ext

    # def handle_create_benchmark(self):
    #     self.output_dir = "data/projs/bench_unstable/base.z3"
    #     log_info(f"output directory is set to {self.output_dir}")
    #     ana = QueryAnalyzer("60nq")
    #     for gid in ["d_fvbkv", "d_lvbkv", "d_komodo", "fs_vwasm", "fs_dice"]:
    #         group = FACT.get_group(gid)
    #         proj = group.get_project(PT.from_str("base.z3"))
    #         exp = FACT.load_any_experiment(proj)
    #         exp = ExperAnalyzer(exp, ana)

    #         for qid in exp.get_overall()[Stability.UNSTABLE]:
    #             i = proj.get_path(qid)
    #             o = os.path.join(self.output_dir, f"{gid}--{qid}.smt2")
    #             if not os.path.exists(o):
    #                 log_warn(f"skipping query {i}")
    #                 continue
    #             self.ninja_stuff += [f"build {o}: add-ids {i}\n"]
    #     random.shuffle(self.ninja_stuff)
        
    def handle_create_shake_log(self, in_proj, frequency):
        self.output_dir = in_proj.get_log_dir(KnownExt.SHK_LOG)
        # ot_proj = in_proj.get_alt_dir(PT.from_str("shkf.z3"))
        assert 0 < frequency and frequency <= 100

        self.ninja_stuff += [f"""
rule shake-log-{frequency}
    command = {MARIPOSA} -i $in -a shake --shake-log-path $out --shake-max-symbol-frequency {frequency}
"""]

        for qid in in_proj.qids:
            i = in_proj.get_path(qid)
            l = in_proj.get_path(qid + "." + str(frequency) , KnownExt.SHK_LOG)

            self.ninja_stuff += [f"build {l}: shake-log-{frequency} {i}\n"]
            self.expect_targets.add(l)

            # o = path.join(ot_proj, f"{qid}.smt2")
            # self.ninja_stuff += [f"build {o}: shake {i}\n", 
            #                      f"    log={l}\n"]

    def handle_create_naive_shake_log(self, in_proj):
        group = FACT.get_group(in_proj.gid)
        ot_proj = group.get_project(PT.from_str("shkn.z3"), build=True)
        # in_proj.get_alt_dir(PT.from_str("shkn.z3"))
        for qid in in_proj.qids:
            i = in_proj.get_path(qid)
            # o = ot_proj.get_path(qid)
            l = ot_proj.get_path(qid, KnownExt.SHK_LOG)
            self.ninja_stuff += [f"build {l}: shake-log-naive {i}\n"]

    def handle_time_shake(self, in_proj):
        pass

    def handle_create_stat_log(self, in_proj):
        self.output_dir = in_proj.get_log_dir(KnownExt.Q_LOG)
        for qid in in_proj.qids:
            i = in_proj.get_path(qid)
            o = in_proj.get_path(qid, KnownExt.Q_LOG)
            self.ninja_stuff += [f"build {o}: query-stat {i}\n"]
            self.expect_targets.add(o)

    def finalize(self, clear, no_build):
        if len(self.ninja_stuff) == 0:
            log_info("no targets to build")
            return
        # reset_dir(self.output_dir, clear)

        ninja_stuff = [NINJA_BUILD_RULES] + self.ninja_stuff
        self.ninja_stuff = "".join(ninja_stuff) 

        with open(NINJA_BUILD_FILE, "w+") as f:
            f.write(self.ninja_stuff)

        log_info(f"generated {len(self.expect_targets)} targets in {NINJA_BUILD_FILE}")

        if no_build:
            return

        # confirm_input(f"run `ninja -j 14 -k 0` to start building?")

        if os.path.exists(NINJA_LOG_FILE):
            os.remove(NINJA_LOG_FILE)

        os.system("ninja -j 7 -k 0")

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
    set_up_build_z3_trace(subparsers)
    set_up_convert_smt_lib(subparsers)
    set_up_get_proof(subparsers)
    set_up_get_core_proof(subparsers)
    set_up_check_proof(subparsers)
    set_up_get_inst(subparsers)
    set_up_load_stat(subparsers)
    set_up_create_benchmark(subparsers)
    set_up_log_shake(subparsers)
    set_up_query_stat(subparsers)
    set_up_log_shake_naive(subparsers)

    cmd = " ".join(sys.argv)

    args = parser.parse_args()
    args = deep_parse_args(args)

    ninja = NinjaPasta(args, cmd)
