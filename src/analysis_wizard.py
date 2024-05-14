#!/usr/bin/env python3

import argparse
import random
from analysis.core_analyzer import CoreAnalyzer
from base.defs import MARIPOSA_GROUPS
from base.exper_analyzer import ExperAnalyzer
from analysis.inst_analyzer import InstAnalyzer
from analysis.perf_analyzer import PrefAnalyzer
from analysis.shake_analyzer import ShakeAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.factory import FACT
from base.query_analyzer import Stability
from utils.option_utils import *
from proj_wizard import *
from utils.shake_utils import parse_shake_log, load_query_cids
from base.query_analyzer import Stability as STB

def set_up_basic(subparsers):
    p = subparsers.add_parser('basic', help='analyze the results of an existing experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_basic(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_status(args.category_verbosity, args.query_verbosity)

def set_up_verify(subparsers):
    p = subparsers.add_parser('verify', help='analyze the verification performance only')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_verify(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.print_plain_status()

def set_up_cvc5_perf(subparsers):
    p = subparsers.add_parser('perf', help='analyze the raw performance of cvc5/z3 on a project group')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def set_up_cvc5_inst(subparsers):
    p = subparsers.add_parser('inst', help='analyze the instantiation logs from cvc5')
    add_input_dir_option(p)

def set_up_unstable(subparsers):
    p = subparsers.add_parser('unstable', help='analyze the unstable reasons of an experiment')
    add_input_dir_option(p)
    add_analysis_options(p)

def handle_unstable(args):
    exp = args.experiment
    log_check(exp.is_done(), "experiment results do not exist")
    ba = ExperAnalyzer(exp, args.analyzer)
    ba.get_failure_types().print_status()

def set_up_core(subparsers):
    p = subparsers.add_parser('core', help='analyze the core')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def set_up_shake(subparsers):
    p = subparsers.add_parser('shake', help='analyze shake')
    add_input_dir_option(p, is_group=True)
    add_analysis_options(p)

def handle_shake(args):
    group = args.input_group
    shake = ShakeAnalyzer(group)

def set_up_wombo(subparsers):
    p = subparsers.add_parser('wombo', help='no help is coming')
    add_input_dir_option(p, is_group=True)

def find_oracle_path(qid):
    for group in "fs_dice", "d_fvbkv", "d_lvbkv", "d_komodo", "fs_vwasm":
        if qid.startswith(group):
            actual = qid[len(group)+2:]
            return f"data/projs/{group}/shko.cvc5/{actual}.smt2"
    assert False
    
def valid_max(scores):
    return max([s for s in scores if not np.isnan(s)])

def handle_special():
    # proj = FACT.get_project_by_path("data/projs/data/projs/fs_dice/base.z3")
    # ana = FACT.get_analyzer("60nq")
    # exp = FACT.load_any_analysis(proj, ana)
    ana = FACT.get_analyzer("60nq")
    group = FACT.get_group("pre_cvc5")
    proj = group.get_project("base.cvc5")
    solver = FACT.get_solver("cvc5_1_1_1")
    cfg = FACT.get_config("debug")

    exp = FACT.load_analysis(
        proj, cfg, solver, ana)
    
    groups = {gid: set() for gid in MARIPOSA_GROUPS}
    stable = exp.stability_categories[STB.STABLE].items
    for qid in stable:
        # qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid].add(qid)

    problems = 0
    for gid in groups:
        samples = set(random.sample(groups[gid], 111)) - {"semantics-common-queries-Semantics.Common.CFG.LLInstructionSemantics-20.smt2"}
        samples = list(samples)
        for qid in samples[:110]:
            oracle = find_oracle_path(f"{gid}--{qid}")
            if not os.path.exists(oracle):
                problems += 1
                continue
            print("cp", find_oracle_path(f"{gid}--{qid}"), f"data/projs/bench_stable_cvc5/shko.cvc5/{gid}--{qid}.smt2")
        # print(gid, len(groups[gid]))
        # qr.print_status(1)
    # proj = group.get_project("shko.cvc5")
    
    # group = FACT.get_group("fs_dice")
    # ca = CoreAnalyzer(group)
    # for qid in ca.base.stability_categories[Stability.UNSTABLE]:
    #     qr = ca.qids[qid]
    #     in_path = qr.base_path
    #     patch_path = qr.patch_path
    #     log_path = f"data/logs/fs_dice.special/base.z3/shk-log/{qid}.shk_log"
    #     ot_path = f"data/projs/fs_dice.special/shko.z3/{qid}.smt2"

    #     # print(f"./src/smt2action/target/release/mariposa -a shake -i {in_path} --shake-max-symbol-frequency 30 --shake-log-path {log_path}")
    #     scores = parse_shake_log(log_path)
    #     if qr.patch_path == qr.base_path:
    #         max_core = np.nan
    #         comp = np.nan
    #     else:
    #         core_path = qr.patch_path + ".fixed"
    #         core_cids = load_query_cids(core_path)
    #         core_scores = [scores[cid] for cid in core_cids.keys()]
    #         max_core = valid_max(core_scores)
    #         comp = 0 if np.nan in core_scores else 1
    #     max_base = valid_max(scores.values())
    #     # print(f"{qid} {max_base} {max_core} {comp}")
    #     if np.isnan(max_core):
    #         max_core = 6
    #     print(f"./src/smt2action/target/release/mariposa -a shake --shake-max-symbol-frequency 30 -i {in_path} -o {ot_path} --shake-max-depth {max_core}")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Mariposa Analysis Wizard is a tool to analyze Mariposa experiment results. ")
    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run analysis in")

    set_up_basic(subparsers)
    set_up_verify(subparsers)
    set_up_cvc5_perf(subparsers)
    set_up_cvc5_inst(subparsers)
    set_up_unstable(subparsers)
    set_up_core(subparsers)
    set_up_shake(subparsers)
    set_up_wombo(subparsers)
    p = subparsers.add_parser('special', help='placeholder for special analysis')

    args = parser.parse_args()
    args = deep_parse_args(args)

    if args.sub_command == "basic":
        handle_basic(args)
    elif args.sub_command == "verify":
        handle_verify(args)
    elif args.sub_command == "perf":
        PrefAnalyzer(args.input_group, args.analyzer)
    elif args.sub_command == "inst":
        InstAnalyzer(args.input_proj)
    elif args.sub_command == "unstable":
        handle_unstable(args)
    elif args.sub_command == "core":
        ca = CoreAnalyzer(args.input_group)
        ca.print_status()
    elif args.sub_command == "shake":
        handle_shake(args)
    elif args.sub_command == "wombo":
        WomboAnalyzer(args.input_group)
    elif args.sub_command == "special":
        handle_special()
    else:
        parser.print_help()
