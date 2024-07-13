import argparse
import multiprocessing
import os
from analysis.shake_context import handle_core_context_analysis, handle_shake_context_analysis
from analysis.core_analyzer import CoreAnalyzer
from analysis.wombo_analyzer import WomboAnalyzer
from base.defs import MARIPOSA, MARIPOSA_GROUPS
from base.exper_analyzer import QueryAnaResult
from base.factory import FACT
from base.project import KnownExt, Project, ProjectType as PT
from base.query_analyzer import Stability as STB
from base.solver import RCode
from utils.analysis_utils import Categorizer, PartialCDF
from utils.cache_utils import has_cache, load_cache, load_cache_or, save_cache
from utils.option_utils import deep_parse_args
from utils.query_utils import count_asserts, normalize_line
from utils.system_utils import log_info, log_warn, subprocess_run
from utils.plot_utils import *
import random
from matplotlib import pyplot as plt
import numpy as np
from tqdm import tqdm

def get_query_shake_time(path):
    o = subprocess_run(f"{MARIPOSA} -a shake -i {path}", shell=True)[0]
    o = o.split("\n")
    assert len(o) == 2
    parse_time = int(o[0].split(": ")[-1])
    shake_time = int(o[1].split(": ")[-1])
    return parse_time, shake_time

def get_shake_times(gid):
    cache_name= f"shake_times_{gid}"

    if has_cache(cache_name):
        return load_cache(cache_name)

    pool = multiprocessing.Pool(6)

    group = FACT.get_group(gid)
    base = group.get_project("base.z3")

    paths = [base.get_path(qid) for qid in base.qids]
    pts, sts = zip(*pool.map(get_query_shake_time, paths))

    shake_times = {}

    for i, qid in enumerate(base.qids):
        shake_times[qid] = (pts[i], sts[i])

    save_cache(cache_name, shake_times)
    return shake_times

SURVIVAL_TEX_LABELS = {
    "base.z3": "Baseline Z3",
    "shkf.z3": "Default Shake Z3",
    "shko.z3": "Oracle Shake Z3",
    "base.cvc5": "Baseline CVC5",
    "shkf.cvc5": "Default Shake CVC5",
    "shko.cvc5": "Oracle Shake CVC5",
}

def perf_delta(base, new):
    prefix = ""
    if new > base:
        prefix = "+"
    return prefix + "%.2f" % round((new - base) * 100 / base, 2) + "\%"

def handle_shake_survival():
    # solved = {}
    # for gid in MARIPOSA_GROUPS:
    #     solved[gid] = _handle_shake_survival(gid)
    
    solved = {'d_komodo': {'base.z3': 1983, 'shkf.z3': 1981, 'shko.z3': 1989, 'base.cvc5': 342, 'shkf.cvc5': 348, 'shko.cvc5': 416}, 'd_fvbkv': {'base.z3': 5103, 'shkf.z3': 5063, 'shko.z3': 5072, 'base.cvc5': 2571, 'shkf.cvc5': 2806, 'shko.cvc5': 3105}, 'd_lvbkv': {'base.z3': 5167, 'shkf.z3': 5146, 'shko.z3': 5165, 'base.cvc5': 3158, 'shkf.cvc5': 3439, 'shko.cvc5': 3569}, 'fs_dice': {'base.z3': 1493, 'shkf.z3': 1492, 'shko.z3': 1498, 'base.cvc5': 259, 'shkf.cvc5': 449, 'shko.cvc5': 683}, 'fs_vwasm': {'base.z3': 1733, 'shkf.z3': 1728, 'shko.z3': 1727, 'base.cvc5': 1630, 'shkf.cvc5': 1628, 'shko.cvc5': 1628}}
    
    overall = [0 for _ in range(6)]    
    for proj, perf in solved.items():
        meta = GROUP_PLOT_META[proj]
        row = [meta.tex_cmd]
        z3 = perf["base.z3"]
        row += ["z3", z3, perf_delta(z3, perf["shkf.z3"]), perf_delta(z3, perf["shko.z3"])]
        overall[0] += z3
        overall[1] += perf["shkf.z3"]
        overall[2] += perf["shko.z3"]
        print(" & ".join(map(str, row)) + " \\\\")
        cvc5 = perf["base.cvc5"]
        row = ["", "cvc5", cvc5, perf_delta(cvc5, perf["shkf.cvc5"]), perf_delta(cvc5, perf["shko.cvc5"])]
        print(" & ".join(map(str, row)) + " \\\\")
        print("\\midrule")
        overall[3] += cvc5
        overall[4] += perf["shkf.cvc5"]
        overall[5] += perf["shko.cvc5"]
    
    print("\\midrule")
    row = ["Overall"]
    row += ["z3", overall[0], perf_delta(overall[0], overall[1]), perf_delta(overall[0], overall[2])]
    print(" & ".join(map(str, row)) + " \\\\")
    row = ["", "cvc5", overall[3], perf_delta(overall[3], overall[4]), perf_delta(overall[3], overall[5])]
    print(" & ".join(map(str, row)) + " \\\\")
    print("\\midrule")

def _handle_shake_survival(gid):
    plt.figure(figsize=(5, 3.5))
    ana = FACT.get_analyzer("60nq")
    group = FACT.get_group(gid)
    shake_times = get_shake_times(gid)
    
    # base_z3 = FACT.load_any_analysis(group.get_project("base.z3"), ana)
    # base_cvc5 = FACT.load_any_analysis(group.get_project("base.cvc5"), ana)
    
    # qids = base_z3.qids
    # oracle_fallback_ids = set()
    # shko = FACT.load_any_analysis(group.get_project("shko.z3"), ana)
    # shkf = group.get_project("shko.z3")

    # for qid in qids:
    #     if qid not in shko.qids:
    #         oracle_fallback_ids.add(qid)
    #     elif shko[qid].get_original_status()[0] != RCode.UNSAT.value:
    #         shake_log = base_z3.get_path(qid, KnownExt.SHK_LOG)
    #         if not os.path.exists(shake_log):
    #             # os.system(f"{MARIPOSA} -a shake -i {base_z3.get_path(qid)} --shake-log-path {shake_log} -o {shkf.get_path(qid)}")
    #             print(f"{MARIPOSA} -a shake -i {base_z3.get_path(qid)} --shake-log-path {shake_log} -o {shkf.get_path(qid)}")
                # core_cids = load_query_cids(qcs.patch_path)

    solved = {}
    for poj in ["base.z3", "shkf.z3", "shko.z3", "base.cvc5", "shkf.cvc5", "shko.cvc5"]:
        exp = FACT.load_any_analysis(group.get_project(poj), ana)
        perf = []

        for qid in exp.qids:
            # if poj.startswith("shko"):
            #     pass
            # else:
            qr: QueryAnaResult = exp[qid]

            rc, et = qr.get_original_status()

            if poj.startswith("shk"):
                et += shake_times[qid][1]

            if rc == RCode.UNSAT.value and et < 6e4:
                perf += [et/1000]

        if poj.startswith("shko"):
            style = "dashed"
        elif poj.startswith("shkf"):
            style = "dotted"
        else:
            style = "solid"

        if poj.endswith("z3"):
            color = "red"
        else:
            color = "blue"

        label = SURVIVAL_TEX_LABELS[poj]
        perf = np.array(np.sort(perf))
        perf = np.cumsum(perf)
        plt.plot(perf, np.arange(0, len(perf)), label=label, linestyle=style, color=color)
        solved[poj] = len(perf)

    plt.legend(fontsize=8)
    plt.ylim(0)
    plt.xlim(0.1)
    plt.xscale("log")
    plt.xlabel("Cumulative Time Log Scale (s)")
    plt.ylabel("Instances Soveld")
    plt.grid()
    plt.tight_layout()
    plt.savefig(f"fig/survival/shake_{gid}.pdf",bbox_inches='tight',pad_inches = 0)
    plt.close()
    
    return solved