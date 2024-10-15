import multiprocessing

import numpy as np
from tabulate import tabulate
from analysis.core_analyzer import CoreAnalyzer
from base.defs import MARIPOSA_GROUPS
from base.exper_analyzer import QueryAnaResult
from base.factory import FACT
from utils.analysis_utils import PartialCDF
from utils.cache_utils import *
from utils.plot_utils import *
from utils.query_utils import count_asserts
from matplotlib import pyplot as plt
from base.query_analyzer import Stability as STB

def handle_core_stability_analysis():
    data = dict()

    for gid in MARIPOSA_GROUPS:
        group = FACT.get_group(gid)
        ana = CoreAnalyzer(group, FACT.get_analyzer("60nq"))
        base = ana.base_adj
        core = ana.core_adj

        base_stable = base[STB.STABLE].items
        base_unstable = base[STB.UNSTABLE].items

        core_unstable = core[STB.UNSTABLE].items
        core_stable = core[STB.STABLE].items

        data[gid] = [
                len(base_stable),
                len(core_stable),
                len(base_unstable),
                len(core_unstable),
                len(base_unstable & core_stable),
                len(base_stable & core_stable),
            ]

    print(data)

def __load_shake_oracle_results_z3():
    groups = {gid: [0, 0, 0, 0] for gid in MARIPOSA_GROUPS}
    groups["Overall"] = [0, 0, 0, 0]
    
    group = FACT.get_group("bench_unstable_simp")
    exp = FACT.load_default_analysis(group.get_project("shko.z3"))

    for qid in exp.qids:
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][0] += 1
        groups["Overall"][0] += 1
        if qr.stability == STB.STABLE:
            groups[gid][1] += 1
            groups["Overall"][1] += 1
            
    group = FACT.get_group("bench_stable")
    exp = FACT.load_default_analysis(group.get_project("shko.z3"))

    for qid in exp.qids:
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][2] += 1
        groups["Overall"][2] += 1
        if qr.stability == STB.STABLE:
            groups[gid][3] += 1
            groups["Overall"][3] += 1
    return groups

def __load_shake_oracle_results_cvc5():
    groups = {gid: [0, 0, 0, 0] for gid in MARIPOSA_GROUPS}
    groups["Overall"] = [0, 0, 0, 0]

    ana = FACT.get_analyzer("60nq")
    group = FACT.get_group("bench_unstable_cvc5")
    proj = group.get_project("base.cvc5")
    solver = FACT.get_solver("cvc5_1_1_1")
    cfg = FACT.get_config("default")

    exp = FACT.load_analysis(
        proj, cfg, solver, ana)
    
    unstable = exp.stability_categories[STB.UNSTABLE].items

    proj = group.get_project("shko.cvc5")
    exp = FACT.load_analysis(
        proj, cfg, solver, ana)

    for qid in exp.qids:
        if qid not in unstable:
            continue
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][0] += 1
        groups["Overall"][0] += 1
        if qr.stability == STB.STABLE:
            groups[gid][1] += 1
            groups["Overall"][1] += 1

    group = FACT.get_group("bench_stable_cvc5")
    proj = group.get_project("shko.cvc5")
    exp = FACT.load_analysis(
        proj, cfg, solver, ana)
    
    for qid in exp.qids:
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][2] += 1
        groups["Overall"][2] += 1
        if qr.stability == STB.STABLE:
            groups[gid][3] += 1
            groups["Overall"][3] += 1

    return groups

def __load_naive_shake_oracle_results_z3():
    groups = {gid: [0, 0, 0, 0] for gid in MARIPOSA_GROUPS}
    groups["Overall"] = [0, 0, 0, 0]

    group = FACT.get_group("bench_unstable.special")
    exp = FACT.load_default_analysis(group.get_project("shko.z3"))

    for qid in exp.qids:
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][0] += 1
        groups["Overall"][0] += 1
        if qr.stability == STB.STABLE:
            groups[gid][1] += 1
            groups["Overall"][1] += 1
            
    group = FACT.get_group("bench_stable.special")
    exp = FACT.load_default_analysis(group.get_project("shko.z3"))

    for qid in exp.qids:
        qr = exp[qid]
        gid, qid = qid.split("--")
        groups[gid][2] += 1
        groups["Overall"][2] += 1
        if qr.stability == STB.STABLE:
            groups[gid][3] += 1
            groups["Overall"][3] += 1
    return groups


def handle_shake_stability_analysis():
    # data = __load_shake_oracle_results_z3()
    # data = __load_shake_oracle_results_cvc5()
    data = __load_naive_shake_oracle_results_z3()

    def into_row(name, data):
        [unstable, mitigated, stable, preserved] = data
        return [
            name,
            tex_fmt_int(stable),
            tex_fmt_int(unstable),
            tex_fmt_percent(preserved * 100 / stable) + "\%",
            tex_fmt_percent(mitigated * 100 / unstable) + "\%",
        ]

    table = []
    for gid in MARIPOSA_GROUPS:
        tex_cmd = GROUP_PLOT_META[gid].tex_cmd
        table.append(into_row(tex_cmd, data[gid]))
    table.append(into_row("Overall", data["Overall"]))

    print("\midrule")

    for row in table:
        print(" & ".join(row) + " \\\\")
