import os, numpy as np
from base.defs import NINJA_REPORTS_DIR
from base.project import KnownExt, Project
from proj_wizard import NinjaStats
from utils.cache_utils import load_cache, save_cache
from utils.analysis_utils import PartialCDF, print_sets_diff
from utils.system_utils import log_check, log_warn
from utils.plot_utils import *
import enum

def parse_cvc5_inst(log_file_path):
    with open(log_file_path, "r") as f:
        lines = f.readlines()

    quant = None
    
    quants = dict()
    for line in lines:
        # print(line)
        line = line.strip()

        if line.startswith("(instantiations"):
            quant = line[16:]
            quants[quant] = set()
        elif line.startswith("(skolem"):
            quant = line[8:]
            quants[quant] = set()
        elif line.startswith("( "):
            assert(quant is not None)
            assert(line.endswith(" )"))
            inst = line[1:-1]
            quants[quant].add(inst)
        else:
            if line not in {")", "unsat"}:
                log_warn(f"unknown line: {line}")
            quant = None

    # for k in quants:
    #     print(f"{k}: {len(quants[k])}")
    return quants

class InstAnalyzer:
    def __init__(self, in_proj: Project):
        # save_cache("woot.pkl", quants)
        quants = load_cache("woot.pkl")
        all_quants = dict()

        for k, qt in quants.items():
            for q in qt:
                if q not in all_quants:
                    all_quants[q] = 0
                all_quants[q] += 1

        all_quants = dict(sorted(all_quants.items(), key=lambda item: item[1], reverse=True))
        qc = np.array(list(all_quants.values()))

        print("total number of queries: ", len(quants))
        print("total number of quantifiers: ", len(all_quants))
        print("number of quantifiers unique to query: ", np.sum([qc == 1]))
        print("most common quantifiers:")
        for k in list(all_quants.keys())[:10]:
            print(f"\t{k}\t\t-- in {all_quants[k]} queries")

        all_insts = dict()
        all_quants = dict()
        no_qt = 0

        for k, qt in quants.items():
            all_insts[k] = 0
            all_quants[k] = len(qt)
            for q in qt:
                all_insts[k] += len(qt[q])
            if len(qt) == 0:
                no_qt += 1

        print("queries with no quantifiers: ", no_qt)
        all_insts = dict(sorted(all_insts.items(), key=lambda item: item[1], reverse=True))
        all_quants = dict(sorted(all_quants.items(), key=lambda item: item[1], reverse=True))
        print("")
        print("queries with most quantifiers:")
        for k in list(all_quants.keys())[:10]:
            print(f"\t{k}.smt2\t\t-- has {all_quants[k]} quantifiers")
        print("")
        print("queries with most instantiations:")
        for k in list(all_insts.keys())[:10]:
            print(f"\t{k}.smt2\t\t-- has {all_insts[k]} instantiations")

        # plt.hist(list(all_quants.values()), bins=100)
        # plt.savefig("inst_hist.png")
        # aqt = PartialCDF(list(all_quants.values()))
        # print(list(aqt.xs))
        
        