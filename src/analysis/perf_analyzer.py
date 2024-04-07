import os, numpy as np
from analysis.expr_analyzer import ExperAnalyzer
from base.defs import NINJA_REPORTS_DIR
from base.factory import FACT
from base.project import Project, ProjectGroup, KnownExt as KE
from base.solver import RCode, SolverType as ST
from proj_wizard import NinjaStats
from query.analyzer import QueryAnalyzer
from utils.analysis_utils import PartialCDF, print_sets_diff
from utils.system_utils import log_check
from utils.plot_utils import *

class PrefAnalyzer:
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        gid = group.gid
        z3_pt = Project.DEFAULT_PTYPE
        z3_p = group.get_project(z3_pt)
        cvc5_p = group.get_project(z3_pt.switch_solver())
        z3_e = FACT.load_any_experiment(z3_p)
        z3_e = ExperAnalyzer(z3_e, ana)

        cvc5_e = FACT.load_any_experiment(cvc5_p)
        cvc5_e = ExperAnalyzer(cvc5_e, ana)

        data = []
        cvc5_tos = []
        for qid in z3_e.qids:
            qr = z3_e[qid]
            rc, z3_et = qr.get_original_status()
            if rc != RCode.UNSAT.value:
                continue
            qr = cvc5_e[qid]
            rc, cvc5_et = qr.get_original_status()
            if rc == RCode.UNSAT.value:
                data += [(z3_et, cvc5_et)]
            else:
                cvc5_tos += [(z3_et, cvc5_et)]
        np_data = np.array(data)
        cvc5_tos = np.array(cvc5_tos)
        fig, ax = plt.subplots(1, 1, squeeze=False)
        sp = ax[0, 0]

        sp.scatter(np_data[:,0]/1000, np_data[:,1]/1000, label="cvc5 passes", alpha=0.5)
        sp.scatter(cvc5_tos[:,0]/1000, cvc5_tos[:,1]/1000, label="cvc5 fails", alpha=0.5)
        
        sp.set_xlabel("z3 time (s)")
        sp.set_ylabel("cvc5 time (s)")

        # z3_v = PartialCDF(np_data[:,2])
        # cvc5_v = PartialCDF(np_data[:,1])
        # cvc5_p = PartialCDF(np_data[:,0])
        
        # sp.plot(z3_v.xs, z3_v.ys, label="z3-verify")
        # sp.plot(cvc5_v.xs, cvc5_v.ys, label="cvc5-verify")
        # sp.plot(cvc5_p.xs, cvc5_p.ys, label="cvc5-proof")

        # m = z3_v.valid_max
        # sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        # sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", va="top", fontsize=8)

        # m = cvc5_v.valid_median
        # sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        # sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        # m = cvc5_v.valid_max
        # sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        # sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        # m = cvc5_p.valid_max
        # sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        # sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        # sp.set_xlim(0, 30)
        # sp.set_ylim(0, 100)

        # sp.set_yticks(np.arange(0, 101, 10))

        # sp.set_ylabel("Cumulative Percentage (\%)")
        # sp.set_xlabel("Run Time (s)")
        # sp.legend()
        
        plt.title(f"{PROJECT_LABELS[gid]} cvc5 vs. Z3 Verification Time")

        # sp.set_aspect('equal', adjustable='box')
        sp.set_xlim(0, 1)
        sp.set_ylim(0, 10)
        sp.legend()

        plt.grid()
        plt.tight_layout()
        plt.savefig(f"{gid}.pdf")
