import os, numpy as np
from base.defs import NINJA_REPORTS_DIR
from base.project import Project, ProjectGroup, KnownExt as KE
from base.solver import SolverType as ST
from proj_wizard import NinjaStats
from utils.analysis_utils import PartialCDF, print_sets_diff
from utils.system_utils import log_check
from utils.plot_utils import *

class PrefAnalyzer:
    def __init__(self, group: ProjectGroup):
        gid = group.gid
        z3_pt = Project.DEFAULT_PTYPE
        z3_p = group.get_project(z3_pt)
        cvc5_p = group.get_project(z3_pt.switch_solver())

        pm = NinjaStats(cvc5_p.get_build_meta_path(KE.LFSC))
        vm = NinjaStats(cvc5_p.get_build_meta_path(KE.VERI))
        zvm = NinjaStats(z3_p.get_build_meta_path(KE.VERI))

        log_check(pm.expected == vm.expected,
                f"proof and verify targets mismatch for {gid}")
        log_check(pm.expected == zvm.expected,
                f"proof and verify targets mismatch for {gid}")

        data = []
        for k in pm.expected:
            data += [(pm.built[k], vm.built[k], zvm.built[k])]

        print_sets_diff(set(pm.built), set(vm.built), "proof", "verify")

        np_data = np.array(data)

        fig, ax = plt.subplots(1, 1, squeeze=False)
        sp = ax[0, 0]

        z3_v = PartialCDF(np_data[:,2])
        cvc5_v = PartialCDF(np_data[:,1])
        cvc5_p = PartialCDF(np_data[:,0])
        
        sp.plot(z3_v.xs, z3_v.ys, label="z3-verify")
        sp.plot(cvc5_v.xs, cvc5_v.ys, label="cvc5-verify")
        sp.plot(cvc5_p.xs, cvc5_p.ys, label="cvc5-proof")

        m = z3_v.valid_max
        sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", va="top", fontsize=8)

        m = cvc5_v.valid_median
        sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        m = cvc5_v.valid_max
        sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        m = cvc5_p.valid_max
        sp.plot(m[0], m[1], color="black", marker="o", markersize=3)
        sp.text(m[0]+0.3, m[1], f"{m[0]:.2f}s", fontsize=8)

        sp.set_xlim(0, 30)
        sp.set_ylim(0, 100)

        sp.set_yticks(np.arange(0, 101, 10))

        sp.set_ylabel("Cumulative Percentage (\%)")
        sp.set_xlabel("Run Time (s)")
        sp.legend()
        
        plt.title(f"{PROJECT_LABELS[gid]} Verification and Proof Time CDF")
        plt.grid()
        plt.tight_layout()
        plt.savefig(f"{gid}.pdf")
