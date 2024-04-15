import os
from base.defs import MARIPOSA, QUERY_WIZARD
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT, get_qid
from base.query_analyzer import QueryAnalyzer, Stability as STB
from base.exper_analyzer import ExperAnalyzer
from query.combo_builder import ComboBuilder
from utils.analysis_utils import *
from utils.system_utils import subprocess_run

class WomboAnalyzer:
    def __init__(self, in_group: ProjectGroup):
        self.ana = FACT.get_analyzer("60nq")

        self.base_p = in_group.get_project(PT.from_str("base.z3"))
        self.pins_p = in_group.get_project(PT.from_str("pins.z3"), build=True)
        # self.temp_p = in_group.get_project(PT.from_str("temp.z3"))

        # for qid in base_p.qids:
        #     log_dir = os.path.join(base_p.get_log_dir(KnownExt.WOCO), qid)
        #     in_path = base_p.get_path(qid)
        #     cb = ComboBuilder(in_path, log_dir)
        #     if not cb.has_converged() and cb.curr == 0:
        #         ncc += 1
        #         # print(log_dir)
        #         # print(cb.counts)
        #     ot_path = temp_p.get_path(qid)
        #     print("cp {} {}".format(cb.cur_file, ot_path))
            # print("src/query_wizard.py wombo-combo -i", base_p.get_path(qid), "-o", log_dir)
        # print(ncc)
        self.build_pins()

    def build_pins(self):
        for qid in self.base_p.qids:
            in_path = self.base_p.get_path(qid)
            ot_path = self.pins_p.get_path(qid)
            print(f"{MARIPOSA} -a pre-inst-z3 -i {in_path} -o {ot_path}")

        # base = FACT.load_default_analysis(base_p)
        # # base.print_status()
        # cb = base.get_overall()

        # p0 = FACT.get_group("bench_unstable_0")
        # a0 = FACT.load_default_analysis(p0.get_project(PT.from_str("core.z3")))
        # c0 = a0.get_overall()
        # for qid in c0[STB.UNSOLVABLE].items:
        #     # print(qid)
        #     if qid in base:
        #         # base[qid].print_status(3)
        #         print("cp {} {}".format(base.get_path(qid), a0.get_path(qid)))
        #     else:
        #         print("no base")
        #     # a0[qid].print_status(3)
        #     # print("")

        # for qid in cb[STB.STABLE].items & c0[STB.UNSTABLE].items:
        #     # base[qid].print_status(3)
        #     # print(get_quantifier_count(base.get_path(qid)))
        #     # print(get_quantifier_count(a0.get_path(qid)))
        #     print("cp {} {}".format(base.get_path(qid), a0.get_path(qid)))

 