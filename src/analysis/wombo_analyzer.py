import os
import random
from analysis.core_analyzer import CoreAnalyzer
from base.defs import MARIPOSA, QUERY_WIZARD
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT, get_qid
from base.query_analyzer import QueryAnalyzer, Stability as STB
from base.exper_analyzer import ExperAnalyzer
from query.combo_builder import ComboBuilder
from utils.analysis_utils import *
from utils.system_utils import subprocess_run
import matplotlib.pyplot as plt

class WomboAnalyzer(CoreAnalyzer):
    def __init__(self, group: ProjectGroup):
        super().__init__(group)
        self.ana = FACT.get_analyzer("60nq")

        self.pins = group.get_project(PT.from_str("pins.z3"), build=True)
        self.temp = group.get_project(PT.from_str("temp.z3"), build=True)

        self.cmds = []
        ncc = 0
        for qid in self.qids:
            # self.build_pin(qid)
            # self.build_temp(qid)
            cb = self.get_cb(qid)
            # if cb.no_progress():
            #     continue
            if not cb.has_converged():
                print(cb.counts)
                cmd = f"{QUERY_WIZARD} wombo-combo -i {cb.input_query} -o {cb.output_dir}"
            #     # self.cmds.append(cmd)
                print(cmd)
                cmd = "src/query_wizard.py build-core -i " + cb.output_dir + "/0.smt2" + " -o " + cb.output_dir + "/1.smt2" + " --complete" + " --restarts 5" + " --ids-available" + " --solver z3_4_8_5" + " --timeout 120"
                print(cmd)
                print("")
                # self.cmds.append(cmd)
        self.print_cmds()

    def print_cmds(self):
        random.shuffle(self.cmds)
        for cmd in self.cmds:
            print(cmd)

    def get_cb(self, qid):
        log_dir = os.path.join(self.base.get_log_dir(KnownExt.WOCO), qid)
        pins_path = self.pins.get_path(qid)
        cb = ComboBuilder(pins_path, log_dir)
        return cb

    def build_pin(self, qid):
        cqs = self.qids[qid]
        in_path = cqs.patch_path
        ot_path = self.pins.get_path(qid)
        if os.path.exists(ot_path):
            return
        self.cmds.append(f"{MARIPOSA} -a pre-inst-z3 -i {in_path} -o {ot_path}")

    def build_temp(self, qid):
        cb = self.get_cb(qid)
        ot_path = self.temp.get_path(qid)
        if os.path.exists(ot_path):
            return
        self.cmds.append(f"cp {cb.cur_file} {ot_path}")
