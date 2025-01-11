import os
import shutil
from base.exper import Experiment
from base.exper_analyzer import ExperAnalyzer
from base.query_analyzer import FailureType, QueryAnalyzer, Stability
from base.solver import RCode
from utils.system_utils import list_smt2_files, log_error, log_info, log_warn


class SingletonAnalyzer(ExperAnalyzer):
    def __init__(self, exp: Experiment, ana: QueryAnalyzer):
        super().__init__(exp, ana)

        self.edit_results = self.get_plain_statuses()
        self.passed_edits = []
        self.errored_edits = []
        self.unknown_edits = []
        self.timeout_edits = []

        for eid, (rc, _) in self.edit_results.items():
            if rc == RCode.UNSAT:
                self.passed_edits.append(eid)
            elif rc == RCode.ERROR:
                self.errored_edits.append(eid)
            elif rc == RCode.UNKNOWN:
                self.unknown_edits.append(eid)
            elif rc == RCode.TIMEOUT:
                self.timeout_edits.append(eid)
            else:
                print(rc)
                assert False

        self.passed_edits = sorted(self.passed_edits, key=lambda x: self.edit_results[x][1])

        # log_info(f"{self.exp.proj.gid} has {len(self.qids)} queries, {len(passed)} passed")

        # if len(errored) > 0:
        #     log_error(f"{len(errored)} errors!")
        #     for qid in errored:
        #         query_path = self[qid].query_path
        #         print(f"{query_path}")

    def get_query_result(self, eid):
        return self.edit_results[eid]
    
    def create_filtered_project(self):
        filtered_dir = self.exp.proj.sub_root.replace("/base", ".filtered/base")
        os.makedirs(filtered_dir, exist_ok=True)
        
        use_caution = len(list_smt2_files(filtered_dir)) != 0

        if use_caution:
            log_warn("filtered dir is not empty, proceeding with caution")

        budget, selected = 0, 0
        max_selected_et = 0

        for eid in self.passed_edits:
            if budget >= 360:
                break
            (_, et) = self.get_query_result(eid)
            budget += et/1000
            selected += 1
            dest = f"{filtered_dir}/{eid}.smt2"
            max_selected_et = max(max_selected_et, et)

            if os.path.exists(dest) or use_caution:
                continue

            shutil.copy(self[eid].query_path, dest)

        log_info(f"selected {selected} queries to {filtered_dir}")
        eta = budget * 180 / 7 / 5 / 60 / 60
        log_info(f"plain budget: {round(budget, 2)}s, eta: {round(eta, 2)} hours, max selected et: {max_selected_et/1000}(s)")
