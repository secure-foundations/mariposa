import json
import os
from typing import Dict, List
from tqdm import tqdm
from tabulate import tabulate

from debugger.edit_info import EditAction, EditInfo
from debugger.mutant_info import MutantInfo
from debugger.pool_utils import run_with_pool
from debugger.proof_analyzer import ProofAnalyzer
from debugger.infomed_editor import InformedEditor 
from utils.system_utils import confirm_input, create_dir, list_smt2_files, log_info, log_warn, remove_dir, subprocess_run


def _run_edit(ei: EditInfo):
    ei.run_query()
    return ei

class EditManager(InformedEditor):
    def __init__(
        self,
        name_hash: str,
        proof: ProofAnalyzer,
        trace: MutantInfo,
        clear_edits=False,
    ):
        query_path = f"dbg/{name_hash}/orig.smt2"
        super().__init__(query_path, proof, trace)

        self.__edit_infos: Dict[int, EditInfo] = dict()
        self.sub_root = f"dbg/{name_hash}"
        self.edits_meta = f"{self.sub_root}/edits.json"
        self.edit_dir = f"{self.sub_root}/edits/"

        self.feasible_actions = self.get_all_feasible_actions()
        self.singleton_project = "singleton_" + name_hash

        self.__init_dirs(clear_edits)
        self.__init_edits(clear_edits)

    def save_edits_meta(self):
        infos = [ei.to_dict() for ei in self.__edit_infos.values()]

        with open(self.edits_meta, "w+") as f:
            json.dump(infos, f)

    def __init_dirs(self, reset):
        create_dir(self.edit_dir)

        if reset:
            log_info(f"[init] removing singleton project {self.singleton_project}")
            remove_dir("data/projs/" + self.singleton_project)
            remove_dir("data/projs/" + self.singleton_project + ".filtered")
            remove_dir("data/dbs/" + self.singleton_project)
            remove_dir("data/dbs/" + self.singleton_project + ".filtered")

    def __init_edits(self, clear_edits):
        self.__edit_infos = dict()

        if clear_edits:
            return self.clear_edits()

        if not os.path.exists(self.edits_meta):
            return

        infos = json.load(open(self.edits_meta, "r"))

        for ei in infos:
            ei = EditInfo.from_dict(ei)
            self.__edit_infos[ei.get_id()] = ei

    def clear_edits(self):
        if os.path.exists(self.edit_dir):
            count = len(os.listdir(self.edit_dir))
            if count > 10:
                confirm_input(f"clear {count} edits?")
            os.system(f"rm {self.edit_dir}/*")
        self.__edit_infos = dict()
        log_info("[edit] cleared")

    def create_singleton_project(self):
        project_dir = f"data/projs/{self.singleton_project}/base.z3"
        filtered_dir = f"data/projs/{self.singleton_project}.filtered/base.z3"

        create_dir(project_dir)
        create_dir(filtered_dir)

        if list_smt2_files(project_dir) == []:
            for qid, action in tqdm(self.feasible_actions.items()):
                self.register_edit_info({qid: action}, project_dir)
                if action == EditAction.INST_REPLACE:
                    # this is also feasible
                    self.register_edit_info({qid: EditAction.INST_KEEP}, project_dir)
            self.save_edits_meta()
        else:
            log_warn(f"[proj] {self.singleton_project} already exists")

        query_count = len(list_smt2_files(project_dir))
        log_info(f"[edit] [proj] {self.singleton_project} has {query_count} queries")

        # if list_smt2_files(filtered_dir) == []:
        #     os.system(f"./src/analysis_wizard.py filter_edits -e verify -s z3_4_13_0 -i {project_dir}")
        #     os.system(f"./src/exper_wizard.py manager -e verus_quick --total-parts 30 -s z3_4_13_0 -i {filtered_dir} --clear")
        # else:
        #     log_warn(f"[proj] {self.singleton_edit_project} already filtered")

    def analyze_singleton_project(self):
        name = self.singleton_project
        filtered_dir = f"data/projs/{name}.filtered/base.z3"
        edit_ids = []

        if not os.path.exists(filtered_dir):
            log_warn(f"[proj] {name} has no filtered queries")
            return

        stdout, stderr, _ = subprocess_run(
            [
                "./src/analysis_wizard.py",
                "stable",
                "-e",
                "verus_quick",
                "-s",
                "z3_4_13_0",
                "-i",
                filtered_dir,
            ],
            debug=True,
        )

        # TODO: this is a hacky... I should have used the same exp config...
        if stderr:
            log_warn("skip due to encountered: " + stderr)
            return    

        for line in stdout.split("\n"):
            if line.startswith("edit_id:"):
                edit_id = line.split(": ")[1].strip()
                edit_ids.append(edit_id)

        feasible = []
        for edit_id in edit_ids:
            ei = self.test_edit_with_id(edit_id)
            qname, action = ei.get_singleton_edit()
            feasible.append((ei, qname, action))

        feasible = sorted(feasible, key=lambda x: x[1])

        for ei, qid, action in feasible:
            print(f"{qid} {action.value}")
            print(f"{ei.query_path} {ei.time}s")
            print()

        self.save_edits_meta()
        return

    def test_edit(self, edit):
        ei = self.register_edit_info(edit)
        if ei.has_data():
            return ei
        ei.run_query()
        self.__edit_infos[ei.get_id()] = ei
        return ei

    def test_edit_with_id(self, edit_id) -> EditInfo:
        assert edit_id in self.__edit_infos
        ei = self.__edit_infos[edit_id]
        if not ei.query_exists():
            self._save_edit(ei)
        if not ei.has_data():
            ei.run_query()
        return ei

    def register_edit_info(self, actions, output_dir=None):
        if isinstance(actions, set):
            actions = {qid: self.get_action(qid) for qid in actions}
        else:
            assert isinstance(actions, dict)

        if not output_dir:
            output_dir = self.edit_dir

        create_dir(output_dir)

        ei = EditInfo(output_dir, actions)
        eid = ei.get_id()

        if not ei.query_exists():
            self.edit_by_info(ei)

        if eid in self.__edit_infos:
            return self.__edit_infos[eid]

        self.__edit_infos[eid] = ei

        return ei

    def look_up_edit(self, edit):
        res = []

        for ei in self.__edit_infos:
            if set(ei.edit.keys()) & edit.keys() != set():
                res.append(ei)

        return res

    def _try_edits(self, targets, run_query):
        args = []

        for edit in tqdm(targets):
            ei = self.register_edit_info(edit)
            if ei.has_data():
                continue
            args.append(ei)

        if not run_query:
            log_info(f"[edit] skipped running, queries saved in {self.edit_dir}")
            return

        run_res = run_with_pool(_run_edit, args)

        for ei in run_res:
            assert ei.has_data()
            self.__edit_infos[ei.get_id()] = ei
