import json
import os
from typing import Dict, List
from tqdm import tqdm

from debugger.edit_info import EditAction, EditInfo
from debugger.mutant_info import MutantInfo
from debugger.pool_utils import run_with_pool
from debugger.proof_analyzer import ProofAnalyzer
from debugger.infomed_editor import InformedEditor 
from utils.system_utils import confirm_input, create_dir, log_info, remove_dir


def _run_edit(ei: EditInfo):
    ei.run_query()
    return ei

class EditManager:
    def __init__(
        self,
        name_hash: str,
        proof: ProofAnalyzer,
        trace: MutantInfo,
        clear_edits=False,
    ):
        query_path = f"dbg/{name_hash}/orig.smt2"
        self.editor = InformedEditor(query_path, proof, trace)

        self.__edit_infos: Dict[int, EditInfo] = dict()
        self.sub_root = f"dbg/{name_hash}"
        self.edits_meta = f"{self.sub_root}/edits.json"
        self.edit_dir = f"{self.sub_root}/edits/"

        self.feasible_actions = self.editor.get_all_feasible_actions()
        self.singleton_edit_project = "singleton_" + name_hash

        self.__init_dirs(clear_edits)
        self.__init_edits(clear_edits)

    def __save_edits_meta(self):
        infos = [ei.to_dict() for ei in self.__edit_infos.values()]

        with open(self.edits_meta, "w+") as f:
            json.dump(infos, f)

    def __init_dirs(self, reset):
        create_dir(self.edit_dir)

        if reset:
            log_info(f"[init] removing singleton project {self.singleton_edit_project}")
            remove_dir("data/projs/" + self.singleton_edit_project)
            remove_dir("data/projs/" + self.singleton_edit_project + ".filtered")
            remove_dir("data/dbs/" + self.singleton_edit_project)
            remove_dir("data/dbs/" + self.singleton_edit_project + ".filtered")

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

    def test_edit(self, edit):
        ei = self.register_edit_info(edit)
        if ei.has_data():
            # log_warn("[edit] specified edit already exists")
            return ei
        if not ei.query_exists():
            self._save_edit(ei)
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

    def get_edit_path(self, edit):
        return f"{self.edit_dir}{edit.get_id()}.smt2"

    def register_edit_info(self, edit):
        if isinstance(edit, set):
            edit = {qid: self.editor.get_action(qid) for qid in edit}
        else:
            assert isinstance(edit, dict)
        ei = EditInfo("", edit)
        path = self.get_edit_path(ei)
        ei.query_path = path
        eid = ei.get_id()

        if not ei.query_exists():
            self._save_edit(ei)

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

    # def try_random_edits(self, size=1):
    #     NUM_TRIES = 30
    #     edits = []

    #     for _ in range(NUM_TRIES):
    #         edit = set(random.sample(self.differ.actions.keys(), size))
    #         edits.append({qid: self.differ.actions[qid] for qid in edit})

    #     self._try_edits(edits, run_query=True)

    def _save_edit(self, ei: EditInfo):
        assert isinstance(ei, EditInfo)
        self.editor.edit_specified(ei.edit)
        self.editor.save(ei.query_path)

    def create_singleton_edit_project(self):
        for qid, action in tqdm(self.feasible_actions.items()):
            self.register_edit_info({qid: action})
            if action == EditAction.INST_REPLACE:
                # this is also feasible
                self.register_edit_info({qid: EditAction.INST_KEEP})
        log_info(f"[edit] {len(self.__edit_infos)} edits registered")    
        self.__save_edits_meta()

        name = self.singleton_edit_project
        # assert os.path.exists(self.edit_dir)

        if os.path.exists(f"data/projs/{name}"):
            log_info(f"[proj] {name} already exists")
        else:
            os.system(
                f"./src/proj_wizard.py create -i {self.edit_dir} --new-project-name {name}"
            )
            os.system(
                f"./src/exper_wizard.py manager -e verify --total-parts 30 -s z3_4_13_0 -i data/projs/{name}/base.z3 --clear"
            )

    #     filtered_dir = f"data/projs/{name}.filtered/base.z3"

    #     if os.path.exists(filtered_dir):
    #         log_info(f"[proj] {name}.filtered already exists")
    #     else:
    #         os.system(
    #             f"./src/analysis_wizard.py filter_edits -e verify -s z3_4_13_0 -i data/projs/{name}/base.z3"
    #         )
    #         if len(os.listdir(filtered_dir)) == 0:
    #             return log_warn(f"[proj] {name} has no filtered queries")
    #         os.system(
    #             f"./src/exper_wizard.py manager -e default --total-parts 30 -s z3_4_13_0 -i {filtered_dir}"
    #         )

    # def analyze_singleton_project(self):
    #     name = self.singleton_edit_project
    #     filtered_dir = f"data/projs/{name}.filtered/base.z3"
    #     edit_ids = []

    #     if not os.path.exists(filtered_dir):
    #         log_warn(f"[proj] {name} has no filtered queries")
    #         return edit_ids

    #     for config in ["default", "verus_quick"]:
    #         stdout, stderr, _ = subprocess_run(
    #             [
    #                 "./src/analysis_wizard.py",
    #                 "stable",
    #                 "-e",
    #                 config,
    #                 "-s",
    #                 "z3_4_13_0",
    #                 "-i",
    #                 filtered_dir,
    #             ],
    #             debug=True,
    #         )

    #         # TODO: this is a hacky... I should have used the same exp config...
    #         if stderr:
    #             log_warn("skip due to encountered: " + stderr)
    #             continue

    #         for line in stdout.split("\n"):
    #             if line.startswith("edit_id:"):
    #                 edit_id = line.split(": ")[1].strip()
    #                 edit_ids.append(edit_id)

    #         return edit_ids
