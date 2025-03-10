from enum import Enum
import hashlib
import os
from base.solver import RCode, output_as_rcode
from utils.system_utils import log_info, subprocess_run


# in theory we can be using the factory...
def run_z3(query_path, timeout=10):
    r, e, t = subprocess_run(["./bin/z3-4.13.0", f"-T:{timeout}", query_path])
    r = output_as_rcode(r)
    log_info(f"[run] {query_path} {r} {e} {round(t / 1000, 2)}")
    return (query_path, r, e, round(t / 1000, 2))


class EditAction(Enum):
    NONE = "-"
    ERASE = "erase"
    SKOLEMIZE = "skolemize"
    DSPLIT = "dsplit"
    INST_REPLACE = "inst_replace"
    INST_KEEP = "inst_keep"
    ERROR = "ERROR"


class EditInfo:
    def __init__(self, dir, actions):
        self.edit_dir = dir
        self._actions = actions
        self.__hash_id = EditInfo.hash_actions(actions)

        self.rcode = None
        self.time = None
        self.error = None

    @property
    def query_path(self):
        return os.path.join(self.edit_dir, self.__hash_id + ".smt2")

    @staticmethod
    def hash_actions(actions):
        m = hashlib.md5()
        assert isinstance(actions, dict)
        actions = [(qid, actions[qid]) for qid in sorted(actions)]
        m.update(str(actions).encode())
        return m.hexdigest()[0:8]

    def as_report(self):
        edit = ",\n".join([f"    '{qid}': {e}" for qid, e in self._actions.items()])
        edit = f"edit = {{\n{edit}\n}}"
        lines = [
            "# " + "-" * 80,
            f"# {self.query_path}",
            f"# rcode: {self.rcode}",
            f"# time: {self.time}\n\n",
            edit,
            "dbg.test_edit(edit)",
            "# " + "-" * 80 + "\n",
        ]
        return "\n".join(lines)

    def query_exists(self):
        return os.path.exists(self.query_path)

    def has_data(self):
        return self.rcode != None

    def get_id(self):
        return self.__hash_id

    def run_query(self):
        if self.has_data():
            return
        _, self.rcode, error, self.time = run_z3(self.query_path)
        assert error == ""

    def is_singleton(self):
        return len(self._actions) == 1

    def get_singleton_edit(self):
        assert len(self._actions) == 1
        qid = list(self._actions.keys())[0]
        return (qid, self._actions[qid])

    def is_doubleton(self):
        return len(self._actions) == 2
    
    def get_doubleton_edit(self):
        assert self.is_doubleton()
        qids = list(self._actions.keys())
        return (qids[0], self._actions[qids[0]]), (qids[1], self._actions[qids[1]])

    @staticmethod
    def from_dict(d):
        actions = dict()
        for qid, e in d["actions"].items():
            actions[qid] = EditAction(e)
        ei = EditInfo(d["edit_dir"], actions)
        rc = d["rcode"]
        if rc is not None:
            ei.rcode = RCode(rc)
        ei.time = d["time"]
        ei.error = d["error"]
        return ei

    def to_dict(self):
        edit = dict()
        for qid, e in self._actions.items():
            edit[qid] = e.value
        if self.rcode is not None:
            rcode = self.rcode.value
        else:
            rcode = None
        return {
            "edit_dir": self.edit_dir,
            "actions": edit,
            "rcode": rcode,
            "time": self.time,
            "error": self.error,
        }

    def items(self):
        return self._actions.items()

    @property
    def actions(self):
        return self._actions
