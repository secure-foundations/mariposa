from enum import Enum
import hashlib
import os
from base.solver import RCode, output_as_rcode
from utils.system_utils import log_info, subprocess_run


# in theory we can be using the factory...
def run_z3(query_path):
    r, e, t = subprocess_run(["./bin/z3-4.13.0", "-T:10", query_path])
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
    def __init__(self, path, edit):
        self.path = path
        self.edit = edit

        self.rcode = None
        self.time = None
        self.error = None

    def as_report(self):
        edit = ",\n".join([f"    '{qid}': {e}" for qid, e in self.edit.items()])
        edit = f"edit = {{\n{edit}\n}}"
        lines = [
            "# " + "-" * 80,
            f"# {self.path}",
            f"# rcode: {self.rcode}",
            f"# time: {self.time}\n\n",
            edit,
            "dbg.test_edit(edit)",
            "# " + "-" * 80 + "\n",
        ]
        return "\n".join(lines)

    def query_exists(self):
        return os.path.exists(self.path)

    def has_data(self):
        return self.rcode != None

    def get_id(self):
        m = hashlib.md5()
        qids = [qid for qid in sorted(self.edit)]
        m.update(str(qids).encode())
        return m.hexdigest()[0:8]

    def run_query(self):
        if self.has_data():
            return
        _, self.rcode, self.error, self.time = run_z3(self.path)

    def get_singleton_edit(self):
        assert len(self.edit) == 1
        qid = list(self.edit.keys())[0]
        return (qid, self.edit[qid])

    @staticmethod
    def from_dict(d):
        edit = d["edit"]
        edit = {qid: EditAction(e) for qid, e in edit.items()}
        ei = EditInfo(d["path"], edit)
        ei.rcode = RCode(d["rcode"]) if d["rcode"] is not None else None
        ei.time = d["time"]
        ei.error = d["error"]
        return ei

    def to_dict(self):
        edit = {qid: self.edit[qid].value for qid in self.edit}
        rcode = self.rcode.value if self.rcode is not None else None
        return {
            "path": self.path,
            "edit": edit,
            "rcode": rcode,
            "time": self.time,
            "error": self.error,
        }
