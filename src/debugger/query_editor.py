from typing import List, Set
from debugger.edit_info import run_z3
from debugger.proof_analyzer import QuantInstInfo
from debugger.query_loader import QueryLoader
from debugger.z3_utils import *
from utils.query_utils import add_qids_to_query
from utils.system_utils import log_error, log_info, log_warn
from base.solver import EXPECTED_CODES
import z3


class BaseQueryEditor(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)
        self.__reset_state()

    def __reset_state(self):
        self._new_commands = []
        self._modified_commands = dict()

        self._skolem_ids = set()
        self._erase_ids = set()
        self._banish_ids = set()

    def erase_qid(self, qid):
        if not self.check_qid(qid):
            return
        self._erase_ids.add(qid)

    def skolemize_qid(self, qid):
        # TODO: handle dual quantifiers if needed
        qid = qid[7:] if qid.startswith("skolem_") else qid
        if not self.check_qid(qid):
            return
        if hack_contains_qid(self.query_goal, qid):
            log_error(f"[skolem] is in the goal!")
            return
        if qid in self.existing_sk_decls:
            log_warn(f"[skolem] {qid} has existing skolem function(s)")
            return
        self._skolem_ids.add(qid)

    def instantiate_qid(self, qid, insts: List[str], erase=True):
        if not self.check_qid(qid):
            return
        if erase:
            self._erase_ids.add(qid)

        comment = f"[inst] {qid} {len(insts)} instances"
        self.__add_new_commands(comment, insts)

    def check_qid(self, qid):
        if qid not in self:
            log_warn(f"[edit] target {qid} not found")
            return False
        return True

    def save(self, out_file_path):
        self.__skolemize_assertions()
        self.__erase_quantifiers()
        self.__banish_assertions()

        out_file = open(out_file_path, "w+")
        for i, line in enumerate(self.in_cmds):
            if i in self._modified_commands:
                out_file.write(self._modified_commands[i])
            else:
                out_file.write(line)
        for line in self._new_commands:
            out_file.write(line + "\n")

        if len(self.in_cmds) in self._modified_commands:
            log_info(f"[edit] goal was modified!")
            out_file.write(self._modified_commands[len(self.in_cmds)])
        else:
            out_file.write(self.query_goal)
        out_file.write("(check-sat)\n")
        out_file.close()

        self.__reset_state()
        log_info(f"[edit] written to {out_file_path}")
        add_qids_to_query(out_file_path)

    def __add_new_commands(self, comment, commands):
        log_info("[edit] " + comment)
        comment = f'(set-info :comment "{comment}")'
        self._new_commands.append(comment)
        self._new_commands += commands

    def __skolemize_assertions(self):
        targets = dict()

        for qid in self._skolem_ids:
            quant = self.__z3_quants[qid]
            exp = quant.origin

            if exp.get_id() in targets:
                log_warn(f"[skolem] duplicated match on assertion, skipping: {qid}")
                continue

            targets[exp.get_id()] = (qid, exp)
            # TODO: this is not very robust
            self._banish_ids.add(qid)

        for qid, exp in targets.values():
            self.__skolemize_assertion(qid, exp)

    def __skolemize_assertion(self, qid, exp):
        g = z3.Goal()
        g.add(exp)
        res = z3.Tactic("snf")(g)

        assert len(res) == 1
        asserts, decls = [], []

        for r in res[0]:
            for name, decl in find_sk_decls(r, recursive=True):
                if name in self.existing_sk_decls:
                    continue
                decls.append(decl)
            asserts.append("(assert " + collapse_sexpr(r.sexpr()) + ")")

        comment = f"[skolem] {qid} creates {len(decls)} skolem funs, {len(asserts)} asserts"
        self.__add_new_commands(comment, decls + asserts)

    def __erase_quantifiers(self):
        removed = set()
        for i, line in enumerate(self.in_cmds + [self.query_goal]):
            for qid in self._erase_ids:
                if qid in removed:
                    continue
                if not hack_contains_qid(line, qid):
                    continue
                line = hack_quantifier_removal(line, qid)
                removed.add(qid)
                comment = f"[erase] {qid}"
                self.__add_new_commands(comment, [])
                self._modified_commands[i] = line

        for qid in self._erase_ids - removed:
            log_warn(f"[edit] [erase] failed on {qid}")

    def __banish_assertions(self):
        for i, line in enumerate(self.in_cmds + [self.query_goal]):
            removed = set()
            for qid in self._banish_ids:
                if not hack_contains_qid(line, qid):
                    continue
                self._modified_commands[i] = ""
                removed.add(qid)
                comment = f"[banish] {qid}"
                print(line, end="")
                self.__add_new_commands(comment, [])

        for qid in self._banish_ids - removed:
            log_warn(f"failed to banish {qid}")

    def save_and_test(self, out_file_path):
        self.save(out_file_path)
        _, r, e, _ = run_z3(out_file_path, 2)
        assert e == ""
        return r
