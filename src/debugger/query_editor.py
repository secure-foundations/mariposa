from typing import Set
from debugger.query_loader import QueryLoader
from debugger.z3_utils import *
from utils.query_utils import add_qids_to_query
from utils.system_utils import log_info, log_warn
import z3


class BaseQueryEditor(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)

        self._fun_decls = []
        self._fun_asserts = []
        self._new_commands = []

        self._erase_ids = set()
        self._modified_lines = dict()
        self._banish_ids = set()

    def _basic_check(self, target_ids: Set[str]):
        filtered = set()
        for qid in target_ids:
            if qid not in self.z3_quants:
                log_warn(f"target {qid} not found")
            else:
                filtered.add(qid)
        return filtered

    def erase_qids(self, target_ids: Set[str]):
        target_ids = self._basic_check(target_ids)
        for i, line in enumerate(self.in_cmds):
            removed = set()
            for qid in target_ids:
                if hack_contains_qid(line, qid):
                    line = hack_quantifier_removal(line, qid)
                    removed.add(qid)
                    log_info(f"[erase] erasing {qid}")
                    self._new_commands = [
                        f'(set-info :comment "[erase] {qid}")'
                    ] + self._new_commands
                    self._modified_lines[i] = line
            target_ids -= removed

        if len(target_ids) > 0:
            log_warn(f"failed to erase the following qids:")
            print("\t".join(target_ids))

    def banish_qids(self, target_ids: Set[str]):
        target_ids = self._basic_check(target_ids)
        for i, line in enumerate(self.in_cmds + [self.query_goal]):
            removed = set()
            for qid in target_ids:
                if hack_contains_qid(line, qid):
                    self._modified_lines[i] = ""
                    removed.add(qid)
                    log_info(f"[banish] assertion:")
                    print(line, end="")
                    self._new_commands = [
                        f'(set-info :comment "[banish] {qid}")'
                    ] + self._new_commands
            target_ids -= removed

        if len(target_ids) > 0:
            log_warn(f"failed to banish the following qids:")
            print("\t".join(target_ids))

    def skolemize_qids(self, target_ids: Set[str]):
        # reduce to qids
        target_ids = {q[7:] if q.startswith("skolem_") else q for q in target_ids}

        targets = dict()

        for qid in target_ids:
            quant = self.z3_quants[qid]
            exp = quant.origin

            if exp.get_id() in targets:
                log_warn(f"[skolem] duplicated match on assertion, skipping: {qid}")
                continue

            # dual = self.quants[qid].find_dual()
            dual = False
            targets[exp.get_id()] = (qid, dual, exp)
            # TODO: this is not very robust
            self._banish_ids.add(qid)

        for qid, dual, exp in targets.values():
            asserts, decls = self.__skolemize_assertion(exp, dual, target_ids)

            log_info(f"[skolem] {qid}")
            log_info(
                f"[skolem] {len(decls)} skolem funs, {len(asserts)} asserts added"
            )

            asserts = [
                f'(set-info :comment "[skolem] {len(asserts)} asserts for {qid}")'
            ] + asserts
            self._fun_decls += decls
            self._new_commands += asserts

    def __skolemize_assertion(self, exp, dual, remove_ids):
        g = z3.Goal()
        g.add(exp)
        res = z3.Tactic("snf")(g)
        assert len(res) == 1
        asserts, decls, skf = [], [], Z3SkolemFinder()

        for r in res[0]:
            skf.process_expr(r)
            # print(collapse_sexpr(r.sexpr()))
            asserts.append("(assert " + collapse_sexpr(r.sexpr()) + ")")

        for name, decl in skf.sk_decls.items():
            # if name in self.cur_skolem_funs:
            #     continue
            decls.append(decl)
        return asserts, decls

    def save(self, out_file_path):
        self.erase_qids(self._erase_ids)
        self.banish_qids(self._banish_ids)
        out_file = open(out_file_path, "w+")
        for i, line in enumerate(self.in_cmds[:-1]):
            if i in self._modified_lines:
                out_file.write(self._modified_lines[i])
            else:
                out_file.write(line)
        assert self.in_cmds[-1] == "(check-sat)\n"
        for line in self._fun_decls:
            out_file.write(line + "\n")
        for line in self._fun_asserts:
            out_file.write(line + "\n")
        for line in self._new_commands:
            out_file.write(line + "\n")
        if len(self.in_cmds) in self._modified_lines:
            log_info(f"[edit] goal is modified!")
            out_file.write(self._modified_lines[len(self.in_cmds)])
        else:
            out_file.write(self.query_goal)
        out_file.write("(check-sat)\n")
        out_file.close()

        self._fun_decls = []
        self._fun_asserts = []
        self._new_commands = []
        self._modified_lines = dict()
        self._erase_ids = set()
        self._banish_ids = set()
        log_info(f"[edit] written to {out_file_path}")
        add_qids_to_query(out_file_path)

