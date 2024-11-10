#!/usr/bin/env python3

from typing import Dict, Set
from z3 import *
from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.trace_analyzer import EditAction
from debugger.z3_utils import collapse_sexpr, format_expr_flat, hack_contains_qid, hack_quantifier_removal
from proof_builder import ProofInfo, ProofBuilder, QunatInstInfo, InstError
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from utils.query_utils import add_qids_to_query


class BasicQueryWriter(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)
        self.in_file_path = in_file_path
        self.__in_commands = open(self.in_file_path, "r").readlines()

        assert len(self.__in_commands) > 0
        assert self.__in_commands[-1] == "(check-sat)\n"

        self._fun_decls = []
        self._fun_asserts = []
        self._new_commands = []

        self._erase_ids = set()
        self._modified_lines = dict()
        self._banish_ids = set()

    def _basic_check(self, target_ids: Set[str]):
        filtered = set()
        for qid in target_ids:
            if qid not in self.quants:
                log_warn(f"target {qid} not found")
            else:
                filtered.add(qid)
        return filtered

    def erase_qids(self, target_ids: Set[str]):
        target_ids = self._basic_check(target_ids)
        for i, line in enumerate(self.__in_commands):
            removed = set()
            for qid in target_ids:
                if hack_contains_qid(line, qid):
                    line = hack_quantifier_removal(line, qid)
                    removed.add(qid)
                    log_info(f"[erase] erasing qid: {qid}")
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
        for i, line in enumerate(self.__in_commands):
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

    def skolemize_qids(self, target_ids: Set[str], erase: bool = False):
        # reduce to qids
        target_ids = {q[7:] if q.startswith("skolem_") else q for q in target_ids}
        # target_ids = self.__basic_check(target_ids)

        targets = dict()
        for qid in target_ids:
            assertion = self.quants[qid].assertion
            if assertion in targets:
                log_warn(f"[skolem] duplicated match on assertion, skipping: {qid}")
                continue
            targets[assertion] = qid
            # TODO: this is not very robust
            self._banish_ids.add(qid)

        for exp, qid in targets.items():
            commands, decls = self.__skolemize_assertion(exp)
            if erase:
                for i, line in enumerate(commands):
                    for qid in target_ids:
                        if hack_contains_qid(line, qid):
                            line = hack_quantifier_removal(line, qid)
                    commands[i] = line
            log_info(f"[skolem] qid: {qid}")
            log_info(f"[skolem] {len(decls)} skolem funs {len(commands)} asserts added")
            commands = [
                f'(set-info :comment "[skolem] {len(commands)} asserts for {qid}")'
            ] + commands
            self._fun_decls += decls
            self._new_commands += commands

    def __skolemize_assertion(self, exp):
        g = Goal()
        g.add(exp)
        t = Tactic("snf")
        res = t(g)
        assert len(res) == 1
        res = res[0]
        asserts, decls = [], []
        skf = SkolemFinder()
        for r in res:
            skf.find_sk_fun(r)
            asserts.append("(assert " + collapse_sexpr(r.sexpr()) + ")")
            for name, decl in skf.sk_funs.items():
                if name in self.cur_skolem_funs:
                    continue
                decls.append(decl)
        return asserts, decls

    def save(self, out_file_path):
        self.erase_qids(self._erase_ids)
        self.banish_qids(self._banish_ids)

        out_file = open(out_file_path, "w+")
        for i, line in enumerate(self.__in_commands[:-1]):
            if i in self._modified_lines:
                out_file.write(self._modified_lines[i])
            else:
                out_file.write(line)
        assert self.__in_commands[-1] == "(check-sat)\n"
        for line in self._fun_decls:
            out_file.write(line + "\n")
        for line in self._fun_asserts:
            out_file.write(line + "\n")
        for line in self._new_commands:
            out_file.write(line + "\n")
        out_file.write("(assert true)\n")
        out_file.write("(check-sat)\n")
        out_file.close()

        self._fun_decls = []
        self._fun_asserts = []
        self._new_commands = []
        self._modified_lines = dict()
        self._erase_ids = set()
        self._banish_ids = set()

        add_qids_to_query(out_file_path)
        log_info(f"[edit] written to {out_file_path}")


class QueryEditor(BasicQueryWriter):
    def __init__(self, in_file_path, pi: ProofInfo):
        super().__init__(in_file_path)
        self.pi = pi
        self.__enabled_symbols = set()

    def split_dual_qids(self, target_ids):
        target_ids = self._basic_check(target_ids)

        for qid in target_ids:
            quant = self.quants[qid]
            pq, qp = quant.split_dual()
            self._banish_ids.add(qid)
            self._new_commands += [pq, qp]

    def instantiate_qids(self, target_ids):
        target_ids = self._basic_check(target_ids)
        filtered = set()
        for qid in target_ids:
            if qid not in self.pi.qi_infos:
                log_warn(f"qid {qid} not found in proof!")
                continue
            filtered.add(qid)

        target_ids = {qid: self.pi.qi_infos[qid] for qid in filtered}

        for qid, qi in target_ids.items():
            quant = self.quants[qid]

            log_check(
                len(qi.errors) == 0,
                f"skipping instantiation target {qid} due to errors: "
                + "\t".join([str(e) for e in qi.errors]),
            )

            if len(qi.bindings) == 0:
                log_warn(f"no bindings for {qid}")
                continue

            _ = quant.get_vars()

            log_info(f"[inst] qid {qid} with {len(qi.bindings)} bindings")

            for j, bindings in enumerate(qi.bindings):
                subs = dict()
                self._new_commands.append(
                    f'(set-info :comment "[inst] qid {qid} {j+1}/{len(qi.bindings)} bindings")'
                )
                for i, b in bindings.items():
                    # TODO: do we always expect a hash cons?
                    if b.startswith("hcf_"):
                        self.__enabled_symbols.add(b)
                    subs[i] = b
                self._new_commands.append(quant.rewrite_as_let(subs))

            # TODO: we erase the original quantifier
            self._erase_ids.add(qid)

    def do_edits(self, target_ids: Dict[str, EditAction]):
        erase_qids = set()
        inst_qids = set()
        skol_qids = set()
        dual_qids = set()

        for qid in target_ids:
            action = target_ids[qid]
            if action == EditAction.ERASE:
                erase_qids.add(qid)
            elif action == EditAction.INSTANTIATE:
                inst_qids.add(qid)
            elif action == EditAction.SKOLEMIZE:
                skol_qids.add(qid)
            else:
                assert action == EditAction.DSPLIT
                dual_qids.add(qid)

        self.skolemize_qids(skol_qids)
        self.erase_qids(erase_qids)
        self.instantiate_qids(inst_qids)
        self.split_dual_qids(dual_qids)

    def save(self, out_file_path):
        # symbols = self.pi.tt.get_trans_deps(self.__enabled_symbols)
        defs = self.pi.tt.compress_defs(self.__enabled_symbols)
        # defs = self.pi.tt.as_define_funs(symbols)

        self._fun_asserts.extend(defs)
        super().save(out_file_path)
        self.__enabled_symbols = set()

if __name__ == "__main__":
    set_param(proof=True)
    
    w = BasicQueryWriter("dbg/mimalloc--segment__segment_span_free.smt2/orig.smt2")
    
    qt = w.quants["internal_lib!types.impl&__21.wf_main.?_definition"]
    print(collapse_sexpr(qt.assertion.sexpr()))
    print("(assert " + format_expr_flat(qt.assertion) + ")")

    # pi = ProofInfo.load("dbg/mimalloc--segment__segment_span_free.v2.smt2/insts/shuffle.11874912365756099194")
    # w = QueryEditor("dbg/mimalloc--segment__segment_span_free.v2.smt2/orig.smt2", pi)
    # w.split_dual_qids({
    #     "user_vstd__set__axiom_set_ext_equal_100",
    # })
    # w.save("test.smt2")
