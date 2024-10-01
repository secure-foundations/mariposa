import binascii
from typing import Dict, Set
from z3 import *
from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.z3_utils import collapse_sexpr, hack_contains_qid, hack_quantifier_removal
from proof_reader import ProofInfo, QunatInstInfo
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from utils.query_utils import add_qids_to_query


class BasicQueryWriter(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)
        self.in_file_path = in_file_path
        self.__in_commands = open(self.in_file_path, "r").readlines()

        assert len(self.__in_commands) > 0
        assert self.__in_commands[-1] == "(check-sat)\n"

        self._fun_defs = []
        self._new_commands = []

        self._erase_ids = set()
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
                self.__in_commands[i] = line
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
                    self.__in_commands[i] = ""
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
            self._fun_defs += decls
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
            for name, decl in skf.funs.items():
                if name in self.cur_skolem_funs:
                    continue
                decls.append(decl)
        return asserts, decls

    def write(self, out_file_path):
        self.erase_qids(self._erase_ids)
        self.banish_qids(self._banish_ids)

        out_file = open(out_file_path, "w+")
        for line in self.__in_commands[:-1]:
            out_file.write(line)
        assert self.__in_commands[-1] == "(check-sat)\n"
        for line in self._fun_defs:
            out_file.write(line + "\n")
        for line in self._new_commands:
            out_file.write(line + "\n")
        out_file.write("(assert true)\n")
        out_file.write("(check-sat)\n")
        out_file.close()
        print(f"written to {out_file_path}")
        add_qids_to_query(out_file_path)


class QueryEditor(BasicQueryWriter):
    def __init__(self, in_file_path, pi: ProofInfo):
        super().__init__(in_file_path)
        self.pi = pi
        # this is a lazy way to avoid name clashes
        self.__fun_prefix = (
            "fn_" + binascii.hexlify(os.urandom(4)).decode("utf-8") + "_"
        )
        self.__fun_cache = dict()

    def __get_fresh_name(self):
        return self.__fun_prefix + str(len(self._fun_defs))

    def __add_def_fun(self, body, sort):
        if body in self.__fun_cache:
            return self.__fun_cache[body]
        name = self.__get_fresh_name()
        func = [
            f"(declare-fun {name} () {sort})",
            "(assert (= " + name + " " + body + "))",
        ]
        self._fun_defs += func
        self.__fun_cache[body] = name
        return name

    def instantiate_qids(self, target_ids):
        target_ids = self._basic_check(target_ids)
        target_ids = {qid: self.pi.qi_infos[qid] for qid in target_ids}

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

            # for bindings in qi.bindings:
            #     for i, b in bindings.items():
            #         print(i, b)

            vars = quant.get_vars()
            log_info(f"[inst] qid {qid} with {len(qi.bindings)} bindings")

            for j, bindings in enumerate(qi.bindings):
                subs = dict()
                self._new_commands.append(
                    f'(set-info :comment "[inst] qid {qid} {j+1}/{len(qi.bindings)} bindings")'
                )
                for i, b in bindings.items():
                    name = self.__add_def_fun(b, vars[i][1])
                    subs[i] = name
                self._new_commands.append(quant.rewrite_as_let(subs))

            # TODO: we erase the original quantifier
            self._erase_ids.add(qid)
