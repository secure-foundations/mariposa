import binascii
import os
import re
from typing import Set, Tuple

from debugger.z3_utils import AstVisitor
from z3 import ExprRef, is_const, is_var, is_quantifier

def hack_find_hcf_id(s: str):
    res = re.search("(hcf_[^( |\))]+)", s)
    if res is None:
        return None
    name = res.group(1)
    return name

class TermTable(AstVisitor):
    def __init__(self):
        super().__init__()
        self._ref_counts = dict()
        self._defs = dict()

        self.defs = dict()
        self.depends = dict()

        # TODO: this is a lazy way to avoid name clashes
        self.__fun_prefix = (
            "hcf_" + binascii.hexlify(os.urandom(4)).decode("utf-8") + "_"
        )

    def __get_fresh_name(self):
        return self.__fun_prefix + str(len(self._defs))

    def process_expr(self, e):
        self._count_refs(e)

    def _count_refs(self, e: ExprRef):
        if is_var(e) or is_const(e):
            return

        if self.visit(e):
            self._ref_counts[e] += 1
            return

        self._ref_counts[e] = 1

        for c in e.children():
            self._count_refs(c)

    def create_defs(self):
        targets = set()
        for e, c in self._ref_counts.items():
            if c >= 1:
                targets.add(e)

        for e in targets:
            self._create_defs(e, targets)

    def _create_defs(self, e: ExprRef, targets) -> Tuple[str, Set[str]]:
        if is_var(e) or is_quantifier(e):
            assert False

        if is_const(e):
            return (str(e), set())

        if e in self._defs:
            name = self._defs[e][0]
            return (name, {name})

        fun = e.decl().name()
        res = [fun]
        deps = set()

        for c in e.children():
            r, d = self._create_defs(c, targets)
            res.append(r)
            deps.update(d)

        res = "(" + " ".join(res) + ")"

        if e in targets:
            new_name = self.__get_fresh_name()
            self.depends[new_name] = deps
            print(new_name, res)
            self._defs[e] = (new_name, res, str(e.sort()))
            return (new_name, {new_name})
        return (res, deps)

    def rewrite_expr(self, e: ExprRef):
        if is_const(e) or is_var(e):
            return str(e)

        if e in self._defs:
            return self._defs[e][0]

        args = [self.rewrite_expr(c) for c in e.children()]
        return f"({e.decl().name()} {' '.join(args)})"

    def finalize(self):
        for (e, v) in self._defs.items():
            self.defs[v[0]] = v[1:]
        self.reset_visit()
        self._ref_counts.clear()
        self._defs.clear()

    def get_trans_deps(self, name):
        deps = self.depends[name]
        res = set()
        if len(deps) == 0:
            return res
        res.update(deps)
        for d in deps:
            res.update(self.get_trans_deps(d))
        return res

    def expand_def(self, name):
        return self._expand_def(name)
    
    def estimate_size(self, symbols):
        if isinstance(symbols, str):
            symbols = [symbols]
        t_symbols = set()
        for s in symbols:
            t_symbols.update(self.get_trans_deps(s))
            t_symbols.add(s)
        size = 0
        for s in t_symbols:
            size += len(self.defs[s][1])
        return size

    def _expand_def(self, body):
        res = []
        items = body.split(" ")
        for item in items:
            name = hack_find_hcf_id(item)
            if name is not None:
                defi = self.defs[name][0]
                defi = self._expand_def(defi)
                res.append(item.replace(name, defi))
            else:
                res.append(item)
        return " ".join(res)

    def debug(self):
        print("defs")
        for k, v in self.defs.items():
            print(k, v)

        print("depends")
        for k, v in self.depends.items():
            print(k, v)