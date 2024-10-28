import binascii
import os
import re
from typing import Set, Tuple

from tqdm import tqdm

from debugger.query_loader import SkolemFinder
from z3 import ExprRef, is_const, is_var, is_app, is_quantifier

def hack_find_hcf_id(s: str):
    res = re.search("(hcf_[^( |\))]+)", s)
    if res is None:
        return None
    name = res.group(1)
    return name

class TermTable(SkolemFinder):
    def __init__(self):
        super().__init__()
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
        self.visit(e)

    def create_defs(self):
        for e in tqdm(self.visited()):
            if not is_app(e):
                continue
            self._create_defs(e)

    def _create_defs(self, e: ExprRef) -> Tuple[str, Set[str]]:
        if is_var(e) or is_quantifier(e):
            assert False

        if is_const(e):
            return (str(e), set())

        if e in self._defs:
            name = self._defs[e][0]
            return (name, {name})

        res = [e.decl().name()]
        deps = set()

        for c in e.children():
            r, d = self._create_defs(c)
            res.append(r)
            deps.update(d)

        res = "(" + " ".join(res) + ")"

        assert e not in self._defs
        new_name = self.__get_fresh_name()
        self.depends[new_name] = deps
        # print(new_name, res)
        self._defs[e] = (new_name, res, str(e.sort()))
        return (new_name, {new_name})

    def rewrite_expr(self, e: ExprRef):
        if is_const(e) or is_var(e):
            return str(e)

        if e in self._defs:
            return self._defs[e][0]

        args = [self.rewrite_expr(c) for c in e.children()]
        return f"({e.decl().name()} {' '.join(args)})"

    def finalize(self):
        for (_, v) in self._defs.items():
            self.defs[v[0]] = v[1:]
        self.reset_visit()
        self._defs.clear()

    def get_trans_deps(self, symbols):
        res = set()
        if isinstance(symbols, str):
            symbols = [symbols]
        for s in symbols:
            res.update(self._get_trans_deps(s))
        return res

    def _get_trans_deps(self, symbol):
        deps = self.depends[symbol]
        res = {symbol}
        if len(deps) == 0:
            return res
        res.update(deps)
        for d in deps:
            res.update(self.get_trans_deps(d))
        return res

    def expand_def(self, name):
        return self._expand_def(name)

    def _expand_def(self, body):
        res = []
        items = body.split(" ")
        for item in items:
            name = hack_find_hcf_id(item)
            if name is not None:
                body = self.defs[name][0]
                body = self._expand_def(body)
                res.append(item.replace(name, body))
            else:
                res.append(item)
        return " ".join(res)

    def estimate_size(self, symbols):
        if isinstance(symbols, str):
            symbols = [symbols]
        t_symbols = self.get_trans_deps(symbols)
        size = 0
        for s in t_symbols:
            size += len(self.defs[s][1])
        return size

    def debug(self):
        print("defs")
        for k, v in self.defs.items():
            print(k, v)

        print("depends")
        for k, v in self.depends.items():
            print(k, v)
