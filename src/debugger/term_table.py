import binascii
import os
import re
from typing import Set, Tuple
from collections import Counter

from tqdm import tqdm

from debugger.query_loader import SkolemFinder
from debugger.z3_utils import collapse_sexpr, quote_name
from z3 import ExprRef, is_const, is_var, is_app, is_quantifier, Z3_OP_DT_IS


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
        return self._create_defs(e)

    def _create_defs(self, e: ExprRef) -> str:
        if not is_app(e):
            assert False

        if is_const(e):
            return quote_name(str(e))

        if self.visit(e):
            assert e in self._defs
            name = self._defs[e][0]
            return name

        if e.decl().kind() == Z3_OP_DT_IS:
            assert e.decl().name() == "is"
            params = e.decl().params()
            assert len(params) == 1
            # print(e.decl().params())
            # print(collapse_sexpr(e.sexpr()))
            # print(e.decl())
            res = [f"(_ is {quote_name(params[0].name())})"]
        else:
            res = [quote_name(e.decl().name())]

        deps = set()

        for c in e.children():
            r = self._create_defs(c)
            res.append(r)
            if hack_find_hcf_id(r) is not None:
                deps.add(r)

        res = "(" + " ".join(res) + ")"
        new_name = self.__get_fresh_name()

        self.depends[new_name] = deps
        self._defs[e] = (new_name, res, str(e.sort()))
        return new_name

    def finalize(self):
        for _, v in self._defs.items():
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

    def order_symbols(self, symbols):
        if isinstance(symbols, str):
            symbols = [symbols]
        order = []
        for d in symbols:
            order.append((int(d.split("_")[-1]), d))
            assert d in self.defs
        return [d[1] for d in sorted(order)]

    # def export_define_funs(self, symbols):
    #     if isinstance(symbols, str):
    #         symbols = [symbols]
    #     res = []
    #     for s in self.order_symbols(symbols):
    #         res.append(self.export_define_fun(s))
    #     return res
    
    # def export_define_fun(self, symbol, alt_def=None):
    #     d, sort = self.defs[symbol]
    #     if alt_def is not None:
    #         d = alt_def
    #     return f"(define-fun {symbol} () {sort} {d})"

    def export_declare_fun(self, symbol, alt_def=None):
        d, sort = self.defs[symbol]
        if alt_def is not None:
            d = alt_def
        return [f"(declare-fun {symbol} () {sort})",
                f"(assert (= {symbol} {d}))"]

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

    def get_ref_count(self, symbols):
        if isinstance(symbols, str):
            symbols = [symbols]

        counts = Counter()
        for s in symbols:
            body = self.defs[s][0]
            self._get_ref_count(body, counts)

        return counts

    def _get_ref_count(self, body, counts):
        items = body.split(" ")
        for item in items:
            name = hack_find_hcf_id(item)
            if name is None:
                continue
            body = self.defs[name][0]
            if name not in counts:
                self._get_ref_count(body, counts)
            counts[name] += 1

    def compress_defs(self, symbols):
        refs = self.get_ref_count(symbols)
        tc_symbols = self.get_trans_deps(symbols)
        assert tc_symbols == set(refs.keys()) | set(symbols)
        tc_symbols = self.order_symbols(tc_symbols)

        new_defs = dict()

        for s in tc_symbols:
            old_def = self.defs[s][0]
            nd = self._compress_defs(old_def, refs, new_defs)
            nd = nd.replace("False", "false")
            new_defs[s] = nd

        res = []
        for s in new_defs:
            if refs[s] == 1 and s not in symbols:
                continue
            res += self.export_declare_fun(s, new_defs[s])
    
        return res

    def _compress_defs(self, body, refs, defs):
        res = []
        items = body.split(" ")
        for item in items:
            name = hack_find_hcf_id(item)
            if name is not None and refs[name] == 1:
                if len(self.depends[name]) == 0:
                    res.append(item.replace(name, self.defs[name][0]))
                else:
                    # assert name in defs
                    res.append(item.replace(name, defs[name]))
            else:
                res.append(item)
        return " ".join(res)
