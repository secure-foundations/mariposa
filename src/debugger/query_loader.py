from typing import Dict
from z3 import *

from debugger.z3_utils import (
    AstVisitor,
    collapse_sexpr,
    format_expr_flat,
    quote_name,
    quote_sort,
)
from utils.system_utils import log_warn


# class SkolemFinder(AstVisitor):
#     def __init__(self) -> None:
#         super().__init__()
#         self.sk_funs = dict()

#     def find_sk_fun(self, e):
#         if self.visit(e) or is_var(e):
#             return

#         if is_const(e):
#             name = str(e)
#             if "!skolem_" in name:
#                 # print(name)
#                 self.sk_funs[name] = collapse_sexpr(e.decl().sexpr())
#             return

#         if is_quantifier(e):
#             return self.find_sk_fun(e.body())

#         name = e.decl().name()

#         if name in self.sk_funs:
#             return

#         if "!skolem_" in name:
#             # print(name)
#             self.sk_funs[name] = collapse_sexpr(e.decl().sexpr())
#             return

#         for c in e.children():
#             self.find_sk_fun(c)


class Quant(AstVisitor):
    def __init__(self, quant, assertion, parent):
        super().__init__()
        self.quant: QuantifierRef = quant
        self.assertion = assertion

        self.name = quant.qid()
        self.parent_name = parent

        self.__qbody_str = None
        self.__vars = None

        # self.__eq = None
        # self.dual = None

    def is_root(self):
        return self.parent_name is None

    def get_vars(self):
        if self.__vars is not None:
            return self.__vars
        self.__vars = [
            (quote_name(self.quant.var_name(idx)), quote_sort(self.quant.var_sort(idx)))
            for idx in range(self.quant.num_vars())
        ]
        return self.__vars

    def _build_lets(self, subs):
        lets = []
        vs = self.get_vars()
        for i in range(len(vs)):
            lets.append(f"({vs[i][0]} {subs[i]})")
        return " ".join(lets)

    def __setup_rewrite(self):
        if self.__qbody_str is not None:
            return
        self.__qbody_str = format_expr_flat(self.quant, True)
        self.__quant_str = format_expr_flat(self.quant)
        self.__assert_str = "(assert " + format_expr_flat(self.assertion) + ")"
        assert self.__quant_str in self.__assert_str

    def rewrite_as_let(self, subs):
        self.__setup_rewrite()
        lets = f"(let ({self._build_lets(subs)}) {self.__qbody_str})"
        return self.__assert_str.replace(self.__quant_str, lets)

class InstCost:
    def __init__(self, rid):
        self.rid = rid
        self.group = dict()
        self.__finalized = False
        self.subtotal = 0

    def __getitem__(self, qid):
        return self.group[qid]

    def __setitem__(self, qid, count):
        self.group[qid] = count

    def __iter__(self):
        assert self.__finalized
        return iter(self.group)

    def is_singleton(self):
        assert self.__finalized
        return len(self.group) == 1

    def finalize(self):
        assert not self.__finalized
        assert self.rid in self.group
        self.__finalized = True
        self.subtotal = sum(self.group.values())
        # self.root_cost = self.group[self.rid]

class GroupedCost:
    def __init__(self, fgs: Dict[str, InstCost]):
        self._groups = fgs
        self.total = 0
        self._root_qids = dict()

        for fg in fgs.values():
            for qid in fg:
                self._root_qids[qid] = fg.rid
            self.total += fg.subtotal

    def get_count(self, qid):
        return self._groups[self._root_qids[qid]][qid]

    def __getitem__(self, qid):
        return self._groups[qid]

    def __contains__(self, qid):
        return qid in self._groups

    def __iter__(self):
        return iter(self._groups)

class QueryLoader(AstVisitor):
    def __init__(self, in_file_path):
        super().__init__()
        self.proc_solver = Solver()
        self.proc_solver.set("timeout", 60000)

        self.in_file_path = in_file_path
        self.proc_solver.from_file(in_file_path)
        # map qid to its quantifier
        self.quants: Dict[str, Quant] = dict()

        # self.existing_skolem_funs = dict()
        finder = SkolemFinder()

        for a in self.proc_solver.assertions():
            self.__load_quantifiers(a, None, a)
            finder.find_sk_fun(a)

        self.cur_skolem_funs = finder.sk_funs
        self.all_qids = set(self.quants.keys())
        self.reset_visit()
        self.__load_root_conflicts()

    def __load_quantifiers(self, exp: z3.ExprRef, parent, assertion):
        if self.visit(exp) or is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            quant = Quant(exp, assertion, parent)
            assert quant.name not in self.quants
            self.quants[quant.name] = quant
            parent = quant.name

        for c in exp.children():
            self.__load_quantifiers(c, parent, assertion)

    def get_root(self, name):
        quant = self.quants[name]
        while not quant.is_root():
            name = self.quants[name].parent_name
            quant = self.quants[name]
        return name

    def __load_root_conflicts(self):
        constraints = dict()
        for qid, quant in self.quants.items():
            if not quant.is_root():
                continue
            a = quant.assertion
            if a in constraints:
                constraints[a].add(qid)
            else:
                constraints[a] = {qid}
        self.root_conflicts = [c for c in constraints.values() if len(c) > 1]

    def has_conflicts(self, qid):
        root = self.get_root(qid)
        for c in self.root_conflicts:
            if root in c:
                return True
        return False

    def group_costs(self, costs: Dict[str, int]) -> GroupedCost:
        fgs = dict()
        for qid in self.all_qids:
            rid = self.get_root(qid)
            if rid not in fgs:
                fgs[rid] = InstCost(rid)
            fg = fgs[rid]
            fg[qid] = costs.get(qid, 0)

        for fg in fgs.values():
            fg.finalize()

        return GroupedCost(fgs)
