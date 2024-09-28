from typing import Dict
from z3 import *

from debugger.z3_utils import AstVisitor, collapse_sexpr, hack_quantifier_body
from utils.system_utils import log_warn


class SkolemFinder(AstVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.funs = dict()

    def find_sk_fun(self, e):
        if self.visit(e) or is_var(e):
            return

        if is_const(e):
            if "$!skolem_" in str(e):
                self.funs[str(e)] = collapse_sexpr(e.decl().sexpr())
            return

        if is_quantifier(e):
            return self.find_sk_fun(e.body())

        name = e.decl().name()

        if name in self.funs:
            return

        if "$!skolem_" in name:
            self.funs[name] = collapse_sexpr(e.decl().sexpr())
            return

        for c in e.children():
            self.find_sk_fun(c)


class Quant:
    def __init__(self, quant, assertion):
        self.quant: QuantifierRef = quant
        self.assertion = assertion
        self.qid = quant.qid()

        self.__qbody_str = None
        self.__vars = None

    def is_root(self):
        return self.parent is None
    
    def get_vars(self):
        if self.__vars is None:
            self.__vars = [
                (self.quant.var_name(idx), self.quant.var_sort(idx))
                for idx in range(self.quant.num_vars())
            ]
        return self.__vars

    def rewrite_as_let(self, subs):
        if self.__qbody_str is None:
            self.__qbody_str = hack_quantifier_body(self.quant)

        res = self.__as_let(self.assertion, subs)
        return "(assert " + res + ")"

    def __as_let(self, e, subs):
        if is_const(e):
            return str(e)

        if is_quantifier(e):
            if e.qid() == self.qid:
                # create let bindings for the quantified variables
                lets = []
                for idx in range(e.num_vars()):
                    if idx not in subs:
                        print(self.qid, idx)
                    lets.append(f"({e.var_name(idx)} {subs[idx]})")
                lets = " ".join(lets)
                lets = f"(let\n({lets}) {self.__qbody_str})"
                return lets
            else:
                return e.sexpr()

        items = [self.__as_let(i, subs) for i in e.children()]
        items = " ".join(items)
        items = "(" + e.decl().name() + " " + items + ")"
        return items


class QueryLoader(AstVisitor):
    def __init__(self, in_file_path):
        super().__init__()
        self.proc_solver = Solver()
        self.proc_solver.set("timeout", 60000)

        self.in_file_path = in_file_path
        self.proc_solver.from_file(in_file_path)
        # map qid to its quantifier
        self.quants: Dict[str, Quant] = dict()
        # root qids with nested quantifiers
        self.parent_id = dict()
        # self.existing_skolem_funs = dict()
        finder = SkolemFinder()

        for a in self.proc_solver.assertions():
            self.__load_quantifiers(a, None, a)
            finder.find_sk_fun(a)

        self.cur_skolem_funs = finder.funs
        self.all_qids = set(self.quants.keys())
        self.reset_visit()

    def __load_quantifiers(self, exp: z3.ExprRef, parent, assertion):
        if self.visit(exp) or is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            qid = exp.qid()
            qt = Quant(exp, assertion)
            self.parent_id[qid] = parent
            self.quants[qid] = qt
            parent = qid

        for c in exp.children():
            self.__load_quantifiers(c, parent, assertion)

    def get_root(self, qid):
        while qid in self.parent_id:
            pid = self.parent_id[qid]
            if pid is None:
                return qid
            qid = pid
        return qid
