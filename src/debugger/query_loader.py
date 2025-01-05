from typing import Dict
from z3 import *

from debugger.z3_utils import (
    Z3AstVisitor,
    collapse_sexpr,
    find_sk_decl_non_rec,
    format_expr_flat,
    quote_name,
    quote_sort,
)
from utils.system_utils import log_warn

class Z3QuantWrapper:
    def __init__(self, quant: z3.QuantifierRef, origin: z3.ExprRef, parent_name):
        self.quant = quant
        self.origin = origin
        self.name = quant.qid()
        self.parent_name = parent_name

    def is_root(self):
        return self.parent_name is None

    def __str__(self):
        return f"{self.quant.name} "

class QueryLoader(Z3AstVisitor):
    def __init__(self, in_file_path):
        super().__init__()
        self.query_path = in_file_path
        self.solver = Solver()

        self.solver.from_file(in_file_path)
        # map qid to its quantifier
        self.z3_quants: Dict[str, Z3QuantWrapper] = dict()

        self.existing_sk_decls = dict()

        in_cmds = open(in_file_path, "r").readlines()
        assert len(in_cmds) > 0
        assert in_cmds[-1] == "(check-sat)\n"
        self.query_goal = in_cmds[-2]
        assert(self.query_goal.startswith("(assert "))
        self.in_cmds = in_cmds[:-2]

        for a in self.solver.assertions():
            self.__load_quants(a, None, a)

        self.all_qnames = set(self.z3_quants.keys())
        self.reset_visit()
        # self.__load_root_conflicts()

    def __load_quants(self, exp: z3.ExprRef, parent, origin: z3.ExprRef):
        if self.visit(exp) or is_var(exp):
            return

        if sk := find_sk_decl_non_rec(exp):
            (qname, decl) = sk
            self.existing_sk_decls[qname] = decl

        if is_quantifier(exp):
            quant = Z3QuantWrapper(exp, origin, parent)
            assert quant.name not in self.z3_quants
            self.z3_quants[quant.name] = quant
            parent = quant.name

        for c in exp.children():
            self.__load_quants(c, parent, origin)

    # def get_root(self, name):
    #     quant = self.quants[name]
    #     while not quant.is_root():
    #         name = self.quants[name].parent_name
    #         quant = self.quants[name]
    #     return name

    # def __load_root_conflicts(self):
    #     constraints = dict()
    #     for qid, quant in self.quants.items():
    #         if not quant.is_root():
    #             continue
    #         a = quant.assertion
    #         if a in constraints:
    #             constraints[a].add(qid)
    #         else:
    #             constraints[a] = {qid}
    #     self.root_conflicts = [c for c in constraints.values() if len(c) > 1]

    # def has_conflicts(self, qid):
    #     root = self.get_root(qid)
    #     for c in self.root_conflicts:
    #         if root in c:
    #             return True
    #     return False

    # def group_costs(self, costs: Dict[str, int]) -> GroupedCost:
    #     fgs = dict()
    #     for qid in self.all_qids:
    #         rid = self.get_root(qid)
    #         if rid not in fgs:
    #             fgs[rid] = InstCost(rid)
    #         fg = fgs[rid]
    #         fg[qid] = costs.get(qid, 0)

    #     for fg in fgs.values():
    #         fg.finalize()

    #     return GroupedCost(fgs)
