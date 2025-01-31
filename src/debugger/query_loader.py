from typing import Dict, List, Set
from z3.z3 import *

from debugger.z3_utils import (
    Z3AstVisitor,
    collapse_sexpr,
    format_expr_flat,
    match_sk_decl_used,
    quote_name,
    quote_sort,
)
from utils.system_utils import log_warn

class Z3QuantWrapper:
    def __init__(self, quant: z3.QuantifierRef, parent, origin: z3.ExprRef):
        self.quant = quant
        self.origin = origin
        self.name = quant.qid()
        self.parent: Z3QuantWrapper = parent
        self.group_qnames: Set[str] = set()

    def __str__(self):
        return f"Z3Qref@{self.quant.name}"

    def is_root(self):
        return self.parent is None

    def get_root_qname(self):
        if self.is_root():
            return self.name
        return self.parent.get_root_qname()
    
    def is_singleton(self):
        return len(self.group_qnames) == 1

class QueryLoader(Z3AstVisitor):
    def __init__(self, in_file_path):
        super().__init__()
        self.query_path = in_file_path
        self.solver = Solver()

        self.solver.from_file(in_file_path)
        # map qid to its quantifier
        self.__z3_quants: Dict[str, Z3QuantWrapper] = dict()
        self.existing_sk_decls: Dict[str, str] = dict()

        in_cmds = open(in_file_path, "r").readlines()
        assert len(in_cmds) > 0
        assert in_cmds[-1] == "(check-sat)\n"
        self.query_goal = in_cmds[-2]
        assert(self.query_goal.startswith("(assert "))
        self.in_cmds = in_cmds[:-2]

        for a in self.solver.assertions():
            self.__load_quants(a, None, a)
        self.reset_visit()

        root_qnames: Dict[str, Set[str]] = dict()

        for name, quant in self.__z3_quants.items():
            root_name = quant.get_root_qname()
            if root_name in root_qnames:
                root_qnames[root_name].add(name)
            else:
                root_qnames[root_name] = {name}

        for name, quant in self.__z3_quants.items():
            if not quant.is_root():
                continue
            quant.group_qnames = root_qnames[name]

        self.__root_qnames: Set[str] = set(root_qnames.keys())
        self.__colocated_roots: List[Set[str]] = []
        self.__identify_colocated_roots()

    def __load_quants(self, exp: z3.ExprRef, parent, origin: z3.ExprRef):
        tasks = [(exp, parent, origin)]

        while len(tasks) > 0:
            exp, parent, origin = tasks.pop()
            
            if self.visit(exp) or is_var(exp):
                continue

            if sk := match_sk_decl_used(exp):
                (qname, decl) = sk
                self.existing_sk_decls[qname] = decl

            if is_quantifier(exp):
                quant = Z3QuantWrapper(exp, parent, origin)
                assert quant.name not in self.__z3_quants
                self.__z3_quants[quant.name] = quant
                parent = quant

            for c in exp.children():
                tasks.append((c, parent, origin))

    def __identify_colocated_roots(self):
        colocated_roots = dict()
        for qname, quant in self.__z3_quants.items():
            if not quant.is_root():
                continue
            origin = quant.origin
            if origin not in colocated_roots:
                colocated_roots[origin] = set()
            colocated_roots[origin].add(qname)

        for qnames in colocated_roots.values():
            if len(qnames) <= 1:
                continue
            self.__colocated_roots.append(qnames)

    def is_singleton(self, qname):
        return len(self.__z3_quants[qname].group_qnames) == 1
    
    def is_root(self, qname):
        return self.__z3_quants[qname].is_root()

    def is_colocated(self, qname):
        for qnames in self.__colocated_roots:
            if qname in qnames:
                return True
        return False

    def list_qnames(self, root_only=False):
        if root_only:
            return self.__root_qnames
        return self.__z3_quants.keys()

    def __getitem__(self, qname) -> Z3QuantWrapper:
        return self.__z3_quants[qname]

    def __contains__(self, qname):
        return qname in self.__z3_quants

    def __iter__(self):
        for qname in self.__z3_quants:
            yield self.__z3_quants[qname]

    def items(self, root_only=False):
        if root_only:
            for qname in self.__root_qnames:
                yield qname, self.__z3_quants[qname]
        else:
            return self.__z3_quants.items()

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
