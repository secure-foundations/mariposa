from typing import Dict
from z3 import *

from debugger.z3_utils import (
    AstVisitor,
    collapse_sexpr,
    format_expr_flat,
    hack_quantifier_body,
    quote_name,
)
from utils.system_utils import log_warn
import networkx as nx


class SkolemFinder(AstVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.sk_funs = dict()

    def find_sk_fun(self, e):
        if self.visit(e) or is_var(e):
            return

        if is_const(e):
            name = str(e)
            if "!skolem_" in name:
                # print(name)
                self.sk_funs[name] = collapse_sexpr(e.decl().sexpr())
            return

        if is_quantifier(e):
            return self.find_sk_fun(e.body())

        name = e.decl().name()

        if name in self.sk_funs:
            return

        if "!skolem_" in name:
            # print(name)
            self.sk_funs[name] = collapse_sexpr(e.decl().sexpr())
            return

        for c in e.children():
            self.find_sk_fun(c)


class Quant(AstVisitor):
    def __init__(self, quant, assertion):
        super().__init__()
        self.quant: QuantifierRef = quant
        self.assertion = assertion
        self.qid = quant.qid()

        self.__qbody_str = None
        self.__vars = None

        self.__eq = None
        self.dual = None

    def get_vars(self):
        if self.__vars is None:
            self.__vars = [
                (self.quant.var_name(idx), self.quant.var_sort(idx))
                for idx in range(self.quant.num_vars())
            ]
        return self.__vars

    def get_size(self):
        return len(self.quant.sexpr())

    # def _build_lets(self, subs):
    #     lets = []
    #     for idx, (v, s) in enumerate(self.get_vars()):
    #         v = quote_name(v)
    #         lets.append(f"({v} {subs[idx]})")
    #     return " ".join(lets)

    # def rewrite_as_let(self, subs):
    #     if self.__qbody_str is None:
    #         res = hack_quantifier_body(self.quant)
    #         self.__qbody_str = res[0]
    #         self.__quant_str = res[1]
    #         self.__assert_str = (
    #             "(assert " + collapse_sexpr(self.assertion.sexpr()) + ")"
    #         )
    #     lets = f"(let ({self._build_lets(subs)}) {self.__qbody_str})"
    #     assert self.__quant_str in self.__assert_str
    #     return self.__assert_str.replace(self.__quant_str, lets)

    def _build_lets(self, subs):
        lets = []
        vs = self.get_vars()
        for idx in range(len(vs)):
            lets.append(f"({self.quant.var_name(idx)} {subs[idx]})")
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

    def split_dual(self):
        # assert self.__eq is not None
        self.__setup_rewrite()
        self.find_dual()

        assert self.__eq is not None
        assert self.__eq in self.__assert_str

        pq = f"(=> {self.__p} {self.__q})"
        qp = f"(=> {self.__q} {self.__p})"

        return [
            f"{self.__assert_str.replace(self.__eq, pq)}",
            f"{self.__assert_str.replace(self.__eq, qp)}",
        ]
        
    def get_skolem_dual(self):
        l, r = self.split_dual()
        if self.left_dual:
            return l
        return r

    def find_dual(self):
        if self.dual is not None:
            return self.dual

        self.__find_dual(self.assertion)
        self.reset_visit()

        if self.dual is None:
            self.dual = False

        return self.dual

    def __find_dual(self, exp):
        if self.visit(exp) or is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            assert False

        if exp.sort().kind() != Z3_BOOL_SORT:
            return

        if exp.decl().name() == "=":
            p, q = exp.children()

            if p.sort().kind() != Z3_BOOL_SORT:
                return

            target = self.quant.get_id()

            if p.get_id() == target or q.get_id() == target:
                if self.__eq is not None:
                    log_warn(f"multiple equalities found in qid: {self.quant.qid()}")
                    return

                self.left_dual = p.get_id() == target
                self.__eq = format_expr_flat(exp)
                self.__p = format_expr_flat(p)
                self.__q = format_expr_flat(q)
                self.dual = True

                return

        for c in exp.children():
            self.__find_dual(c)


class QueryLoader(AstVisitor):
    def __init__(self, in_file_path):
        super().__init__()
        self.proc_solver = Solver()
        self.proc_solver.set("timeout", 30000)

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

        self.cur_skolem_funs = finder.sk_funs
        self.all_qids = set(self.quants.keys())
        self.reset_visit()
        self.__load_root_conflicts()

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

    def is_root(self, qid):
        if qid not in self.parent_id:
            log_warn(f"root (?) qid {qid} not found")
            return False
        return self.parent_id[qid] is None

    def get_root(self, qid):
        while qid in self.parent_id:
            pid = self.parent_id[qid]
            if pid is None:
                return qid
            qid = pid
        return qid

    def get_parent(self, qid):
        if qid not in self.parent_id:
            log_warn(f"parent (?) qid {qid} not found")
            return qid
        return self.parent_id[qid]

    def __load_root_conflicts(self):
        constraints = dict()
        for qid, qt in self.quants.items():
            if not self.is_root(qid):
                continue
            a = qt.assertion
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


class InstFreq:
    def __init__(self, rid):
        self.rid = rid
        self.group = dict()
        self.__finalized = False
        self.total_count = 0
        self.root_count = 0

    def __getitem__(self, qid):
        return self.group[qid]

    def __setitem__(self, qid, count):
        self.group[qid] = count

    def __iter__(self):
        assert self.__finalized
        return iter(self.group)

    def is_singleton(self):
        return len(self.group) == 1

    def finalize(self):
        assert not self.__finalized
        self.__finalized = True
        self.total_count = sum(self.group.values())
        self.root_count = self.group[self.rid]

    def is_user_only(self):
        if self.is_singleton():
            return self.rid.startswith("user_")

        for qid in self.group:
            if qid != self.rid and not qid.startswith("user_"):
                return False
        return True


class QueryInstFreq:
    # group a flat frequency map by root qids
    def __init__(self, loader: QueryLoader, freq: Dict[str, int]):
        res = dict()
        for qid in loader.all_qids:
            if qid not in freq:
                freq[qid] = 0
            rid = loader.get_root(qid)
            if rid not in res:
                res[rid] = InstFreq(rid)
            res[rid][qid] = freq[qid]

        for f in res.values():
            f.finalize()

        self.total_count = sum(freq.values())
        self.freqs: Dict[str, InstFreq] = res

    def __getitem__(self, qid):
        return self.freqs[qid]

    def __contains__(self, qid):
        return qid in self.freqs
    
    def __iter__(self):
        return iter(self.freqs)

    def order_by_freq(self):
        s = sorted(self.freqs.values(), key=lambda x: x.total_count, reverse=True)
        return map(lambda x: x.rid, s)
