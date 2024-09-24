import time
import pickle
from typing import Dict

from tabulate import tabulate
from base.defs import MARIPOSA
from query.inst_mapper import SubsMapper, Quant, collapse_sexpr
from z3 import *
from enum import Enum

from utils.system_utils import log_info, log_warn, subprocess_run

set_param(proof=True)

def match_qi(p):
    if p.decl().name() != "quant-inst":
        return None
    assert p.num_args() == 1
    p = p.arg(0)
    assert is_app_of(p, Z3_OP_OR)
    l, r = p.arg(0), p.arg(1)
    assert is_app_of(l, Z3_OP_NOT)
    l = l.arg(0)
    assert is_quantifier(l)
    # print("(assert " + format_expr(r, 0) +")")
    return (l.qid(), r)


def match_sk(p):
    if p.decl().name() != "sk":
        return None
    assert p.num_args() == 1
    p = p.arg(0)
    assert is_app_of(p, Z3_OP_OEQ)
    l, r = p.arg(0), p.arg(1)
    if is_app_of(l, Z3_OP_NOT):
        assert is_app_of(r, Z3_OP_NOT)
        l, r = l.arg(0), r.arg(0)
    return (l.skolem_id(), r)


def is_quantifier_free(e):
    if is_const(e):
        return True
    if is_quantifier(e):
        return False
    for c in e.children():
        if not is_quantifier_free(c):
            return False
    return True


class ProofInfo:
    def __init__(self, handled, errors, sk_funs):
        self.handled = handled
        self.errors = errors
        self.sk_funs = sk_funs
        self.used_qids = set(handled.keys()) | set(errors.keys())
        self.parents = dict()

    def get_inst_count(self, qid):
        if qid in self.handled:
            return len(self.handled[qid])
        if qid in self.errors:
            return self.errors[qid][1]
        return 0

    def has_qid(self, qid):
        return qid in self.handled or qid in self.errors
    
    def print_report(self):
        table = []
        for qid, insts in self.handled.items():
            table.append((qid, len(insts)))
        log_info("listing handled quantifiers:")
        print(tabulate(table, headers=["qid", "insts"]))
        log_info("listing errors:")
        table = []
        for qid, (msg, count, parent) in self.errors.items():
            table.append((qid, msg, count, parent))
        print(tabulate(table, headers=["qid", "error", "count", "parent"]))
        log_info("listing skolem functions:")
        for sk_fun in self.sk_funs:
            print(sk_fun)

    @staticmethod
    def load(file_path):
        with open(file_path, "rb") as f:
            return pickle.load(f)

class InstError(Enum):
    UNMAPPED_VARS = 1
    NON_ROOT = 2
    SKOLEM_FUNS = 3

class Instantiater:
    def __init__(self, in_file_path):
        self.proc_solver = Solver()
        self.solver_opts = []
        self.proof_time = None
        # self.sk_vars = dict()
        self.sk_funcs = dict()
        self.in_file_path = in_file_path

        self.proc_solver.set("timeout", 60000)

        with open(in_file_path, "r") as f:
            for line in f.readlines():
                if line.startswith("(set-option"):
                    self.solver_opts.append(line)

        self.proc_solver.from_file(in_file_path)

        # map qid to its quantifier
        self.quants: Dict[str, Quant] = dict()
        # root qids with nested quantifiers
        self.root_qids = set()
        self.__init_qids()
        
        assert "user_vstd__set__axiom_set_remove_different_94" in self.root_qids

        # map qid to its quant-inst applications
        self.insts = dict()
        self.__visited = set()

        self.inst_freq = dict()

    def __init_qids(self):
        for a in self.proc_solver.assertions():
            # print(collapse_sexpr(simplify(a).sexpr()))
            self.__load_quantifiers(a, None, a)

        for qid, qtf in self.quants.items():
            if qtf.parent is None:
                self.root_qids.add(qid)

        self.parents = dict()

        for qid, qt in self.quants.items():
            if qt.parent is not None:
                self.parents[qid] = qt.parent

    def __load_quantifiers(self, exp: z3.ExprRef, parent, assertion):
        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            qid = exp.qid()
            qt = Quant(exp, parent)
            qt.assertion = assertion
            self.quants[qid] = qt
            parent = qid

        for c in exp.children():
            self.__load_quantifiers(c, parent, assertion)

    def get_root(self, qid):
        while qid in self.parents:
            qid = self.parents[qid]
        return qid

    def accumulate_inst_count(self, trace):
        roots = dict()
        # attribute the count to the root quantifier
        for qid, count in trace.items():
            root = self.get_root(qid)
            if root not in roots:
                roots[root] = dict()
            roots[root][qid] = count
        for qid in roots:
            roots[qid]["isum"] = sum(roots[qid].values())
        return roots

    def process(self):
        start = time.time()
        res = self.proc_solver.check()
        self.proof_time = int((time.time() - start) * 1000)

        if res != unsat:
            log_warn("[proof] query returned {0}".format(res))
            return False

        p = self.proc_solver.proof()
        self.__match_qis(p)

        self.inst_freq = dict(map(lambda x: (x[0], len(x[1])), self.insts.items()))

        return True

    def __match_qis(self, p):
        oid = p.get_id()
        if oid in self.__visited:
            return
        self.__visited.add(oid)

        if is_const(p) or is_var(p):
            return

        if is_quantifier(p):
            p = p.body()

        res = match_qi(p)

        if res is not None:
            qid, qi = res
            self.insts[qid] = self.insts.get(qid, set()) | {qi}

        for c in p.children():
            self.__match_qis(c)

    def __has_sk_fun(self, e):        
        oid = e.get_id()
        if oid in self.__visited:
            return self.__visited[oid]

        if is_const(e):
            if "$!skolem_" in str(e):
                self.sk_funcs[str(e)] = e.decl()
                return True
            return False

        if is_var(e):
            return False

        if is_quantifier(e):
            res = self.__has_sk_fun(e.body())
            self.__visited[oid] = res
            return res

        name = e.decl().name()
        
        if name in self.sk_funcs:
            self.__visited[oid] = True
            return True

        if "$!skolem_" in name:
            self.__visited[oid] = True
            self.sk_funcs[name] = e.decl()
            return True

        res = any(self.__has_sk_fun(c) for c in e.children())
        self.__visited[oid] = res
        return res

    def save_state(self, out_file_path):
        handled = dict()
        error_insts = dict()
        sk_funs = []

        for qid, insts in self.insts.items():
            if qid not in self.root_qids:
                error_insts[qid] = (InstError.NON_ROOT, len(insts))
                continue

            qt = self.quants[qid]
            m = SubsMapper(qt)

            if m.unmapped != 0:
                error_insts[qid] = (InstError.UNMAPPED_VARS, len(insts))
                continue

            asserts, skolem = [], False

            self.__visited = dict()
            for inst in insts:
                bindings = m.map_inst(inst)
                skolem |= any(self.__has_sk_fun(b) for b in bindings.values())
                a = qt.rewrite_as_let(bindings)
                asserts.append(a)

            if not skolem:
                handled[qid] = asserts
            else:
                error_insts[qid] = (InstError.SKOLEM_FUNS, len(insts))

        for _, sk_fun in self.sk_funcs.items():
            sk_funs.append(collapse_sexpr(sk_fun.sexpr()))

        pi = ProofInfo(handled, error_insts, sk_funs)

        with open(out_file_path, "wb") as f:
            pickle.dump(pi, f)

    def print_report(self):
        # print("nested quantifiers:")
        # for qid, qt in self.quants.items():
        #     if qt.parent is None:
        #         continue
        #     chain, cur = [qid], qt.parent
        #     while cur is not None:
        #         chain.append(cur)
        #         cur = self.quants[cur].parent
        #     print("\t".join(chain))
        inst_freq = sorted(self.inst_freq.items(), key=lambda x: x[1], reverse=True)

        print("instantiation frequency:")
        for qid, count in inst_freq:
            print(count, qid, end=" ")
            if qid not in self.quants:
                print("(unhandled)")
                continue
            parent = self.quants[qid].parent
            if parent is not None:
                print("(parent:", parent, end=")")
            print("")

