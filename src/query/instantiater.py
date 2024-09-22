import time
import pickle
from typing import Dict
from base.defs import MARIPOSA
from query.inst_mapper import SubsMapper, Quant, collapse_sexpr
from z3 import *

from utils.system_utils import log_warn, subprocess_run

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

    def get_inst_count(self, qid):
        if qid in self.handled:
            return len(self.handled[qid])
        if qid in self.errors:
            return self.errors[qid][1]
        return 0

    def has_qid(self, qid):
        return qid in self.handled or qid in self.errors

    @staticmethod
    def load(file_path):
        with open(file_path, "rb") as f:
            return pickle.load(f)

class Instantiater:
    def __init__(self, in_file_path):
        self.proc_solver = Solver()
        self.solver_opts = []
        self.proof_time = None
        self.sk_vars = dict()
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

        # map qid to its quant-inst applications
        self.insts = dict()
        self.__visited = set()

        self.inst_freq = dict()

    def __init_qids(self):
        for a in self.proc_solver.assertions():
            self.__load_quantifiers(a, None, a)

        for qid, qtf in self.quants.items():
            if qtf.parent is None:
                self.root_qids.add(qid)

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

    def get_qid_inst_count(self, qid, insts, transitive=True):
        if qid not in self.quants:
            return 0

        count = len(insts[qid]) if qid in insts else 0
        qt = self.quants[qid]

        if not transitive or qt.parent is None:
            return count

        return count + self.get_qid_inst_count(qt.parent, insts, transitive)

    def process(self):
        start = time.time()
        res = self.proc_solver.check()
        self.proof_time = int((time.time() - start) * 1000)

        if res != unsat:
            log_warn("query is not unsat")
            return False

        p = self.proc_solver.proof()
        self.__match_qis(p)
        self.sk_funcs = dict()

        for skid, exprs in self.sk_vars.items():
            if not skid.startswith("skolem_"):
                print("unhandled skid", skid)
                continue

            for expr in exprs:
                self.__find_sk_funs(skid, expr)
        
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

        res = match_sk(p)

        if res is not None:
            skid, sk = res
            self.sk_vars[skid] = self.sk_vars.get(skid, set()) | {sk}

        res = match_qi(p)

        if res is not None:
            qid, qi = res
            self.insts[qid] = self.insts.get(qid, set()) | {qi}

        for c in p.children():
            self.__match_qis(c)

    def __find_sk_funs(self, skid, e):
        if is_const(e) or is_var(e):
            return

        if is_quantifier(e):
            e = e.body()
        
        name = e.decl().name()

        if skid in name:
            if name not in self.sk_funcs:
                self.sk_funcs[name] = e.decl()

        for c in e.children():
            self.__find_sk_funs(skid, c)

    def save_state(self, out_file_path):
        handled = dict()
        error_insts = dict()
        sk_funs = []

        for _, sk_fun in self.sk_funcs.items():
            sk_funs.append(collapse_sexpr(sk_fun.sexpr()))

        for qid, insts in self.insts.items():
            if qid not in self.root_qids:
                error_insts[qid] = ("fail to handle insts of non-root qid", len(insts))
                continue

            qt = self.quants[qid]
            m = SubsMapper(qt)

            if m.unmapped != 0:
                error_insts[qid] = ("fail to handle due to unmapped vars", len(insts))
                continue

            asserts = []

            for inst in insts:
                m.map_inst(inst)
                a = qt.rewrite_as_let(m.var_bindings)
                asserts.append(a)

            handled[qid] = asserts
            
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

    # def save_as_smt2(self, out_file_path, qids):
    #     with open(self.in_file_path, "r") as f:
    #         lines = f.readlines()

    #     insts, replaced_qids = self.replace_insts(qids)

    #     f = open(out_file_path, "w")
    #     last = lines[-2]
    #     for line in lines[:-2]:
    #         should_skip = False
    #         for qid in replaced_qids:
    #             if qid + " " in line:
    #                 should_skip = True
    #                 break
    #         if should_skip:
    #             print("skipping", line, end="")
    #             continue
    #         f.write(line)

    #     for inst in sk_funs + insts:
    #         f.write(inst)
    #         f.write("\n")
    #     f.write(last)
    #     f.write("(check-sat)\n")
    #     f.close()

    #     args = [
    #         MARIPOSA,
    #         "-i",
    #         out_file_path,
    #         "--action=format",
    #         "-o",
    #         out_file_path,
    #     ]

    #     subprocess_run(args, check=True, debug=True)
    