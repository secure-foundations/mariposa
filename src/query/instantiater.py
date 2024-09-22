import time
import pickle
from z3 import *

set_param(proof=True)


def format_expr(e, depth=0, offset=0):
    if is_const(e):
        return str(e)

    if is_var(e):
        return "qv" + str(get_var_index(e))

    if is_quantifier(e):
        if depth == 0:
            v_count = e.num_vars()
            vars = [f"qv{str(offset+i)} {e.var_sort(offset+i)}" for i in range(v_count)]
            vars = "(" + " ".join(vars) + ") "
            if e.is_forall():
                return (
                    "(forall "
                    + vars
                    + format_expr(e.body(), depth + 1, offset + v_count)
                    + ")"
                )
            else:
                return (
                    "(exists "
                    + vars
                    + format_expr(e.body(), depth + 1, offset + v_count)
                    + ")"
                )

        return "[QID: " + str(e.qid()) + "]"

    name = e.decl().name()
    items = []
    prefix = " " * (depth + 1)
    for i in e.children():
        items += [format_expr(i, depth + 1)]
    length = sum([len(i) for i in items]) + len(name)
    if length > 80:
        items = [prefix + i for i in items]
        items = "(" + name + "\n" + "\n".join(items) + ")"
    else:
        items = "(" + name + " " + " ".join(items) + ")"
    return items


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
    assert is_quantifier(l)
    # print(format_expr(r, 0))
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


class SubsMapper:
    def __init__(self, quant):
        self.app_map = dict()
        self.unmapped = 0

        num_vars = quant.num_vars()
        self.find_apps(quant)

        mapped = set()
        self.app_map = {k: v for k, v in self.app_map.items() if v != []}

        for _, idxs in self.app_map.items():
            for idx, _ in idxs:
                mapped.add(idx)

        for i in range(num_vars):
            if i not in mapped:
                self.unmapped += 1

    def find_apps(self, exp):
        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self.find_apps(exp.body())
            return

        fun = exp.decl().name()

        idxs = []

        for i, c in enumerate(exp.children()):
            if not is_var(c):
                continue
            idx = get_var_index(c)
            idxs.append((idx, i))

        if fun in self.app_map:
            idxs_ = self.app_map[fun]
            inconsistent = False
            if len(idxs_) != len(idxs):
                inconsistent = True
            else:
                for i in range(len(idxs)):
                    if idxs[i] != idxs_[i]:
                        inconsistent = True
                        break
            if inconsistent:
                self.app_map[fun] = []
        else:
            self.app_map[fun] = idxs

        for c in exp.children():
            self.find_apps(c)

    def map_inst(self, exp):
        assert self.unmapped == 0
        self.var_bindings = dict()

        # for func, idxs in self.app_map.items():
        #     print(func, idxs)

        self._match_vars(exp)

        for i, v in self.var_bindings.items():
            print(i, v.sexpr())

    def _match_vars(self, exp):
        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self._match_vars(exp.body())
            return

        fun = exp.decl().name()
        
        if fun in self.app_map:
            idxs = self.app_map[fun]
            for i, j in idxs:
                self.var_bindings[i] = exp.children()[j]

        for c in exp.children():
            self._match_vars(c)


class Instantiater:
    def __init__(self, in_file_path):
        self.proc_solver = Solver()
        self.solver_opts = []
        self.proof_time = None
        self.sk_vars = dict()

        self.proc_solver.set("timeout", 60000)

        with open(in_file_path, "r") as f:
            for line in f.readlines():
                if line.startswith("(set-option"):
                    self.solver_opts.append(line)

        self.proc_solver.from_file(in_file_path)

        # map qid to its quantifier
        self.quants = dict()
        # root qids with nested quantifiers
        self.root_qids = set()
        self.__init_qids()

        # map qid to its quant-inst applications
        self.insts = dict()
        self.__visited = set()

        self.inst_freq = dict()

    def __init_qids(self):
        for a in self.proc_solver.assertions():
            self.__load_quantifiers(a)

        referred = set()

        for qid, (_, parent) in self.quants.items():
            if parent is not None:
                referred.add(parent)

            if parent is None and self.quants[qid][1] is None:
                self.root_qids.add(qid)

        self.root_qids = self.root_qids.intersection(referred)

    def __load_quantifiers(self, exp: z3.ExprRef, parent=None):
        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            qid = exp.qid()
            self.quants[qid] = (exp, parent)
            parent = qid

        for c in exp.children():
            self.__load_quantifiers(c, parent)

    def get_qid_inst_count(self, qid, insts, transitive=True):
        if qid not in self.quants:
            return 0

        (_, parent) = self.quants[qid]

        count = 0

        if qid in insts:
            count = len(insts[qid])

        if not transitive or parent is None:
            return count

        return count + self.get_qid_inst_count(parent, insts, transitive)

    def process(self):
        start = time.time()
        res = self.proc_solver.check()
        self.proof_time = int((time.time() - start) * 1000)

        if res != unsat:
            return False

        p = self.proc_solver.proof()
        self.match_qis(p)
        self.inst_freq = dict(map(lambda x: (x[0], len(x[1])), self.insts.items()))

        return True

    def print_report(self):
        print("nested quantifiers:")
        for qid, (_, parent) in self.quants.items():
            if parent is None:
                continue
            chain, cur = [qid], parent
            while cur is not None:
                chain.append(cur)
                _, cur = self.quants[cur]
            print("\t".join(chain))

        inst_freq = sorted(self.inst_freq.items(), key=lambda x: x[1], reverse=True)

        print("instantiation frequency:")
        for qid, count in inst_freq:
            # q = self.quants[qid]
            # qf = is_quantifier_free(q.body())
            print(count, qid, end=" ")
            if qid not in self.quants:
                print("(unhandled)")
                continue
            print("")

        print("skolem variables:")

        for skid in self.sk_vars:
            if not skid.startswith("skolem_"):
                print("unhandled skid", skid)
                continue

            qid = skid[7:]

            if qid not in self.quants:
                print("unhandled skid", qid)
                continue

            print(skid)

    def find_insts(self):
        # for qid in self.root_qids:
        #     qexp = self.quants[qid][0]
        #     m = SubsMapper(qexp)

        for qid, insts in self.insts.items():
            if qid not in self.root_qids:
                continue
            m = SubsMapper(self.quants[qid][0])
            if m.unmapped != 0:
                print("unhandled vars", qid)
                continue
            # for inst in insts:
            #     print(qid)
            #     # print(format_expr(inst))
            #     m.map_inst(inst)
            #     break

    def match_qis(self, p):
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
            self.match_qis(c)

    def save_insts(self, out_file_path):
        insts = dict()

        for qid, inss in self.insts.items():
            # res = [format_expr(i) for i in inss]
            res = [i.sexpr() for i in inss]
            insts[qid] = res

        with open(out_file_path, "wb+") as f:
            pickle.dump(insts, f)
