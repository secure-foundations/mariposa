import re
import time
from z3 import *

from utils.system_utils import log_debug, log_info, log_warn


def quote_name(name):
    if "#" in name or "'" in name:
        if name[0] != "|":
            return f"|{name}|"
        # already quoted
        assert name[-1] == "|"
        return name
    if name == "False":
        return "false"
    return name


def quote_sort(sort):
    ss = str(sort)
    if sort.kind() == Z3_RE_SORT:
        return ss.replace("ReSort(", "(RegEx ")
    return ss


class AstPrinter:
    def __init__(self, parent=None):
        self.__vars = dict()

        if parent is None:
            return

        assert is_quantifier(parent)

        for i in range(parent.num_vars()):
            self.__vars[i] = parent.var_name(i)

    def _format_expr(self, e, offset):
        if is_const(e):
            r = str(e)
            if r == "True":
                return "true"
            if r == "False":
                return "false"
            return quote_name(r)

        if is_var(e):
            idx = offset - get_var_index(e) - 1
            return quote_name(self.__vars[idx])

        if is_quantifier(e):
            v_count = e.num_vars()
            vars = []

            for i in range(v_count):
                var_name = quote_name(e.var_name(i))
                self.__vars[offset + i] = var_name
                vars += [f"({var_name} {quote_sort(e.var_sort(i))})"]

            vars = "(" + " ".join(vars) + ") "
            attributes = [f":skolemid {e.skolem_id()}", f":qid {e.qid()}"]

            for i in range(e.num_patterns()):
                assert e.pattern(i).decl().name() == "pattern"
                p = e.pattern(i).children()[0]
                attributes.append(
                    f":pattern ({self._format_expr(p, offset + v_count)})"
                )

            attributes = " ".join(attributes)
            body = self._format_expr(e.body(), offset + v_count)

            for i in range(v_count):
                del self.__vars[offset + i]

            if e.is_forall():
                return f"(forall {vars} (! {body} {attributes}))"

            return f"(exists {vars} (! {body} {attributes}))"

        if e.decl().kind() == Z3_OP_DT_IS:
            assert e.decl().name() == "is"
            params = e.decl().params()
            assert len(params) == 1
            res = [f"(_ is {quote_name(params[0].name())})"]
        else:
            res = [quote_name(e.decl().name())]

        # name = e.decl().name()
        for i in e.children():
            res += [self._format_expr(i, offset)]
        return "(" + " ".join(res) + ")"


def format_expr_flat(e, body_only=False):
    if body_only:
        p = AstPrinter(e)
        return p._format_expr(e.body(), e.num_vars())
    p = AstPrinter()
    return p._format_expr(e, 0)


def find_matching_brackets(s):
    results = []
    stack = []
    for i, c in enumerate(s):
        if c == "(":
            stack.append(i)
        elif c == ")":
            assert len(stack) != 0
            depth = len(stack)
            results.append((stack.pop(), i + 1, depth))
    assert len(stack) == 0
    results = sorted(results, key=lambda x: x[0])
    return results


def collapse_sexpr(s):
    res, index = "", 0
    s = s.replace("\n", " ")
    while index < len(s):
        c = s[index]
        if c == " ":
            while index < len(s) and s[index] == " ":
                index += 1
        else:
            index += 1
        res += c
    return res


def hack_quantifier_removal(expr, qid):
    expr = collapse_sexpr(expr)
    brackets = find_matching_brackets(expr)
    found, depth = [], -1
    for s, e, d in brackets:
        if hack_contains_qid(expr[s:e], qid) and d > depth:
            depth = d
            found += [(s, e, d)]
    for s, e, d in found:
        if d == depth - 1:
            return expr[:s] + "true" + expr[e:]
    assert False


def hack_contains_qid(line, qid):
    qid = ":qid " + qid
    return qid + " " in line or qid + ")" in line


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

# TODO: this is a hack!
SK_FUN_PAT = re.compile("\!skolem\_([^!]+)\![0-9]+")

def get_skolem_qname(name):
    if m := re.search(SK_FUN_PAT, name):
        return m.group(1)
    return None

class Z3AstVisitor:
    def __init__(self):
        self.__visited = set()

    def __del__(self):
        self.__visited.clear()

    def visit(self, e: ExprRef):
        eid = e.get_id()
        if eid in self.__visited:
            return True
        self.__visited.add(eid)
        return False

    def reset_visit(self):
        self.__visited = set()

    def visited(self):
        return self.__visited

def match_sk_decl_used(e):
    if is_app(e):
        if name := get_skolem_qname(e.decl().name()):
            return (name, e.decl().sexpr())
    return None

def find_sk_decls_used(e):
    res = []
    v = Z3AstVisitor()
    __find_sk_decl_rec(v, e, res)
    return res

def __find_sk_decl_rec(v, e, res):
    if v.visit(e):
        return
    if is_quantifier(e):
        return __find_sk_decl_rec(v, e.body(), res)
    if r := match_sk_decl_used(e):
        res.append(r)
    for c in e.children():
        __find_sk_decl_rec(v, c, res)

def dump_z3_proof(query_path, proof_path) -> bool:
    set_param(proof=True)
    timeout = 60000
    start = time.time()

    solver = Solver()
    solver.set("timeout", timeout)
    solver.from_file(query_path)
    log_debug(f"[proof] z3 version {get_version_string()}")
    log_debug(f"[proof] attempt {query_path}, timeout: {int( timeout/1000)}(s)")

    res = solver.check()
    proof_time = int((time.time() - start))

    if res != unsat:
        log_warn(f"failure [proof] {query_path} result {res}")
        return False
    log_debug(f"[proof] finished in {proof_time}(s) {proof_path}")

    p = solver.proof()

    with open(proof_path, "w+") as f:
        f.write(p.sexpr())

    return True
