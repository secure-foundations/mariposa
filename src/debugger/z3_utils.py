from z3 import *

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


# TODO: this is a very hacky way to do it
def hack_quantifier_body(quant):
    args = []
    for i in range(quant.num_vars()):
        var = quant.var_name(i)
        if "'" in var or "#" in var:
            var = "|" + var + "|"
        arg = f"({var} {quant.var_sort(i)})"
        if "ReSort(" in arg:
            arg = arg.replace("ReSort(", "(RegEx ")
        args += [arg]
    # sanity check
    quant = collapse_sexpr(quant.sexpr())
    args = " ".join(args)
    expected = "(forall (" + args + ")"
    assert quant.startswith(expected)
    func_body = quant[len(expected) : -1].strip()
    assert func_body.startswith("(!")
    assert func_body.endswith(")")
    brackets = find_matching_brackets(func_body)
    s, e, _ = brackets[1]
    return func_body[s:e].strip(), quant


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


def extract_sk_qid_from_decl(sk_fun):
    assert sk_fun.startswith("(declare-fun ")
    sk_fun = sk_fun.split(" ")[1]
    s = sk_fun.find("$!skolem_") + 9
    e = sk_fun.rfind("!")
    return sk_fun[s:e]


class AstVisitor:
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
