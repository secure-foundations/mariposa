from z3 import *


# def format_expr(e, depth=0, offset=0):
#     if is_const(e):
#         return str(e)

#     if is_var(e):
#         return "qv" + str(get_var_index(e))

#     if is_quantifier(e):
#         if depth == 0:
#             v_count = e.num_vars()
#             vars = [f"qv{str(offset+i)} {e.var_sort(offset+i)}" for i in range(v_count)]
#             vars = "((" + " ".join(vars) + ")) "
#             if e.is_forall():
#                 return (
#                     "(forall "
#                     + vars
#                     + format_expr(e.body(), depth + 1, offset + v_count)
#                     + ")"
#                 )
#             else:
#                 return (
#                     "(exists "
#                     + vars
#                     + format_expr(e.body(), depth + 1, offset + v_count)
#                     + ")"
#                 )

#         return "[QID: " + str(e.qid()) + "]"

#     name = e.decl().name()
#     items = []
#     prefix = " " * (depth + 1)
#     for i in e.children():
#         items += [format_expr(i, depth + 1)]
#     length = sum([len(i) for i in items]) + len(name)
#     if length > 80:
#         items = [prefix + i for i in items]
#         items = "(" + name + "\n" + "\n".join(items) + ")"
#     else:
#         items = "(" + name + " " + " ".join(items) + ")"
#     return items


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
            if r == "True": return "true"
            if r == "False": return "false"
            return r

        if is_var(e):
            idx = offset - get_var_index(e) - 1
            return self.__vars[idx]

        if is_quantifier(e):
            v_count = e.num_vars()
            vars = []

            for i in range(v_count):
                var_name = e.var_name(i)
                self.__vars[offset + i] = var_name
                vars += [f"({var_name} {e.var_sort(i)})"]

            vars = "(" + " ".join(vars) + ") "
            attributes = [f":skolemid {e.skolem_id()}", f":qid {e.qid()}"]

            for i in range(e.num_patterns()):
                assert e.pattern(i).decl().name() == "pattern"
                p = e.pattern(i).children()[0]
                attributes.append(f":pattern ({self._format_expr(p, offset + v_count)})")
        
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


def extract_sk_qid_from_name(name):
    assert "!skolem_" in name
    s = name.find("!skolem_") + len("!skolem_")
    e = name.rfind("!")
    return name[s:e]


def extract_sk_qid_from_decl(sk_fun):
    assert sk_fun.startswith("(declare-fun ")
    sk_fun = sk_fun.split(" ")[1]
    return extract_sk_qid_from_name(sk_fun)


def quote_name(name):
    if "#" in name:
        return f"|{name}|"
    return name


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

    def visited(self):
        return self.__visited
