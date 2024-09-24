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
        args += [f"({quant.var_name(i)} {quant.var_sort(i)})"]
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
    return func_body[s:e].strip()


def hack_quantifier_removal(expr, qid):
    expr = collapse_sexpr(expr)
    brackets = find_matching_brackets(expr)
    found, depth = [], -1
    for s, e, d in brackets:
        if (qid + " " in expr[s:e] or qid + ")" in expr[s:e]) and d > depth:
            depth = d
            found += [(s, e, d)]
    for (s, e, d) in found:
        if d == depth -1:
            return expr[:s] + "true" + expr[e:]
    assert False

class Quant:
    def __init__(self, quant, parent):
        self.quant: QuantifierRef = quant
        self.parent = parent
        self.assertion = None
        self.qid = quant.qid()
        self.vars = dict()
        self.dbg_fun_name = "dbg_" + quant.qid()
        self.fun_def = None

        if parent is None:
            # hack off the quantifier
            self.__qbody_str = hack_quantifier_body(quant)
        else:
            self.__qbody_str = None

    def is_root(self):
        return self.parent is None

    def rewrite_as_let(self, subs):
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
                    lets.append(f"({e.var_name(idx)} {subs[idx].sexpr()})")
                lets = " ".join(lets)
                lets = f"(let\n({lets}) {self.__qbody_str})"
                return lets
            else:
                return e.sexpr()

        items = [self.__as_let(i, subs) for i in e.children()]
        items = " ".join(items)
        items = "(" + e.decl().name() + " " + items + ")"
        return items


class SubsMapper:
    def __init__(self, qt: Quant):
        self.app_map = dict()
        self.unmapped = 0

        self.num_vars = qt.quant.num_vars()
        self.__visited = set()
        self.__find_apps(qt.quant, 0)
        self.__visited = set()

        mapped = set()
        self.app_map = {k: v for k, v in self.app_map.items() if v != []}

        for _, idxs in self.app_map.items():
            for idx, _ in idxs:
                mapped.add(idx)

        for i in range(self.num_vars):
            if i not in mapped:
                self.unmapped += 1

    def __find_apps(self, exp, offset):
        oid = exp.get_id()
        if oid in self.__visited:
            return
        self.__visited.add(oid)

        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self.__find_apps(exp.body(), offset + exp.num_vars())
            return

        fun, idxs = exp.decl().name(), []

        for i, c in enumerate(exp.children()):
            if not is_var(c):
                continue
            idx = get_var_index(c)
            idx = offset - idx - 1
            if idx >= self.num_vars:
                continue
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
            self.__find_apps(c, offset)

    def _match_vars(self, exp, var_bindings):
        oid = exp.get_id()
        if oid in self.__visited:
            return
        self.__visited.add(oid)

        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self._match_vars(exp.body(), var_bindings)
            return

        fun = exp.decl().name()

        if fun in self.app_map:
            idxs = self.app_map[fun]
            for i, j in idxs:
                var_bindings[i] = exp.children()[j]

        for c in exp.children():
            self._match_vars(c, var_bindings)

    def map_inst(self, exp):
        assert self.unmapped == 0
        self.__visited = set()
        var_bindings = dict()
        self._match_vars(exp, var_bindings)
        return var_bindings
