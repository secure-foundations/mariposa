import sexpdata as sexp

proof_file = "dbg/815f69b161/proofs/shuffle.13565831226465156427.proof"

with open(proof_file) as f:
    data = sexp.load(f)

PROOF_RULES = {
    "true",
    "der",
    "asserted",
    "quant-inst",
    "goal",
    "hypothesis",
    "mp",
    "mp~",
    "lemma",
    "unit-resolution",
    "refl",
    "iff-true",
    "symm",
    "iff-false",
    "trans",
    "commutativity",
    "monotonicity",
    "def-axiom",
    "quant-intro",
    "def-intro",
    "distributivity",
    "apply-def",
    "and-elim",
    "iff~",
    "not-or-elim",
    "nnf-pos",
    "rewrite",
    "nnf-neg",
    "pull-quant",
    "sk",
    "push-quant",
    "elim-unused-vars",
    "th-lemma",
}

Z3_BUILTIN = {
    "and",
    "or",
    "not",
    "=>",
    "ite",
    "=",
    "+",
    "-",
    "*",
    ">=",
    "<=",
    "<",
    ">",
    "~",
    "false",
}


def get_symbol(data):
    assert isinstance(data, sexp.Symbol)
    return data.value()


def try_get_symbol(data):
    if isinstance(data, sexp.Symbol):
        return data.value()
    return None


class TODONode:
    def __init__(self, name, children):
        self.name = name
        self.children = children

    def __str__(self):
        return f"(TODO {self.name})"


class LeafNode:
    def __init__(self, value):
        self.value = value
    
    def __str__(self):
        return self.value


class ProofNode(TODONode):
    def __init__(self, name, children):
        super().__init__(name, children)


class QuantNode(TODONode):
    def __init__(self, name, children):
        super().__init__(name, children)


class LetNode:
    def __init__(self, bindings, body):
        self.bindings = bindings
        self.body = body

    def __str__(self):
        items = ["(let"]
        for var, val in self.bindings:
            items.append(f"({var} {val})")
        items.append(str(self.body) + ")")
        return "\n".join(items)


class AppNode:
    def __init__(self, name, children):
        self.name = name
        self.children = children

    def __str__(self):
        items = [f"({self.name}"]
        for child in self.children:
            items.append(str(child))
        items.append(")")
        return " ".join(items)


class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


def parse_quant_bindings(bindings):
    assert isinstance(bindings, list)
    result = []
    # print(bindings)
    for binding in bindings:
        assert isinstance(binding, list)
        assert len(binding) == 2
        if binding[0] == True:
            # this seems to be a bug in the sexp parser
            var = "t"
        else:
            var = get_symbol(binding[0])
        sort = get_symbol(binding[1])
        result.append((var, sort))
    return result


def parse_into_let_node(items) -> LetNode:
    assert isinstance(items, list)
    assert len(items) == 3
    _bindings, _body = items[1], items[2]
    assert isinstance(_bindings, list)
    bindings = []
    for _binding in _bindings:
        assert isinstance(_binding, list)
        assert len(_binding) == 2
        var = get_symbol(_binding[0])
        val = parse_into_node(_binding[1])
        bindings.append((var, val))
    body = parse_into_node(_body)
    return LetNode(bindings, body)


def try_parse_into_datatype_node(items) -> DatatypeAppNode:
    _name = items[0]
    if (
        not isinstance(_name, list)
        or len(_name) != 3
        or try_get_symbol(_name[0]) != "_"
        or try_get_symbol(_name[1]) != "is"
    ):
        return None
    name = get_symbol(_name[2])
    params = [parse_into_node(c) for c in items[1:]]
    return DatatypeAppNode(name, params)

def parse_into_node(data):
    if isinstance(data, sexp.Symbol):
        return LeafNode(data.value())
    if isinstance(data, int):
        return LeafNode(str(data))

    assert isinstance(data, list)
    assert len(data) > 0

    node = try_parse_into_datatype_node(data)

    if node is not None:
        return node

    name = try_get_symbol(data[0])

    if name is None:
        print(data)
        assert False

    if name == "let":
        return parse_into_let_node(data)

    if name in PROOF_RULES:
        children = [parse_into_node(c) for c in data[1:]]
        return ProofNode(name, children)

    if name == "forall" or name == "exists" or name == "lambda":
        assert len(data) == 3
        # TODO: parse quant body
        return QuantNode(name, data[1:])

    children = [parse_into_node(c) for c in data[1:]]
    return AppNode(name, children)


class ProofAnalyzer:
    def __init__(self, data):
        self.proof = parse_into_node(data)
        self.__global_bindings = dict()
        self.__local_bindings = dict()
        self.__realloc_stack = dict()
        self.proof = self.__rebind_let(self.proof)
        print(self.proof)

    def add_local_binding(self, name, val):
        if name not in self.__local_bindings:
            self.__local_bindings[name] = val
            self.__global_bindings[name] = val
            return name
        print("needs rebinding!", name)
        assert False

    def remove_local_binding(self, name):
        assert name in self.__local_bindings
        del self.__local_bindings[name]

    def __rebind_let(self, node):
        if isinstance(node, LeafNode):
            return node

        if isinstance(node, LetNode):
            for var, val in node.bindings:
                self.add_local_binding(var, val)

            body = self.__rebind_let(node.body)

            for var, _ in node.bindings:
                self.remove_local_binding(var)

            return body

        if isinstance(node, AppNode):
            node.children = [self.__rebind_let(c) for c in node.children]
            return node

        if isinstance(node, ProofNode):
            node.children = [self.__rebind_let(c) for c in node.children]
            return node

        print("NYI for", node)
        return node

ProofAnalyzer(data)
