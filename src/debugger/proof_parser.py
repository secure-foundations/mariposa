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
        items = ["(TODO " + self.name]
        for child in self.children:
            items.append(str(child))
        return " ".join(items) + ")"


class LeafNode:
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.value


class ProofNode(TODONode):
    def __init__(self, name, children):
        super().__init__(name, children)


class QuantNode:
    def __init__(self, quant_type, bindings, _body, attrs):
        self.quant_type = quant_type
        self.bindings = bindings
        self._body = _body

        self.attrs = attrs
        self.qid = attrs.get(":qid", None)
        self.skolemid = attrs.get(":skolemid", None)

    def __str__(self):
        return f"(QUANT {self.qid})"

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
        return " ".join(items) + ")"


class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


def parse_attributes(_attrs):
    index = 0
    attrs = dict()
    while index < len(_attrs):
        attr_name = get_symbol(_attrs[index])
        if attr_name in {":pattern"}:
            # TODO: parse pattern if needed
            # attrs[attr_name] = _attrs[index + 1]
            pass
        elif attr_name in {":qid", ":skolemid"}:
            attrs[attr_name] = get_symbol(_attrs[index + 1])
        else:
            print(attr_name)
            assert False
        index += 2
    return attrs


def parse_into_quant_node(items) -> QuantNode:
    assert len(items) == 3
    quant_type, _bindings, _body = get_symbol(items[0]), items[1], items[2]
    assert isinstance(_bindings, list)

    # parse bindings
    bindings = []
    for _binding in _bindings:
        assert isinstance(_binding, list)
        assert len(_binding) == 2
        if _binding[0] == True:
            # this seems to be a bug in the sexp parser
            var = "t"
        else:
            var = get_symbol(_binding[0])
        sort = get_symbol(_binding[1])
        bindings.append((var, sort))

    # parse attributes
    if quant_type != "lambda":
        assert get_symbol(_body[0]) == "!"
        _body, _attrs = _body[1], _body[2:]
        attrs = parse_attributes(_attrs)
    else:
        _body, attrs = _body[1], dict()
    # TODO: parse quant body if needed?
    # body = parse_into_node(_body)
    return QuantNode(quant_type, bindings, _body, attrs)


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
        # assert len(data) == 3
        # TODO: parse quant body
        return parse_into_quant_node(data)

    children = [parse_into_node(c) for c in data[1:]]
    return AppNode(name, children)

class SymbolTable:
    def __init__(self):
        self.table = dict()
        self.__var_prefix = "h!"

    # def process(self, node):
    #     if isinstance(node, LeafNode):
    #         return node

    #     if isinstance(node, LetNode):
    #         for var, val in node.bindings:
    #             self.table[var] = val
    #         return self.process(node.body)

    #     if isinstance(node, AppNode) or isinstance(node, ProofNode):
    #         node.children = [self.process(c) for c in node.children]
    #         return node

    #     return node 

class ProofAnalyzer:
    def __init__(self, data):
        self.__global_defs = dict()

        proof = parse_into_node(data)
        self.proof = self.__rebind_let(proof)

    def add_def(self, name, val):
        if name not in self.__global_defs:
            self.__global_defs[name] = val
            return name
        print("needs rebinding!", name)
        assert False

    def __rebind_let(self, node):
        if isinstance(node, LeafNode):
            return node

        if isinstance(node, LetNode):
            for var, val in node.bindings:
                self.add_def(var, val)
            # we haven't ran into any rebinds yet
            body = self.__rebind_let(node.body)
            # remove the LetNode
            return body

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            node.children = [self.__rebind_let(c) for c in node.children]
            return node

        return node

    def format_node(self, node):
        if isinstance(node, LeafNode):
            value = node.value
            if value in self.__global_defs:
                return self.format_node(self.__global_defs[value])
            return value
        assert not isinstance(node, LetNode)

        if isinstance(node, QuantNode):
            return f"(QUANT {node.quant_type} {node.qid})"

        items = [f"({node.name}"]
        for child in node.children:
            items.append(self.format_node(child))

        return " ".join(items) + ")"

    def print_global_def(self, name):
        node = self.__global_defs[name]
        print(self.format_node(node))

    # def __find_theory_lemmas(self, node):
    #     if isinstance(node, LeafNode):
    #         return []

    #     if isinstance(node, AppNode):
    #         lemmas = []
    #         for child in node.children:
    #             lemmas.extend(self.__find_theory_lemmas(child))
    #         return lemmas

    #     if isinstance(node, ProofNode):
    #         lemmas = []
    #         if node.name == "th-lemma":
    #             lemmas.append(node)
    #         for child in node.children:
    #             lemmas.extend(self.__find_theory_lemmas(child))
    #         return lemmas

    #     return []

    # def find_theory_lemmas(self):
    #     theory_lemmas = []
    #     for node in self.__global_bindings.values():
    #         theory_lemmas.extend(self.__find_theory_lemmas(node))
    #     return theory_lemmas


a = ProofAnalyzer(data)
# lemmas = a.find_theory_lemmas()
# for lemma in lemmas:
#     print(lemma)

a.print_global_def("a!6790")
