import sexpdata as sexp

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

class BaseNode:
    global_id = 0
    def __init__(self):
        self.node_id = BaseNode.global_id
        BaseNode.global_id += 1
    
    def __str__(self):
        raise NotImplementedError

    def shallow_hash(self):
        # we don't need to recurse into children
        # since hash-consing is already recursive
        return hash(str(self))

class LeafNode(BaseNode):
    def __init__(self, value, is_int=False):
        super().__init__()
        self.value = value
        self.is_int = is_int

    def __str__(self):
        if self.is_int:
            return str(self.value)
        return self.value


class ProofNode(BaseNode):
    def __init__(self, name, children):
        super().__init__()
        self.name = name
        self.children = children

    def __str__(self):
        items = ["(TODO " + self.name]
        for child in self.children:
            items.append(str(child))
        return " ".join(items) + ")"


class QuantNode(BaseNode):
    def __init__(self, quant_type, bindings, _body, attrs):
        super().__init__()
        self.quant_type = quant_type
        self.bindings = bindings
        self._body = _body

        self.attrs = attrs
        self.qid = attrs.get(":qid", None)
        self.skolemid = attrs.get(":skolemid", None)

    def __str__(self):
        return f"(QUANT {self.qid})"


class LetNode(BaseNode):
    def __init__(self, bindings, body):
        super().__init__()
        self.bindings = bindings
        self.body = body

    def __str__(self):
        items = ["(let"]
        for var, val in self.bindings:
            items.append(f"({var} {val})")
        items.append(str(self.body) + ")")
        return "\n".join(items)


class AppNode(BaseNode):
    def __init__(self, name, children):
        super().__init__()
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
        return LeafNode(data, is_int=True)

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


def parse_proof_log(file_path):
    with open(file_path) as f:
        data = sexp.load(f)
    return parse_into_node(data)
