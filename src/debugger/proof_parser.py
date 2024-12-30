import sexpdata as sexp
from enum import Enum

PROOF_GRAPH_RULES = {
    "true": False,
    "der": False,
    "asserted": False,
    "quant-inst": True,
    "goal": False,
    "hypothesis": False,
    "mp": False,
    "mp~": False,
    "lemma": True,
    "unit-resolution": False,
    "refl": False,
    "iff-true": False,
    "symm": False,
    "iff-false": False,
    "trans": False,
    "trans*": False,
    "commutativity": False,
    "monotonicity": False,
    "def-axiom": False,
    "quant-intro": False,
    "def-intro": False,
    "distributivity": False,
    "apply-def": False,
    "and-elim": False,
    "iff~": False,
    "not-or-elim": False,
    "nnf-pos": False,
    "rewrite": True,
    "nnf-neg": False,
    "pull-quant": False,
    "sk": True,
    "push-quant": False,
    "elim-unused-vars": False,
    "th-lemma": True,
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

class QuantType(Enum):
    FORALL = "forall"
    EXISTS = "exists"
    LAMBDA = "lambda"

class NodeRef:
    def __init__(self, index):
        self._index = index

    def __str__(self):
        return f"@[h!{self._index}]"

    def __hash__(self):
        return hash(self._index)

    def __eq__(self, other):
        return self._index == other._index
    
    def index(self):
        return self._index

class QuantRef(NodeRef):
    def __init__(self, index, quant_type: QuantType):
        super().__init__(index)
        assert isinstance(quant_type, QuantType)
        self.__qt = quant_type

    def __str__(self):
        return f"@[{self.__qt.value[0]}!{self._index}]"

class TreeNode:
    # global_id = 0
    def __init__(self):
        pass
        # self.id = TreeNode.global_id
        # TreeNode.global_id += 1

    def __str__(self):
        raise NotImplementedError


class LeafNode(TreeNode):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def __str__(self):
        return self.value


class LeafIntNode(LeafNode):
    def __init__(self, value):
        super().__init__(value)

    def __str__(self):
        return str(self.value)


class QuantNode(TreeNode):
    lambda_id = 0

    def __init__(self, quant_type, args, body, attrs):
        super().__init__()
        assert isinstance(quant_type, QuantType)
        self.quant_type = quant_type
        self.args = args
        self.body = body
        self.attrs = attrs
        self.qid = attrs.get(":qid", None)
        if self.qid is None:
            assert quant_type == QuantType.LAMBDA
            self.qid = f"lambda_{QuantNode.lambda_id}"
            QuantNode.lambda_id += 1
        self.skolemid = attrs.get(":skolemid", None)

    def __str__(self):
        return f"({self.quant_type.value} ({' '.join([f'({var} {sort})' for var, sort in self.args])}) {self.body})"


class LetNode(TreeNode):
    def __init__(self, bindings, body):
        super().__init__()
        self.bindings = bindings
        self.body = body

    def __str__(self):
        items = ["(let"]
        for var, val in self.bindings:
            items.append(f"({var} {val})")
        items.append(str(self.body) + ")")
        return " ".join(items)


class AppNode(TreeNode):
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


class ProofNode(AppNode):
    def __init__(self, name, children):
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
    if quant_type == "lambda":
        body, attrs = parse_into_node(_body), dict()
    else:
        assert get_symbol(_body[0]) == "!"
        attrs = parse_attributes(_body[2:])
        body = parse_into_node(_body[1])
    qt = QuantType(quant_type)
    return QuantNode(qt, bindings, body, attrs)


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
        return LeafIntNode(data)

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

    if name in PROOF_GRAPH_RULES:
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
