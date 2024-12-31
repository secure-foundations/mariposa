import sexpdata as sexp
from enum import Enum
from functools import partial

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
    unknown_id = 0

    def __init__(self, quant_type, args, body, attrs):
        super().__init__()
        self.quant_type = QuantType(quant_type)
        self.args = args
        self.body = body
        self.attrs = attrs
        self.qid = attrs.get(":qid", None)

        if self.qid is None:
            if quant_type == QuantType.LAMBDA:
                self.qid = f"lambda_{QuantNode.lambda_id}"
                QuantNode.lambda_id += 1
            else:
                self.qid = f"unknown_{QuantNode.unknown_id}"
                QuantNode.unknown_id += 1

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


def set_let_body(node, body):
    assert isinstance(node, LetNode)
    node.body = body


def set_quant_body(node, body):
    assert isinstance(node, QuantNode)
    node.body = body


def add_let_binding(node, var, val):
    assert isinstance(node, LetNode)
    node.bindings.append((var, val))


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


def add_app_child(self, child):
    self.children.append(child)


class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


class ProofNode(AppNode):
    def __init__(self, name, children):
        super().__init__(name, children)


def parse_proof_log(file_path):
    with open(file_path) as f:
        data = sexp.load(f)
    return parse_into_node(data)


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


def parse_into_node(data):
    root = AppNode("root", [])
    tasks = [(data, partial(add_app_child, root))]

    while tasks:
        data, callback = tasks.pop()
        node = __parse_node(data, tasks)
        callback(node)

    return root.children[0]

def __parse_node(data, tasks):
    if isinstance(data, sexp.Symbol):
        return LeafNode(data.value())

    if isinstance(data, int):
        return LeafIntNode(data)

    assert isinstance(data, list)
    assert len(data) > 0

    if node := __parse_datatype_app(data, tasks):
        return node

    name = try_get_symbol(data[0])

    if name is None:
        print(data)
        assert False

    if node := __parse_let(name, data, tasks):
        return node

    if node := __parse_quant(name, data, tasks):
        return node

    if name in PROOF_GRAPH_RULES:
        node = ProofNode(name, [])
    else:
        node = AppNode(name, [])

    for c in reversed(data[1:]):
        tasks.append((c, partial(add_app_child, node)))

    return node

def __parse_datatype_app(data, tasks):
    _name = data[0]
    if not (
        isinstance(_name, list)
        and len(_name) == 3
        and try_get_symbol(_name[0]) == "_"
        and try_get_symbol(_name[1]) == "is"
    ):
        return None

    name = get_symbol(_name[2])
    node = DatatypeAppNode(name, [])

    for c in reversed(data[1:]):
        tasks.append((c, partial(add_app_child, node)))

    return node


def __parse_let(name, data, tasks):
    if name != "let":
        return None
    assert isinstance(data, list)
    assert len(data) == 3
    _bindings, _body = data[1], data[2]
    assert isinstance(_bindings, list)
    node = LetNode([], None)

    for _binding in reversed(_bindings):
        assert isinstance(_binding, list)
        assert len(_binding) == 2
        var = get_symbol(_binding[0])
        cb = partial(add_let_binding, node, var)
        tasks.append((_binding[1], cb))

    cb = partial(set_let_body, node)
    tasks.append((_body, cb))
    return node


def __parse_quant(name, data, tasks):
    if name not in {"forall", "exists", "lambda"}:
        return None

    assert len(data) == 3
    quant_type, _bindings, _body = get_symbol(data[0]), data[1], data[2]
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
        attrs = dict()
    else:
        assert get_symbol(_body[0]) == "!"
        attrs = parse_attributes(_body[2:])
        _body = _body[1]
    node = QuantNode(quant_type, bindings, None, attrs)
    tasks.append((_body, partial(set_quant_body, node)))

    return node
