import sexpdata as sexp
from debugger.tree_node import *
from functools import partial

class ProofParser:
    def __init__(self, file_path):
        self.quant_nodes = set()
        self.root_node = self.__parse_file(file_path)

    def __parse_file(self, file_path):
        temp = AppNode("temp", [])

        with open(file_path) as f:
            data = sexp.load(f)

        cb = partial(cb_add_app_child, temp)
        self.tasks = [(data, cb)]

        while self.tasks:
            data, callback = self.tasks.pop()
            node = self.__parse_node(data)
            callback(node)

        return temp.children[0]

    def __parse_node(self, data):
        if isinstance(data, sexp.Symbol):
            return LeafNode(data.value())

        if isinstance(data, int):
            return LeafIntNode(data)

        assert isinstance(data, list)
        assert len(data) > 0

        if node := self.__parse_datatype_app(data):
            return node
        
        if node := self.__parse_other_apps(data):
            return node

        name = _try_get_symbol(data[0])

        if name is None:
            print(data)
            assert False

        if node := self.__parse_let(name, data):
            return node

        if node := self.__parse_quant(name, data):
            return node

        if name in PROOF_GRAPH_RULES:
            node = ProofNode(name, [])
        else:
            node = AppNode(name, [])

        for c in reversed(data[1:]):
            self.tasks.append((c, partial(cb_add_app_child, node)))

        return node

    def __parse_datatype_app(self, data):
        _name = data[0]
        if not (
            isinstance(_name, list)
            and len(_name) == 3
            and _try_get_symbol(_name[0]) == "_"
            and _try_get_symbol(_name[1]) == "is"
        ):
            return None

        name = _get_symbol(_name[2])
        node = DatatypeAppNode(name, [])

        for c in reversed(data[1:]):
            self.tasks.append((c, partial(cb_add_app_child, node)))

        return node
    
    def __parse_other_apps(self, data):
        _name = data[0]
        if not (
            isinstance(_name, list)
            and _try_get_symbol(_name[0]) == "_"
        ):
            return None

        name = []
        for i in _name:
            if isinstance(i, int):
                name.append(str(i))
            else:
                name.append(_get_symbol(i))

        name = "(" + " ".join(name) + ")"
        node = AppNode(name, [])
        
        for c in reversed(data[1:]):
            self.tasks.append((c, partial(cb_add_app_child, node)))

        return node

    def __parse_let(self, name, data):
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
            var = _get_symbol(_binding[0])
            cb = partial(cb_add_let_binding, node, var)
            self.tasks.append((_binding[1], cb))

        cb = partial(cb_set_let_body, node)
        self.tasks.append((_body, cb))
        return node

    def __parse_quant(self, name, data):
        if name not in {"forall", "exists", "lambda"}:
            return None

        assert len(data) == 3
        q_type, _body = _get_symbol(data[0]), data[2]

        # parse bindings
        bindings = _parse_quant_vars(data[1])

        # parse attributes
        if q_type == "lambda":
            attrs = dict()
        else:
            assert _get_symbol(_body[0]) == "!"
            attrs = _parse_attributes(_body[2:])
            _body = _body[1]
        node = QuantNode(q_type, bindings, attrs)

        self.tasks.append((_body, partial(cb_set_quant_body, node)))
        self.quant_nodes.add(node)

        return node


def _get_symbol(data):
    assert isinstance(data, sexp.Symbol)
    return data.value()


def _get_sort(data):
    if isinstance(data, sexp.Symbol):
        return data.value()
    res = []
    for x in data:
        if isinstance(x, sexp.Symbol):
            res.append(x.value())
        else:
            assert isinstance(x, int)
            res.append(str(x))
    return " ".join(res)


def _try_get_symbol(data):
    if isinstance(data, sexp.Symbol):
        return data.value()
    return None


def _parse_quant_vars(_bindings):
    bindings = []
    for _binding in _bindings:
        assert isinstance(_binding, list)
        assert len(_binding) == 2
        if _binding[0] == True:
            # this seems to be a bug in the sexp parser
            var = "t"
        else:
            var = _get_symbol(_binding[0])
        sort = _get_sort(_binding[1])
        bindings.append((var, sort))
    return bindings


def _parse_attributes(_attrs):
    index = 0
    attrs = dict()
    while index < len(_attrs):
        attr_name = _get_symbol(_attrs[index])
        if attr_name in {":pattern", ":weight", ":no-pattern"}:
            # TODO: parse pattern if needed
            # attrs[attr_name] = _attrs[index + 1]
            pass
        elif attr_name in {":qid", ":skolemid"}:
            attrs[attr_name] = _get_symbol(_attrs[index + 1])
        else:
            print(attr_name)
            assert False
        index += 2
    return attrs


def cb_set_let_body(node, body):
    assert isinstance(node, LetNode)
    node.body = body


def cb_set_quant_body(node, body):
    assert isinstance(node, QuantNode)
    node.body = body


def cb_add_let_binding(node, var, val):
    assert isinstance(node, LetNode)
    node.bindings.append((var, val))


def cb_add_app_child(node, child):
    assert isinstance(node, AppNode)
    node.children.append(child)


def replace_successor(node, old, new):
    found = False
    if isinstance(node, AppNode):
        for i, child in enumerate(node.children):
            if child == old:
                found = True
                node.children[i] = new
    elif isinstance(node, LetNode):
        if node.body == old:
            found = True
            node.body = new
    elif isinstance(node, QuantNode):
        if node.body == old:
            found = True
            node.body = new
    return found
