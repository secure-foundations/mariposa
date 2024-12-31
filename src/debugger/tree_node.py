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

    @staticmethod
    def from_str(repr):
        if repr.startswith("@[h!"):
            return NodeRef(int(repr[4:-1]))
        qt = repr[4]
        if qt == "f":
            qt = QuantType.FORALL
        elif qt == "e":
            qt = QuantType.EXISTS
        else:
            assert qt == "l"
            qt = QuantType.LAMBDA
        return QuantRef(int(repr[4:-1]), qt)


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

    @staticmethod
    def from_dict(d):
        if d["cls"] == "leaf_int":
            return LeafIntNode(d["value"])

        if d["cls"] == "leaf":
            return LeafNode(d["value"])
        
        if d["cls"] == "quant":
            body = NodeRef.from_str(d["body"])
            node = QuantNode(d["quant_type"], d["args"], body, d["attrs"])
            node.qid = d["qid"]
            node.skolemid = d["skolemid"]
            return node

        if d["cls"] == "let":
            bindings = [(var, NodeRef.from_str(val)) for var, val in d["bindings"]]
            body = NodeRef.from_str(d["body"])
            return LetNode(bindings, body)

        children = [NodeRef.from_str(child) for child in d["children"]]

        if d["cls"] == "app":
            return AppNode(d["name"], children)

        if d["cls"] == "datatype_app":
            return DatatypeAppNode(d["name"], children)

        assert d["cls"] == "proof"
        return ProofNode(d["name"], children)

    def _load_children(self, children):
        for child in children:
            self.children.append(NodeRef.from_str(child))

class LeafNode(TreeNode):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def __str__(self):
        return self.value

    def to_dict(self):
        assert isinstance(self.value, str)
        return {
            "cls": "leaf",
            "value": self.value,
        }

class LeafIntNode(LeafNode):
    def __init__(self, value):
        super().__init__(value)
        assert isinstance(value, int)

    def __str__(self):
        return str(self.value)

    def to_dict(self):
        return {
            "cls": "leaf_int",
            "value": self.value,
        }

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
        args = {" ".join([f"({var} {sort})" for var, sort in self.args])}
        return f"({self.quant_type.value} ({args}) {self.body})"

    def to_dict(self):
        # assert isinstance(self.body, NodeRef)
        return {
            "cls": "quant",
            "quant_type": self.quant_type.value,
            "args": [(var, sort) for var, sort in self.args],
            # "body": str(self.body),
            "attrs": self.attrs,
            "qid": self.qid,
            "skolemid": self.skolemid,
        }


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

    def to_dict(self):
        bindings = [(var, val.to_dict()) for var, val in self.bindings]
        return {
            "cls": "let",
            "bindings": bindings,
            "body": self.body,
        }

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

    def to_dict(self):
        children = []

        for child in self.children:
            children.append(child)

        cls = "app"

        if isinstance(self, ProofNode):
            cls = "proof"
        elif isinstance(self, DatatypeAppNode):
            cls = "datatype_app"

        return {
            "cls": cls,
            "name": self.name,
            "children": children,
        }

class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


class ProofNode(AppNode):
    def __init__(self, name, children):
        super().__init__(name, children)
