from enum import Enum
import re

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

# TODO: this is a hack!
SK_FUN_PAT = re.compile("\$\!skolem\_([^!]+)\![0-9]+")

class NodeRef:
    def __init__(self, index):
        self._index = index

    def __str__(self):
        return f"@[h!{self._index}]"

    def __hash__(self):
        return hash(self._index)

    def __eq__(self, other):
        return self._index == other._index


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

    def maybe_skolemized(self):
        return None


class LeafNode(TreeNode):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def __str__(self):
        return self.value

    def maybe_skolemized(self):
        if m := re.search(SK_FUN_PAT, self.value):
            return m.group(1)
        return None


class LeafIntNode(LeafNode):
    def __init__(self, value):
        super().__init__(value)
        assert isinstance(value, int)

    def __str__(self):
        return str(self.value)

    def maybe_skolemized(self):
        return None


class QuantNode(TreeNode):
    lambda_id = 0
    unknown_id = 0

    def __init__(self, quant_type, args, attrs):
        super().__init__()
        self.quant_type = QuantType(quant_type)
        self.args = args
        self.body = None
        self.attrs = attrs
        self.qid = attrs.get(":qid", None)

        # let bindings within the quantifier body

        if self.qid is None:
            if quant_type == QuantType.LAMBDA:
                self.qid = f"lambda_{QuantNode.lambda_id}"
                QuantNode.lambda_id += 1
            else:
                self.qid = f"unknown_{QuantNode.unknown_id}"
                QuantNode.unknown_id += 1
        self.skolemid = attrs.get(":skolemid", None)

    def __str__(self):
        args = " ".join([f"({var} {sort})" for var, sort in self.args])
        return f"({self.quant_type.value} ({args}) {self.body})"

    # def remove_let(self):
    #     self.body = self.__remove_let(self.body)
    #     assert self.__local_binds == dict()

    # def __remove_let(self, node) -> TreeNode:
    #     if isinstance(node, LeafNode):
    #         if node.maybe_temp():
    #             assert node.value in self.__local_binds
    #             return node
    #         return node

    #     if isinstance(node, QuantNode):
    #         assert node.body is not None
    #         return node

    #     if isinstance(node, LetNode):
    #         for var, val in node.bindings:
    #             assert var not in self.__local_binds
    #             assert var not in self.local_defs
    #             val = self.__remove_let(val)
    #             self.local_defs[var] = val
    #             self.__local_binds[var] = val
    #         result = self.__remove_let(node.body)
    #         for var, _ in node.bindings:
    #             # we don't pop the local defs
    #             del self.__local_binds[var]
    #         return result

    #     assert isinstance(node, AppNode)
    #     node.children = [self.__remove_let(c) for c in node.children]
    #     return node


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

    def maybe_skolemized(self):
        if m := re.search(SK_FUN_PAT, self.name):
            return m.group(1)
        return None


class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


class ProofNode(AppNode):
    def __init__(self, name, children):
        super().__init__(name, children)
