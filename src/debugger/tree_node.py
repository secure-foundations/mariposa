from enum import Enum
from debugger.z3_utils import get_skolem_qname

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

    def __hash__(self):
        return hash(self._index)

    def __eq__(self, other):
        return hash(self) == hash(other)

    def export_symbol(self):
        return f"h!{str(self._index)}"

    def __str__(self):
        return f"@[{self.export_symbol()}]"

    @property
    def index(self):
        return self._index

class QuantRef(NodeRef):
    def __init__(self, index, quant_type: QuantType):
        super().__init__(index)
        assert isinstance(quant_type, QuantType)
        self.__qt = quant_type

    def export_symbol(self):
        return f"{self.__qt.value[0]}!{self._index}"


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
        return get_skolem_qname(self.value)


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
        assert isinstance(self.attrs, list)
        self.qid = None
        self.skolemid = None

        for (k, v) in attrs:
            if k == ":qid":
                self.qid = v
            elif k == ":skolemid":
                self.skolemid = v
            assert isinstance(k, str)
            assert isinstance(v, str)

        if self.qid is None:
            if quant_type == QuantType.LAMBDA:
                self.qid = f"lambda_{QuantNode.lambda_id}"
                QuantNode.lambda_id += 1
            else:
                # unknown quantifier, we drop the body
                self.qid = f"unknown_{QuantNode.unknown_id}"
                QuantNode.unknown_id += 1

    def debug_format_attrs(self):
        res = []
        for (k, v) in self.attrs:
            res += [k + " " + v]
        return " ".join(res)
    
    def debug_format_args(self):
        args = " ".join([f"({var} {sort})" for var, sort in self.args])
        return args

    def debug_format_quant(self):
        attrs = self.debug_format_attrs()
        args = self.debug_format_args()
        body = self.body
        if attrs != "":
            body = f"(! {body} {attrs})"
        return f"({self.quant_type.value} ({args}) {body})"


class LetNode(TreeNode):
    def __init__(self, bindings, body):
        super().__init__()
        self.bindings = bindings
        self.body = body

class AppNode(TreeNode):
    def __init__(self, name, children):
        super().__init__()
        self.name = name
        self.children = children

    def __str__(self):
        return debug_print_node(self)

    def maybe_skolemized(self):
        return get_skolem_qname(self.name)


class DatatypeAppNode(AppNode):
    def __init__(self, name, children):
        name = "(_ is " + name + ")"
        super().__init__(name, children)


class ProofNode(AppNode):
    def __init__(self, name, children):
        super().__init__(name, children)


def debug_print_node(root: TreeNode):
    print(debug_format_node(root))


def debug_format_node(root: TreeNode) -> str:
    stack = [root] 
    result = []

    while stack:
        node = stack.pop()
        if isinstance(node, LeafNode):
            result.append(str(node))
            continue

        if isinstance(node, str):
            result.append(node)
            continue

        if isinstance(node, LetNode):
            stack.append(")")
            stack.append(node.body)
            for var, val in node.bindings:
                stack.append(")")
                stack.append(val)
                stack.append(var)
                stack.append("(")
            stack.append("(let (")
            continue

        if isinstance(node, QuantNode):
            stack.append(node.debug_format_quant())
            continue

        if isinstance(node, AppNode):
            stack.append(")")
            for child in reversed(node.children):
                stack.append(child)
            stack.append("(" + node.name)
            continue

        if isinstance(node, NodeRef):
            result.append(str(node))
            continue

        if isinstance(node, QuantRef):
            result.append(str(node))
            continue

        assert False, f"Unknown node type: {type(node)}"
    result = " ".join(result)
    result = result.replace(" )", ")").replace("( ", "(")
    return result
