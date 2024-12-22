from debugger.proof_parser import *

class SymbolTable:
    def __init__(self):
        self.nodes = dict()
        self._counter = 0

    def process_node(self, node):
        if isinstance(node, LeafNode):
            return
        # if isinstance(node, LetNode):
        #     for var, val in node.bindings:
        #         self.process_node(val)
        #     self.process_node(node.body)
        #     return
        # if isinstance(node, AppNode) or isinstance(node, ProofNode):
        #     for child in node.children:
        #         self.process_node(child)
        #     return
        # assert isinstance(node, QuantNode)
        # self.process_node(node._body)
        # return

class ProofAnalyzer:
    def __init__(self, file_path):
        proof = parse_proof_log(file_path)
        self.__global_defs = dict()
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

        # rebind does happen in quantifiers
        # currently we don't use them ...
        assert isinstance(node, QuantNode)
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

    def __filter_proof_nodes(self, node, name):
        if isinstance(node, LeafNode):
            return []

        if isinstance(node, AppNode):
            nodes = []
            for child in node.children:
                nodes.extend(self.__filter_proof_nodes(child, name))
            return nodes

        if isinstance(node, ProofNode):
            nodes = []
            if node.name == name:
                nodes.append(node)
            for child in node.children:
                nodes.extend(self.__filter_proof_nodes(child, name))
            return nodes

        return []

    def filter_proof_nodes(self, name):
        assert name in PROOF_RULES
        nodes = []
        for node in self.__global_defs.values():
            nodes.extend(self.__filter_proof_nodes(node, name))
        return nodes

proof_file = "dbg/815f69b161/proofs/shuffle.13565831226465156427.proof"
a = ProofAnalyzer(proof_file)
# lemmas = a.filter_proof_nodes("unit-resolution")
