from debugger.proof_parser import *

class ProofAnalyzer:
    def __init__(self, file_path):
        root = parse_proof_log(file_path)

        # first get rid of LetNodes
        self.__global_defs = dict()
        root = self.__rebind_let(root)

        # then hash-cons the nodes
        self._hashed = dict()
        self.__replaced = dict()
        self.__ref_counts = dict()

        for name, node in self.__global_defs.items():
            new_node = self.__hash_cons_node(node)
            if new_node.node_id != node.node_id:
                self.__replaced[name] = new_node
        root = self.__hash_cons_node(root)

        self.__check_reachable(root)
        # print(len(self.__ref_counts), len(self.__global_defs))
        sorted_refs = sorted(
            self.__ref_counts.items(), key=lambda x: x[1], reverse=True
        )
        for name, count in sorted_refs:
            print(name, count, self.__global_defs[name])

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

    def __add_node(self, node):
        s_hash = node.shallow_hash()
        if s_hash in self._hashed:
            return self._hashed[s_hash]
        self._hashed[s_hash] = node
        return node

    def __hash_cons_node(self, node):
        assert not isinstance(node, LetNode)

        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__replaced:
                return self.__replaced[symbol]
            return self.__add_node(node)

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            children = [self.__hash_cons_node(child) for child in node.children]
            node.children = children
            return self.__add_node(node)

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

    def __check_undefined_symbols(self, node):
        if isinstance(node, LeafNode):
            symbol = node.value
            if (
                not node.is_int
                and symbol not in self.__global_defs
                and symbol.startswith("a!")
            ):
                print(f"??? undefined symbol: {symbol}")
            return

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            for child in node.children:
                self.__check_undefined_symbols(child)
            return

        assert isinstance(node, QuantNode)
        return

    def check_undefined_symbols(self):
        for node in self.__global_defs.values():
            self.__check_undefined_symbols(node)

    def __check_reachable(self, node):
        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__ref_counts:
                self.__ref_counts[symbol] += 1
                return
            if symbol in self.__global_defs:
                self.__ref_counts[symbol] = 1
                self.__check_reachable(self.__global_defs[node.value])
            return

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            for child in node.children:
                self.__check_reachable(child)
            return

        assert isinstance(node, QuantNode)
        return
