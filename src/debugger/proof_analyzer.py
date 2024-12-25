from debugger.proof_parser import *
import networkx as nx


class ProofAnalyzer:
    def __init__(self, file_path):
        root = parse_proof_log(file_path)

        # get rid of let bindings
        self.__global_defs = dict()
        root = self.__rebind_let(root)

        # hash-cons the nodes
        self.__flattened = dict()
        self.__redirected = dict()

        # TODO: this is assuming that global_defs are in topological order
        for name in self.__global_defs:
            node = self.__global_defs[name]
            new_node = self.__hash_cons_node(node)
            new_hash = new_node.hash_id()
            if new_hash not in self.__flattened:
                self.__flattened[new_hash] = new_node
            self.__redirected[name] = new_hash

        self.root = self.__hash_cons_node(root)
        self.__flattened[self.root.hash_id()] = self.root

        del self.__redirected
        del self.__global_defs

        self.term_graph: nx.DiGraph = nx.DiGraph()
        self.__build_term_graph()

    def __getitem__(self, nid):
        return self.__flattened[nid]

    def __add_def(self, name, val):
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
                self.__add_def(var, val)
            # we haven't ran into any rebinds yet
            body = self.__rebind_let(node.body)
            # remove the LetNode
            return body

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            node.children = [self.__rebind_let(c) for c in node.children]
            return node

        # TODO: rebind does happen in quantifiers
        # currently we don't use them ...
        assert isinstance(node, QuantNode)
        return node

    def __add_node(self, node: BaseNode):
        nid = node.hash_id()
        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            sanity_check = all(
                isinstance(child, LeafRefNode) and child.value in self.__flattened
                for child in node.children
            )
            assert sanity_check
        if nid in self.__flattened:
            return self.__flattened[nid]
        self.__flattened[nid] = node
        return node

    def __hash_cons_node(self, node):
        assert not isinstance(node, LetNode)

        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__global_defs:
                if symbol in self.__redirected:
                    return self.__flattened[self.__redirected[symbol]]
                new_node = self.__hash_cons_node(self.__global_defs[symbol])
                return self.__add_node(new_node)
            return self.__add_node(node)

        if isinstance(node, AppNode) or isinstance(node, ProofNode):
            children = []
            for child in node.children:
                child = self.__hash_cons_node(child)
                children.append(LeafRefNode(child.hash_id()))
            node.children = children
            return self.__add_node(node)

        assert isinstance(node, QuantNode)
        return node

    def __build_term_graph(self):
        for nid, node in self.__flattened.items():
            assert nid == node.hash_id()
            if isinstance(node, LeafNode):
                continue
            if isinstance(node, QuantNode):
                continue
            for child in node.children:
                assert isinstance(child, LeafRefNode)
                assert child.value in self.__flattened
                self.term_graph.add_edge(nid, child.value)

        assert nx.is_directed_acyclic_graph(self.term_graph)
        reachable = nx.descendants(self.term_graph, self.root.hash_id())
        reachable.add(self.root.hash_id())
        assert set(self.__flattened.keys()) == reachable

    def format_node(self, nid, depth_limit=0):
        if isinstance(nid, LeafRefNode):
            node = self.__flattened[nid.value]
        else:
            assert isinstance(nid, str)
            node = self.__flattened[nid]

        if isinstance(node, LeafNode):
            assert not isinstance(node, LeafRefNode)
            return str(node.value)

        if isinstance(node, QuantNode):
            return f"(QUANT {node.quant_type} {node.qid})"

        items = [f"({node.name}"]
        for child in node.children:
            assert isinstance(child, LeafRefNode)
            child_ref_id = child.value
            if depth_limit == 0:
                items.append(child_ref_id)
            else:
                items.append(self.format_node(child_ref_id, depth_limit - 1))

        return " ".join(items) + ")"

    def filter_proof_nodes(self, name):
        assert name in PROOF_RULES
        results = []
        for node in self.__flattened.values():
            if isinstance(node, ProofNode) and node.name == name:
                results.append(node)
        return results

    def __build_proof_successors(self, nid):
        queue = [nid]
        visited = set()
        successors = set()
        while queue:
            current = queue.pop()
            if current in visited:
                continue
            visited.add(current)
            for child in self.term_graph.successors(current):
                # assert isinstance(child, LeafRefNode)
                child_node = self.__flattened[child]
                if isinstance(child_node, ProofNode):
                    successors.add(child)
                else:
                    queue.append(child)
        return successors

    def build_proof_graph(self):
        graph = nx.DiGraph()
        for node in self.__flattened.values():
            if isinstance(node, ProofNode):
                graph.add_node(node.hash_id(), name=node.name)
        for nid in graph.nodes:
            successors = self.__build_proof_successors(nid)
            for succ in successors:
                graph.add_edge(nid, succ)
            # self.__build_proof_successors(nid)
        return graph

    def sanity_check_proof_nodes(self):
        for node in self.__flattened.values():
            if not isinstance(node, ProofNode):
                continue
            name = node.name
            assert name in PROOF_RULES
            if name == "lemma":
                assert len(node.children) == 2
            elif name == "quant-inst":
                assert len(node.children) == 1
            elif name == "th-lemma":
                print(self.format_node(node.children[-1].value, 10))
                # print(len(node.children))
