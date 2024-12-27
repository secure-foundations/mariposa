from debugger.proof_parser import *
import networkx as nx


class ProofAnalyzer:
    def __init__(self, file_path):
        root = parse_proof_log(file_path)

        # hash-cons the nodes
        self.__flattened = dict()
        self.__flatten_tree_nodes(root)

        self.term_graph: nx.DiGraph = nx.DiGraph()
        self.__build_term_graph()

    def __flatten_tree_nodes(self, root: TreeNode):
        self.__global_defs = dict()
        # get rid of let bindings
        # store them in global_defs (temporarily)
        root = self.__rebind_let_rec(root)
        self.__redirected = dict()

        # TODO: this is assuming that global_defs are in topological order
        for name in self.__global_defs:
            node = self.__global_defs[name]
            new_node = self.__hash_cons_node_rec(node)
            new_hash = new_node.hash_id()
            if new_hash not in self.__flattened:
                self.__flattened[new_hash] = new_node
            self.__redirected[name] = new_hash

        root = self.__hash_cons_node_rec(root)
        self.root_id = root.hash_id()
        self.__flattened[self.root_id] = root

        del self.__redirected
        del self.__global_defs

    def __getitem__(self, nid):
        return self.term_graph.nodes()[nid]

    def __add_global_def(self, name, val):
        if name not in self.__global_defs:
            self.__global_defs[name] = val
            return name
        print("needs rebinding!", name)
        assert False

    def __rebind_let_rec(self, node):
        if isinstance(node, LeafNode):
            return node

        if isinstance(node, LetNode):
            for var, val in node.bindings:
                self.__add_global_def(var, val)
            # we haven't ran into any rebinds yet
            body = self.__rebind_let_rec(node.body)
            # remove the LetNode
            return body

        if isinstance(node, AppNode):
            node.children = [self.__rebind_let_rec(c) for c in node.children]
            return node

        # TODO: rebind does happen in quantifiers
        # currently we don't use them ...
        assert isinstance(node, QuantNode)
        return node

    # def __is_flattened(self, node: TreeNode):
    #     if node.hash_id() not in self.__flattened:
    #         return False
    #     if isinstance(node, AppNode):
    #         return all(
    #             isinstance(child, LeafRefNode) and child.value in self.__flattened
    #             for child in node.children
    #         )
    #     return True

    def __add_hash_node(self, node: TreeNode):
        nid = node.hash_id()
        if isinstance(node, AppNode):
            sanity_check = all(
                isinstance(child, LeafRefNode) and child.value in self.__flattened
                for child in node.children
            )
            assert sanity_check
        if nid in self.__flattened:
            return self.__flattened[nid]
        self.__flattened[nid] = node
        return node

    def __hash_cons_node_rec(self, node: TreeNode):
        assert not isinstance(node, LetNode)

        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__global_defs:
                if symbol in self.__redirected:
                    return self.__flattened[self.__redirected[symbol]]
                new_node = self.__hash_cons_node_rec(self.__global_defs[symbol])
                return self.__add_hash_node(new_node)
            return self.__add_hash_node(node)

        if isinstance(node, AppNode):
            children = []
            for child in node.children:
                child = self.__hash_cons_node_rec(child)
                children.append(LeafRefNode(child.hash_id()))
            node.children = children
            return self.__add_hash_node(node)

        assert isinstance(node, QuantNode)
        return node

    def __build_term_graph(self):
        for nid, node in self.__flattened.items():
            assert nid == node.hash_id()
            self.term_graph.add_node(nid, tree_node=node)
            if isinstance(node, LeafNode):
                continue
            if isinstance(node, QuantNode):
                continue
            for child in node.children:
                assert isinstance(child, LeafRefNode)
                assert child.value in self.__flattened
                self.term_graph.add_edge(nid, child.value)

        assert nx.is_directed_acyclic_graph(self.term_graph)
        reachable = nx.descendants(self.term_graph, self.root_id)
        reachable.add(self.root_id)
        assert set(self.__flattened.keys()) == reachable
        del self.__flattened

    def pprint_node(self, nid, indent=0, limit=10):
        assert isinstance(nid, str)
        node = self.term_graph.nodes[nid]["tree_node"]
        prefix = " " * indent

        if isinstance(node, LeafNode):
            assert not isinstance(node, LeafRefNode)
            print(f"{prefix}{str(node.value)}", end="")
            return

        if isinstance(node, QuantNode):
            print(f"{prefix}(QUANT {node.quant_type} {node.qid})", end="")
            return

        print(f"{prefix}({node.name}")
        last = len(node.children) - 1
        for i, child in enumerate(node.children):
            assert isinstance(child, LeafRefNode)
            child_ref_id = child.value
            if limit == 0:
                print(f"{prefix} {child_ref_id}", end="")
            else:
                self.pprint_node(child_ref_id, indent + 1, limit - 1)
            if i != last:
                print("")
        print(f")", end="")

    # def filter_proof_nodes(self, name):
    #     assert name in PROOF_RULES
    #     results = []
    #     for node in self.__flattened.values():
    #         if isinstance(node, ProofNode) and node.name == name:
    #             results.append(node)
    #     return results

    # def __add_proof_successors(self, proof_graph, nid):
    #     queue = [nid]
    #     visited = set()
    #     while queue:
    #         current = queue.pop()
    #         if current in visited:
    #             continue
    #         visited.add(current)
    #         for child_id in self.term_graph.successors(current):
    #             # assert isinstance(child, LeafRefNode)
    #             if proof_graph.has_node(child_id):
    #                 proof_graph.add_edge(nid, child_id)
    #             else:
    #                 queue.append(child_id)

    # def build_proof_graph(self):
    #     graph = nx.DiGraph()
    #     for node in self.__flattened.values():
    #         if isinstance(node, ProofNode):
    #             if node.name in {
    #                 "refl",
    #                 "iff-true",
    #                 "unit-resolution",
    #                 "commutativity",
    #                 "distributivity",
    #                 "symm",
    #                 "mp",
    #                 "mp~",
    #                 "monotonicity",
    #                 "trans",
    #             } and node.hash_id() != self.root.hash_id():
    #                 continue
    #             graph.add_node(node.hash_id(), name=node.name)
    #     for nid in graph.nodes:
    #         self.__add_proof_successors(graph, nid)

    #     reachable = nx.descendants(graph, self.root.hash_id())
    #     reachable.add(self.root.hash_id())
    #     assert set(graph.nodes) == reachable
    #     return graph

    # def __sanity_check_theory_node(self, nid):
    #     if not (isinstance(node, ProofNode) and node.name == "th-lemma"):
    #         return
    #     if len(node.children) != 1:
    #         # TODO
    #         return
    #     self.pprint_node(node.children[0].value)
    #     print("")

    def sanity_check_proof_nodes(self):
        arg_counts = dict()
        for nid, node in self.term_graph.nodes(data="tree_node"):
            if not isinstance(node, ProofNode):
                continue
            name = node.name
            assert name in PROOF_RULES
            if name == "lemma":
                assert len(node.children) == 2
            elif name == "quant-inst":
                assert len(node.children) == 1
            # else:
            #     self.__sanity_check_theory_node(nid)
        #     else:
        #         if name not in arg_counts:
        #             arg_counts[name] = dict()
        #         arg_counts[name][len(node.children)] = (
        #             arg_counts[name].get(len(node.children), 0) + 1
        #         )

        # for name in arg_counts:
        #     print(name)
        #     for arg_count in sorted(arg_counts[name]):
        #         print("\t", arg_count, arg_counts[name][arg_count])
