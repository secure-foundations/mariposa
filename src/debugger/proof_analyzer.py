from typing import Dict
from debugger.proof_parser import *
import networkx as nx


class ProofAnalyzer:
    def __init__(self, file_path):
        root = parse_proof_log(file_path)

        # hash-cons the nodes
        self.__flattened: Dict[NodeRef, TreeNode] = dict()
        self.__flatten_tree_nodes(root)

        self.term_graph: nx.DiGraph = nx.DiGraph()
        self.__build_term_graph()

    def debug(self):
        for nid in self.term_graph.nodes:
            print(nid, end=" ")
            self.pprint_node(nid)
            print("")

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
            assert not isinstance(new_node, NodeRef)
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

    def __add_hash_node(self, node: TreeNode) -> TreeNode:
        nid = node.hash_id()
        if nid in self.__flattened:
            return self.__flattened[nid]
        self.__flattened[nid] = node
        return node

    def __hash_cons_node_rec(self, node: TreeNode):
        assert not isinstance(node, LetNode)

        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__global_defs:
                assert symbol in self.__redirected
                # topological order should ensure that any global def is already redirected
                return self.__flattened[self.__redirected[symbol]]
            else:
                assert symbol not in self.__redirected
            return self.__add_hash_node(node)

        if isinstance(node, AppNode):
            children = []
            for child in node.children:
                child = self.__hash_cons_node_rec(child)
                assert not isinstance(child, NodeRef)
                children.append(child.make_ref())
            node.children = children
            return self.__add_hash_node(node)

        assert isinstance(node, QuantNode)
        return node

    def __build_term_graph(self):
        for cur_index, node in self.__flattened.items():
            assert cur_index == node.hash_id()
            self.term_graph.add_node(cur_index, tree_node=node)
            if isinstance(node, LeafNode):
                continue
            if isinstance(node, QuantNode):
                continue
            for child in node.children:
                assert isinstance(child, NodeRef)
                assert child.index in self.__flattened
                self.term_graph.add_edge(cur_index, child.index)

        assert nx.is_directed_acyclic_graph(self.term_graph)
        reachable = nx.descendants(self.term_graph, self.root_id)
        reachable.add(self.root_id)
        assert set(self.__flattened.keys()) == reachable
        del self.__flattened

    def __pprint_node_rec(self, index, indent, depth):
        assert isinstance(index, str)
        node = self.term_graph.nodes[index]["tree_node"]
        prefix = " " * indent

        if isinstance(node, LeafNode):
            print(f"{prefix}{str(node.value)}", end="")
            return

        if isinstance(node, QuantNode):
            print(f"{prefix}(QUANT {node.quant_type} {node.qid})", end="")
            return

        if depth == 0:
            print(f"{prefix}({node.name}", end=" ")
        else:
            print(f"{prefix}({node.name}")

        last = len(node.children) - 1
        for i, child in enumerate(node.children):
            assert isinstance(child, NodeRef)
            if depth == 0:
                print(f"{child.index}", end="")
            else:
                self.__pprint_node_rec(child.index, indent + 1, depth - 1)
            if depth == 0:
                if i == last: continue
                print(" ", end="")
            elif i != last:
                print("")
        print(f")", end="")

    def pprint_node(self, index, depth=0):
        self.__pprint_node_rec(index, 0, depth)

    # def filter_proof_nodes(self, name):
    #     assert name in PROOF_RULES
    #     results = []
    #     for node in self.term_graph.nodes(data="tree_node"):
    #         if isinstance(node, ProofNode) and node.name == name:
    #             results.append(node)
    #     return results

    def __add_proof_successors(self, proof_graph, nid):
        queue = [nid]
        visited = set()
        while queue:
            current = queue.pop()
            if current in visited:
                continue
            visited.add(current)
            for child_id in self.term_graph.successors(current):
                # assert isinstance(child, LeafRefNode)
                if proof_graph.has_node(child_id):
                    proof_graph.add_edge(nid, child_id)
                else:
                    queue.append(child_id)

    def build_proof_graph(self):
        graph = nx.DiGraph()
        for (index, node) in self.term_graph.nodes(data="tree_node"):
            if isinstance(node, ProofNode):
                if node.name in {
                    "refl",
                    "iff-true",
                    "unit-resolution",
                    "commutativity",
                    "distributivity",
                    "symm",
                    "mp",
                    "mp~",
                    "monotonicity",
                    "trans",
                }:
                    continue
                assert index == node.hash_id()
                graph.add_node(index)

        graph.add_node(self.root_id)

        for nid in graph.nodes:
            self.__add_proof_successors(graph, nid)

        reachable = nx.descendants(graph, self.root_id)
        reachable.add(self.root_id)
        assert set(graph.nodes) == reachable

        # for nid in graph.nodes:
        #     print(nid, end=" ")
        #     self.pprint_node(nid)
        #     print("")

        return graph

    def __sanity_check_theory_node(self, node: ProofNode):
        if not (isinstance(node, ProofNode) and node.name == "th-lemma"):
            return
        if len(node.children) != 1:
            # TODO
            return
        # self.pprint_node(node.children[0].index, 100)
        # print("")

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
            else:
                self.__sanity_check_theory_node(node)
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
