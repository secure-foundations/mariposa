from typing import Dict
from debugger.proof_parser import *
import networkx as nx

from utils.system_utils import log_debug


class ProofAnalyzer(nx.DiGraph):
    def __init__(self, file_path):
        super().__init__()
        root = parse_proof_log(file_path)

        # hash-cons the nodes
        self.__build_term_graph(root)

        self.rewrites = []
        self.trivial_rewrite_count = 0
        self.lemmas = []
        self.th_lemmas = []
        self.quant_insts = []
        
        self.__ignored_proofs = dict()
        self.__proof_node_count = 0
        self.__analyze_proof_nodes()

    def debug(self):
        for nid in self.nodes:
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
            new_hash = new_node.hash_index()
            if new_hash not in self.__flattened:
                self.__flattened[new_hash] = new_node
            self.__redirected[name] = new_hash

        root = self.__hash_cons_node_rec(root)
        self.root_id = root.hash_index()
        self.__flattened[self.root_id] = root

        del self.__redirected
        del self.__global_defs

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
        nid = node.hash_index()
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

    def __build_term_graph(self, root: TreeNode):
        self.__flattened: Dict[NodeRef, TreeNode] = dict()
        self.__flatten_tree_nodes(root)

        for cur_index, node in self.__flattened.items():
            assert cur_index == node.hash_index()
            self.add_node(cur_index, tree_node=node)
            if isinstance(node, LeafNode):
                continue
            if isinstance(node, QuantNode):
                continue
            for i, child in enumerate(node.children):
                assert isinstance(child, NodeRef)
                assert child.index in self.__flattened
                self.add_edge(cur_index, child.index, index=i)

        assert nx.is_directed_acyclic_graph(self)
        reachable = nx.descendants(self, self.root_id)
        reachable.add(self.root_id)
        assert set(self.__flattened.keys()) == reachable
        del self.__flattened

    def __pprint_node_rec(self, index, indent, depth):
        assert isinstance(index, str)
        node = self.nodes[index]["tree_node"]
        prefix = "  " * indent

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
        print("")

    # def __add_proof_successors(self, proof_graph, nid):
    #     queue = [nid]
    #     visited = set()
    #     while queue:
    #         current = queue.pop()
    #         if current in visited:
    #             continue
    #         visited.add(current)
    #         for child_id in self.successors(current):
    #             # assert isinstance(child, LeafRefNode)
    #             if proof_graph.has_node(child_id):
    #                 proof_graph.add_edge(nid, child_id)
    #             else:
    #                 queue.append(child_id)

    # def build_proof_graph(self):
    #     graph = nx.DiGraph()
    #     for (index, node) in self.nodes(data="tree_node"):
    #         if isinstance(node, ProofNode) and PROOF_GRAPH_RULES[node.name]:
    #             if self.__is_non_trivial_rewrite(node):
    #                 graph.add_node(index)
    #                 continue
    #             # print(node.name)
    #             assert index == node.hash_id()
    #             graph.add_node(index)

    #     graph.add_node(self.root_id)

    #     for nid in graph.nodes:
    #         self.__add_proof_successors(graph, nid)

    #     reachable = nx.descendants(graph, self.root_id)
    #     reachable.add(self.root_id)
    #     assert set(graph.nodes) == reachable
    #     log_debug(f"{len(graph.nodes)} nodes, {len(graph.edges)} edges")
    #     return graph

    def __analyze_proof_nodes(self):
        for nid, node in self.nodes(data="tree_node"):
            if not isinstance(node, ProofNode):
                continue
            self.__proof_node_count += 1
            name = node.name
            assert name in PROOF_GRAPH_RULES

            if (self.__collect_lemma(nid)
                or self.__collect_rewrite(nid)
                or self.__collect_th_lemma(nid)
                or self.__collect_quant_inst(nid)):
                continue

            if name in {"iff-true", "iff-false", "and-elim", "not-or-elim", "symm", "nnf-pos"}:
                assert len(node.children) == 2
            elif name in {"refl", "asserted", "hypothesis", "commutativity", "def-axiom"}:
                assert len(node.children) == 1
            elif name in {"mp~", "mp", "trans"}:
                assert len(node.children) == 3
            if name not in self.__ignored_proofs:
                self.__ignored_proofs[name] = 0
            self.__ignored_proofs[name] += 1

    def print_stats(self):
        print("total node count:", len(self.nodes))
        print("proof node count:", self.__proof_node_count)
        print("\nhandled proof node count:")
        rewrite_count = len(self.rewrites) + self.trivial_rewrite_count
        print(f"\trewrites (non-trivial): {len(self.rewrites)}/{rewrite_count}")
        print(f"\tlemmas: {len(self.lemmas)}")
        print(f"\tth-lemmas: {len(self.th_lemmas)}")
        print(f"\tquant-insts: {len(self.quant_insts)}")
        print("\nignored proof node count:")
        for name, count in self.__ignored_proofs.items():
            print(f"\t{name}: {count}")

    def get_tree_node(self, nid):
        return self.nodes[nid]["tree_node"]

    def unwrap_single_successor(self, nid):
        successors = list(self.successors(nid))
        assert len(successors) == 1
        cid = successors[0]
        return self.get_tree_node(cid)

    def unwrap_successors(self, nid, expected=None):
        # successors = list(self.successors(nid))
        node = self.get_tree_node(nid)
        successors = []
        for i, child in enumerate(node.children):
            assert isinstance(child, NodeRef)
            successors.append(self.get_tree_node(child.index))
        if expected is not None:
            assert len(successors) == expected
        return successors

    def __collect_rewrite(self, nid) -> bool:
        node = self.get_tree_node(nid)
        if node.name != "rewrite":
            return False
        assert len(node.children) == 1
        eq_node = self.unwrap_single_successor(nid)
        assert isinstance(eq_node, AppNode)
        assert eq_node.name == "="
        left, right = self.unwrap_successors(eq_node.index, 2)
        if left != right:
            self.rewrites.append((left, right))
        else:
            self.trivial_rewrite_count += 1
        return True

    def __collect_lemma(self, nid) -> bool:
        node = self.get_tree_node(nid)
        if node.name != "lemma":
            return False
        left, right = self.unwrap_successors(nid, 2)
        self.lemmas.append((left, right))
        return True

    def __collect_th_lemma(self, nid) -> bool:
        node = self.get_tree_node(nid)
        if node.name != "th-lemma":
            return False
        self.th_lemmas.append(node)
        return True
    
    def __collect_quant_inst(self, nid) -> bool:
        node = self.get_tree_node(nid)
        if node.name != "quant-inst":
            return False
        self.quant_insts.append(node)
        return True