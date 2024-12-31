import networkx as nx
import hashlib
from typing import Dict, Set
from debugger.proof_parser import *


class TermTable(nx.DiGraph):
    def __init__(self, file_path):
        super().__init__()
        root = parse_proof_log(file_path)

        self.__storage: Dict[NodeRef, TreeNode] = dict()

        self.quant_refs: Set[NodeRef] = set()
        self.quant_names: Dict[str, Set[NodeRef]] = dict()

        self.root_ref = self.__flatten_tree_nodes(root)

        self.__build_term_graph()

    # def to_dict(self):
    #     storage = dict()
    #     quant_names = dict()

    #     for ref, node in self.__storage.items():
    #         storage[str(ref)] = node.to_dict()

    #     quant_refs = [str(ref) for ref in self.quant_refs]

    #     for qid, refs in self.quant_names.items():
    #         quant_names[qid] = [str(ref) for ref in refs]

    #     return {
    #         "storage": storage,
    #         "quant_refs": quant_refs,
    #         "quant_names": quant_names,
    #     }

    # @staticmethod
    # def from_dict(d):
    #     tt = TermTable.__new__(TermTable)
    #     storage = dict()
    #     for ref, node in d["storage"].items():
    #         storage[NodeRef.from_str(ref)] = TreeNode.from_dict(node)
    #     tt.__storage = storage
    #     quant_refs = set()
    #     for ref in d["quant_refs"]:
    #         quant_refs.add(NodeRef.from_str(ref))
    #     tt.quant_refs = quant_refs
    #     quant_names = d["quant_names"]
    #     for qid, refs in quant_names.items():
    #         quant_names[qid] = {NodeRef.from_str(ref) for ref in refs}
    #     tt.__build_term_graph()
    #     return tt

    def debug(self):
        for ref in self.nodes:
            if ref in self.quant_refs:
                continue
            print(ref, end=" ")
            self.pprint_node(ref)

        for ref in self.quant_refs:
            print(ref, end=" ")
            self.pprint_node(ref)

    def __flatten_tree_nodes(self, root: TreeNode):
        self.__global_defs = dict()
        # get rid of let bindings
        # store them in global_defs (temporarily)
        root = self.__rebind_let_rec(root)
        self.__redirected = dict()
        # TODO: this is assuming that global_defs are in topological order
        for name, node in self.__global_defs.items():
            node = self.__global_defs[name]
            ref = self.__hash_cons_node_rec(node)
            assert isinstance(ref, NodeRef)
            self.__redirected[name] = ref
        root_ref = self.__hash_cons_node_rec(root)

        del self.__redirected
        del self.__global_defs

        return root_ref

    def __add_global_def(self, name, val):
        if name not in self.__global_defs:
            self.__global_defs[name] = val
            return name
        print("needs rebinding!", name)
        assert False

    def __rebind_let_rec(self, node: TreeNode):
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

    def __make_ref(self, node: TreeNode) -> NodeRef:
        if isinstance(node, AppNode):
            assert all(
                (isinstance(c, NodeRef) and c in self.__storage) for c in node.children
            )
        digest = hashlib.sha1(str(node).encode("utf-8")).hexdigest()
        if isinstance(node, QuantNode):
            return QuantRef(digest[:8], node.quant_type)
        return NodeRef(digest[:8])

    def __hash_node(self, node: TreeNode) -> NodeRef:
        ref = self.__make_ref(node)
        if ref in self.__storage:
            return ref
        if isinstance(node, QuantNode):
            self.__add_quantifier(ref, node)
        self.__storage[ref] = node
        return ref

    def __add_quantifier(self, ref, node: QuantNode):
        if node.quant_type != QuantType.LAMBDA:
            if node.qid not in self.quant_names:
                self.quant_names[node.qid] = set()
            self.quant_names[node.qid].add(ref)
        self.quant_refs.add(ref)

    def __hash_cons_node_rec(self, node: TreeNode) -> NodeRef:
        assert not isinstance(node, LetNode)
        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__global_defs:
                assert symbol in self.__redirected
                # topological order should ensure that any global def is already redirected
                return self.__redirected[symbol]
            else:
                assert symbol not in self.__redirected
        elif isinstance(node, AppNode):
            children = []
            for child in node.children:
                child = self.__hash_cons_node_rec(child)
                assert isinstance(child, NodeRef)
                children.append(child)
            node.children = children
        else:
            assert isinstance(node, QuantNode)
        return self.__hash_node(node)

    def __build_term_graph(self):
        for ref, node in self.__storage.items():
            self.add_node(ref)
            if isinstance(node, LeafNode):
                continue
            if isinstance(node, QuantNode):
                continue
            for _, child in enumerate(node.children):
                assert isinstance(child, NodeRef)
                assert child in self.__storage
                self.add_edge(ref, child)

        assert nx.is_directed_acyclic_graph(self)
        reachable = nx.descendants(self, self.root_ref)
        reachable.add(self.root_ref)
        assert set(self.__storage.keys()) == reachable

    def lookup(self, nor) -> TreeNode:
        if isinstance(nor, str):
            nor = NodeRef(nor)
        if isinstance(nor, NodeRef):
            return self.__storage[nor]
        assert isinstance(nor, TreeNode)
        return nor

    def pprint_node(self, nor, depth=0):
        # terrible argument naming...
        node = self.lookup(nor)
        self.__pprint_node_rec(node, 0, depth)
        print("")

    def __pprint_node_rec(self, node, indent, depth):
        assert isinstance(node, TreeNode)
        prefix = "  " * indent

        if isinstance(node, LeafNode):
            print(f"{prefix}{str(node.value)}", end="")
            return

        if isinstance(node, QuantNode):
            print(f"{prefix}{node}", end="")
            return

        if depth == 0:
            print(f"{prefix}({node.name}", end=" ")
        else:
            print(f"{prefix}({node.name}")

        last = len(node.children) - 1
        for i, child in enumerate(node.children):
            assert isinstance(child, NodeRef)
            if depth == 0:
                print(f"{child}", end="")
            else:
                child = self.__storage[child]
                self.__pprint_node_rec(child, indent + 1, depth - 1)
            if depth == 0:
                if i == last:
                    continue
                print(" ", end="")
            elif i != last:
                print("")
        print(f")", end="")

    def dump_node(self, nor):
        node = self.lookup(nor)
        return self.__dump_node_rec(node)

    def __dump_node_rec(self, node):
        if isinstance(node, LeafNode):
            return f"{node.value}"
        if isinstance(node, QuantNode):
            return str(node)
        children = []
        for child in node.children:
            child = self.lookup(child)
            children.append(self.__dump_node_rec(child))
        return f"({node.name} {' '.join(children)})"

    def resolve_child(self, nor):
        node = self.lookup(nor)
        assert isinstance(node, AppNode)
        assert len(node.children) == 1
        return self.lookup(node.children[0])

    def resolve_children(self, nor, expected=None):
        node = self.lookup(nor)
        successors = []
        for child in node.children:
            assert isinstance(child, NodeRef)
            successors.append(self.lookup(child))
        if expected is not None:
            assert len(successors) == expected
        return successors

    def is_leaf(self, ref, value):
        node = self.lookup(ref)
        if not isinstance(node, LeafNode):
            return False
        return node.value == value

    def is_proof_free(self, ron) -> bool:
        node = self.lookup(ron)
        return self.__is_proof_free_rec(node)

    def __is_proof_free_rec(self, node: TreeNode) -> bool:
        node = self.lookup(node)
        if isinstance(node, ProofNode):
            return False
        if isinstance(node, AppNode):
            return all(self.__is_proof_free_rec(c) for c in node.children)
        return True

    def is_ground(self, ref):
        node = self.lookup(ref)
        return self.__is_ground_rec(node)
    
    def __is_ground_rec(self, node):
        if isinstance(node, LeafNode):
            return True
        if isinstance(node, QuantNode):
            return False
        return all(self.__is_ground_rec(self.lookup(c)) for c in node.children)
