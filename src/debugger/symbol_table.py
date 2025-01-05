import networkx as nx
import hashlib
from typing import Dict, Set
from debugger.tree_parser import *
from utils.system_utils import log_debug


class TermTable(nx.DiGraph):
    def __init__(self, file_path):
        super().__init__()
        parser = ProofParser(file_path)

        self.__storage: Dict[NodeRef, TreeNode] = dict()
        self.quant_refs: Set[NodeRef] = set()
        self.quant_names: Dict[str, Set[NodeRef]] = dict()

        self.__redirected_quant_nodes = dict()
        self.__collect_quants(parser.quant_nodes)
        self.root_ref = self.__flatten_tree_nodes(parser.root_node)

        self.__build_term_graph()

        # these nodes are skolemized
        self.skolem_refs: Dict[NodeRef, str] = dict()
        self.__identify_skolem()

    def debug(self):
        for ref in self.__storage:
            if ref in self.quant_refs:
                continue
            print(ref, end=" ")
            self.pprint_node(ref)

        for ref in self.quant_refs:
            node = self.__storage[ref]
            print(ref, node.qid, end=" ")
            self.pprint_node(ref)

    def __collect_quants(self, quant_nodes):
        def __collect_quants_rec(node):
            if isinstance(node, QuantNode):
                if node in self.__redirected_quant_nodes:
                    return self.__redirected_quant_nodes[node]
                node.body = __collect_quants_rec(node.body)
                ref = self.__add_tree_node(node)
                self.__redirected_quant_nodes[node] = ref
                return ref

            if isinstance(node, AppNode):
                for i, child in enumerate(node.children):
                    node.children[i] = __collect_quants_rec(child)

            elif isinstance(node, LetNode):
                for i, (k, v) in enumerate(node.bindings):
                    node.bindings[i] = (k, __collect_quants_rec(v))
                node.body = __collect_quants_rec(node.body)

            return node

        for node in quant_nodes:
            __collect_quants_rec(node)

    def add_tree_node(self, node: TreeNode) -> NodeRef:
        assert not isinstance(node, QuantNode)
        assert isinstance(node, TreeNode)
        return self.__add_tree_node(node)

    def __add_tree_node(self, node: TreeNode) -> NodeRef:
        ref = self.__make_ref(node)
        if ref in self.__storage:
            return ref
        if isinstance(node, QuantNode):
            if node.quant_type != QuantType.LAMBDA:
                if node.qid not in self.quant_names:
                    self.quant_names[node.qid] = set()
                self.quant_names[node.qid].add(ref)
            self.quant_refs.add(ref)           
        self.__storage[ref] = node
        return ref

    def __make_ref(self, node: TreeNode) -> NodeRef:
        assert isinstance(node, TreeNode)
        if isinstance(node, AppNode):
            assert all(
                (isinstance(c, NodeRef) and c in self.__storage) for c in node.children
            )
        digest = hashlib.sha1(str(node).encode("utf-8")).hexdigest()
        if isinstance(node, QuantNode):
            return QuantRef(digest[:8], node.quant_type)
        return NodeRef(digest[:8])

    def __flatten_tree_nodes(self, root: TreeNode):
        self.__global_defs = dict()
        # get rid of let bindings
        # store them in global_defs (temporarily)
        root = self.__rebind_let_rec(root)

        self.__redirected_globals = dict()
        # TODO: this is assuming that global_defs are in topological order
        for name, node in self.__global_defs.items():
            node = self.__global_defs[name]
            ref = self.__hash_cons_node_rec(node)
            assert isinstance(ref, NodeRef)
            self.__redirected_globals[name] = ref

        root_ref = self.__hash_cons_node_rec(root)

        del self.__redirected_globals
        del self.__global_defs

        return root_ref

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

        assert isinstance(node, QuantNode)
        assert node in self.__redirected_quant_nodes
        return node

    def __add_global_def(self, name, val):
        if name not in self.__global_defs:
            self.__global_defs[name] = val
            return name
        print("needs rebinding!", name)
        assert False

    def __hash_cons_node_rec(self, node: TreeNode) -> NodeRef:
        assert not isinstance(node, LetNode)
        if isinstance(node, LeafNode):
            symbol = node.value
            if symbol in self.__global_defs:
                assert symbol in self.__redirected_globals
                # topological order should ensure that any global def is already redirected
                return self.__redirected_globals[symbol]
            else:
                assert symbol not in self.__redirected_globals
        elif isinstance(node, AppNode):
            children = []
            for child in node.children:
                child = self.__hash_cons_node_rec(child)
                assert isinstance(child, NodeRef)
                children.append(child)
            node.children = children
        else:
            assert isinstance(node, QuantNode)
            return self.__redirected_quant_nodes[node]
        return self.__add_tree_node(node)

    def __build_term_graph(self):
        for ref, node in self.__storage.items():
            assert ref == self.__make_ref(node)
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
        unreachable = set(self.__storage) - reachable

        # for ref in unreachable:
        #     print(ref, self.in_degree(ref), self.out_degree(ref))
        #     self.pprint_node(ref, 3)

        log_debug(f"[term graph] {len(self)} nodes, {len(self.edges)} edges, root {self.root_ref}")
        log_debug(f"{len(unreachable)} nodes are unreachable!")

    def lookup_node(self, nor) -> TreeNode:
        if isinstance(nor, str):
            nor = NodeRef(nor)
        if isinstance(nor, NodeRef):
            return self.__storage[nor]
        assert isinstance(nor, TreeNode)
        return nor

    def pprint_node(self, nor, depth=0):
        # terrible argument naming...
        node = self.lookup_node(nor)
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
        node = self.lookup_node(nor)
        return self.__dump_node_rec(node)

    def __dump_node_rec(self, node):
        if isinstance(node, LeafNode):
            return f"{node.value}"
        if isinstance(node, QuantNode):
            return str(node)
        children = []
        for child in node.children:
            child = self.lookup_node(child)
            children.append(self.__dump_node_rec(child))
        return f"({node.name} {' '.join(children)})"

    def resolve_child(self, nor):
        node = self.lookup_node(nor)
        assert isinstance(node, AppNode)
        assert len(node.children) == 1
        return self.lookup_node(node.children[0])

    def resolve_children(self, nor, expected=None):
        node = self.lookup_node(nor)
        successors = []
        for child in node.children:
            assert isinstance(child, NodeRef)
            successors.append(self.lookup_node(child))
        if expected is not None:
            assert len(successors) == expected
        return successors

    def is_leaf(self, ref, value):
        node = self.lookup_node(ref)
        if not isinstance(node, LeafNode):
            return False
        return node.value == value

    def is_proof_free(self, ron) -> bool:
        refs = [self.__make_ref(self.lookup_node(ron))]
        while refs:
            node = self.lookup_node(refs.pop())
            if isinstance(node, ProofNode):
                return False
            if isinstance(node, AppNode):
                refs.extend(node.children)
        return True

    def is_ground(self, ron):
        refs = [self.__make_ref(self.lookup_node(ron))]
        while refs:
            node = self.lookup_node(refs.pop())
            if isinstance(node, QuantNode):
                return False
            if isinstance(node, ProofNode):
                return False
            if isinstance(node, AppNode):
                refs.extend(node.children)
        return True

    def __identify_skolem(self):
        for ref, node in self.__storage.items():
            assert isinstance(node, TreeNode)
            if name := node.maybe_skolemized():
                assert name in self.quant_names
                self.skolem_refs[ref] = name

    def get_skolem_deps(self, ron) -> Set[NodeRef]:
        refs = [self.__make_ref(self.lookup_node(ron))]
        deps = set()
        while refs:
            ref = refs.pop()
            node = self.lookup_node(ref)
            if isinstance(node, AppNode):
                refs.extend(node.children)
            if ref in self.skolem_refs:
                deps.add(ref)
        return deps
