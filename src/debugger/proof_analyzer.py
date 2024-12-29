from typing import Dict
import networkx as nx
from debugger.proof_parser import *
from debugger.symbol_table import TermTable
from utils.system_utils import log_debug

class ProofTerm:
    def __init__(self, rule_name, assumptions, conclusion):
        self.rule_name = rule_name
        self.assumptions = assumptions
        self.conclusion = conclusion


class LemmaTerm(ProofTerm):
    def __init__(self, assumptions, conclusion):
        super().__init__("lemma", assumptions, conclusion)


class RewriteTerm:
    def __init__(self, left, right):
        assert left != right
        self.left = left
        self.right = right


class ProofAnalyzer(TermTable):
    def __init__(self, file_path):
        super().__init__(file_path)

        self.rewrites = dict()
        self.trivial_rewrites = set()
        self.lemmas = []
        self.th_lemmas = []
        self.quant_insts = []

        self.__ignored_proof_stats = dict()
        self.__proof_node_count = 0

        self.proof_graph = nx.DiGraph()
        self.__analyze_proof_nodes()

    def __add_proof_successors(self, proof_graph, ref):
        queue = [ref]
        visited = set()

        while queue:
            current = queue.pop()
            if current in visited:
                continue
            visited.add(current)
            for child_id in self.successors(current):
                # assert isinstance(child, LeafRefNode)
                if proof_graph.has_node(child_id):
                    proof_graph.add_edge(ref, child_id)
                else:
                    queue.append(child_id)

    def __analyze_proof_nodes(self):
        for ref in self.nodes():
            node = self.lookup(ref)
            if not isinstance(node, ProofNode):
                continue
            self.__proof_node_count += 1
            name = node.name
            assert name in PROOF_GRAPH_RULES

            conclusion = node.children[-1]

            if not self.is_proof_free(conclusion):
                print("proof node conclusion is not grounded?:")
                self.pprint_node(ref, 1)
                assert False

            if (
                self.__collect_lemma(ref)
                or self.__collect_rewrite(ref)
                or self.__collect_th_lemma(ref)
                or self.__collect_quant_inst(ref)
            ):
                if ref not in self.trivial_rewrites:
                    self.proof_graph.add_node(ref)
                continue

            if name in {
                "iff-true",
                "iff-false",
                "and-elim",
                "not-or-elim",
                "symm",
                "nnf-pos",
            }:
                assert len(node.children) == 2
            elif name in {
                "refl",
                "asserted",
                "hypothesis",
                "commutativity",
                "def-axiom",
            }:
                assert len(node.children) == 1
            elif name in {"mp~", "mp", "trans"}:
                assert len(node.children) == 3

            if name not in self.__ignored_proof_stats:
                self.__ignored_proof_stats[name] = 0
            self.__ignored_proof_stats[name] += 1

        # root will likely be unit-resolution...
        self.proof_graph.add_node(self.root_ref)

        for ref in self.proof_graph.nodes:
            self.__add_proof_successors(self.proof_graph, ref)

        reachable = nx.descendants(self.proof_graph, self.root_ref)
        reachable.add(self.root_ref)
        assert set(self.proof_graph.nodes) == reachable
        log_debug(
            f"{len(self.proof_graph.nodes)} nodes, {len(self.proof_graph.edges)} edges"
        )

    def __collect_rewrite(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "rewrite":
            return False
        assert len(node.children) == 1
        eq_node = self.resolve_child(ref)
        assert isinstance(eq_node, AppNode)
        assert eq_node.name == "="
        left, right = self.resolve_children(eq_node, 2)
        if left != right:
            self.rewrites[ref] = RewriteTerm(left, right)
        else:
            self.trivial_rewrites.add(ref)
        return True

    def __collect_lemma(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "lemma":
            return False
        premises, conclusion = self.resolve_children(ref, 2)
        left_last_children = premises.children[-1]
        assert self.is_leaf(left_last_children, "false")
        premises = premises.children[:-1]
        self.lemmas.append((premises, conclusion))
        assert self.is_proof_free(conclusion)
        return True

    def __collect_th_lemma(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "th-lemma":
            return False
        children = self.resolve_children(ref)
        premises, conclusion = children[:-1], children[-1]
        assert self.is_proof_free(conclusion)
        self.th_lemmas.append((premises, conclusion))
        return True

    def __collect_quant_inst(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "quant-inst":
            return False
        self.quant_insts.append(node)
        return True
