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
        self.lemmas = dict()
        self.th_lemmas = dict()
        self.quant_insts = dict()

        self.__ignored_proof_stats = dict()
        self.__proof_node_count = 0

        self.proof_graph = nx.DiGraph()
        self.__analyze_proof_nodes()

    def __add_proof_successors(self, ref):
        queue = [ref]
        visited = set()

        while queue:
            current = queue.pop()
            if current in visited:
                continue
            visited.add(current)
            for child_ref in self.successors(current):
                # assert isinstance(child, LeafRefNode)
                if self.proof_graph.has_node(child_ref):
                    self.proof_graph.add_edge(ref, child_ref)
                else:
                    queue.append(child_ref)

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
            self.proof_graph.add_node(ref)

            if (
                self.__collect_lemma(ref)
                or self.__collect_rewrite(ref)
                or (ref in self.trivial_rewrites)
                or self.__collect_th_lemma(ref)
                or self.__collect_quant_inst(ref)
            ):
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
            for child_ref in self.successors(ref):
                if child_ref in self.proof_graph.nodes:
                    self.proof_graph.add_edge(ref, child_ref)
            # self.__add_proof_successors(ref)

        reachable = nx.descendants(self.proof_graph, self.root_ref)
        # for reached in reachable:
        #     if self.proof_graph.out_degree(reached) == 0:
        #         print(reached)

        reachable.add(self.root_ref)
        assert set(self.proof_graph.nodes) == reachable
        log_debug(
            f"{len(self.proof_graph.nodes)} nodes, {len(self.proof_graph.edges)} edges, root {self.root_ref}"
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
        assumptions, conclusion = self.resolve_children(ref, 2)
        left_last_children = assumptions.children[-1]
        assert self.is_leaf(left_last_children, "false")
        assumptions = assumptions.children[:-1]
        self.lemmas[ref] = (assumptions, conclusion)
        assert self.is_proof_free(conclusion)
        return True

    def __collect_th_lemma(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "th-lemma":
            return False
        children = self.resolve_children(ref)
        assumptions, conclusion = children[:-1], children[-1]
        assert self.is_proof_free(conclusion)
        self.th_lemmas[ref] = (assumptions, conclusion)
        return True

    def __collect_quant_inst(self, ref) -> bool:
        node = self.lookup(ref)
        if node.name != "quant-inst":
            return False
        node = self.resolve_child(ref)
        assert isinstance(node, AppNode)
        assert node.name == "or"
        children = self.resolve_children(node)
        l = children[0]
        inst = children[1:]
        # for i in inst:
        #     if not self.is_ground(i):
        #         print(ref)
        assert isinstance(l, AppNode)
        assert l.name == "not"
        l = self.resolve_child(l)
        assert isinstance(l, QuantNode)
        self.quant_insts[ref] = (l, inst)
        return True

    def debug_rewrite(self, ref):
        assert ref in self.rewrites
        rewrite = self.rewrites[ref]
        print(f"rewrite: {ref}")
        print(f"(define-fun foo () Bool (=\n\t{self.dump_node(rewrite.left)}\n\t{self.dump_node(rewrite.right)}))")

    def __debug_assumptions(self, assumptions):
        items = []
        for assumption in assumptions:
            item = self.lookup(assumption)
            last = item.children[-1]
            items.append(self.dump_node(last))
        return items

    def debug_lemma(self, ref):
        assert ref in self.lemmas
        assumptions, conclusion = self.lemmas[ref]
        print(f"lemma: {ref}")
        assumptions = self.__debug_assumptions(assumptions)
        if len(assumptions) == 0:
            assumptions = ""
        elif len(assumptions) == 1:
            assumptions = assumptions[0]
        else:
            assumptions = "\n\t\t".join(assumptions)
            assumptions = f"(and\n\t\t{assumptions})"
        conclusion = self.dump_node(conclusion)
        if assumptions:
            print(f"(define-fun foo () Bool (=> {assumptions}\n\t{conclusion}))")
        else:
            print(f"(define-fun foo () Bool {conclusion})")

    def debug_th_lemma(self, ref):
        assert ref in self.th_lemmas
        assumptions, conclusion = self.th_lemmas[ref]
        print(f"th-lemma: {ref}")
        assumptions = self.__debug_assumptions(assumptions)
        if len(assumptions) == 0:
            assumptions = ""
        elif len(assumptions) == 1:
            assumptions = assumptions[0]
        else:
            assumptions = "\n\t".join(assumptions)
            assumptions = f"(and \n\t{assumptions})"
        conclusion = self.dump_node(conclusion)
        if assumptions:
            print(f"(define-fun foo () Bool (=> {assumptions} {conclusion}))")
        else:
            print(f"(define-fun foo () Bool {conclusion})")

    def debug_quant_inst(self, ref):
        assert ref in self.quant_insts
        quant, insts = self.quant_insts[ref]
        print(f"quant-inst: {ref} {quant.qid}")
        quant = self.dump_node(quant)
        insts = [self.dump_node(inst) for inst in insts]
        if len(insts) == 1:
            insts = insts[0]
        else:
            insts = '\n\t'.join(insts)
            insts = f"(or \n\t{insts})"
        print(f"(define-fun foo () Bool {insts})")

    def debug_proof_node(self, ref):
        if ref in self.rewrites:
            self.debug_rewrite(ref)
        elif ref in self.lemmas:
            self.debug_lemma(ref)
        elif ref in self.th_lemmas:
            self.debug_th_lemma(ref)
        elif ref in self.quant_insts:
            self.debug_quant_inst(ref)
        else:
            node = self.lookup(ref)
            print("NYI", ref, node.name)
        print()
