from typing import Dict, Set
import networkx as nx
from debugger.tree_parser import *
from debugger.symbol_table import TermTable
from utils.system_utils import log_debug

class RewriteTerm:
    def __init__(self, left, right):
        assert left != right
        self.left = left
        self.right = right

class QuantInstInfo:
    def __init__(self, qname):
        self.qname = qname
        self.insts: Dict[QuantRef, Set[NodeRef]] = dict()
    
    def add_inst(self, quant, inst):
        assert isinstance(quant, QuantNode)
        assert quant.qid == self.qname
        assert isinstance(inst, NodeRef)
        if quant not in self.insts:
            self.insts[quant] = set()
        self.insts[quant].add(inst)

    def get_inst_count(self):
        return sum(len(insts) for insts in self.insts.values())

    def get_quant_count(self):
        return len(self.insts)
    
    def get_insts(self):
        res = []
        for _, insts in self.insts.items():
            res.extend(insts)
        return res

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
        self.qi_infos: Dict[str, QuantInstInfo] = dict()

        # self.__analyze_proof_nodes()
        # self.__analyze_quant_insts()

    def __analyze_proof_nodes(self):
        for ref in self.nodes():
            node = self.lookup_node(ref)
            if not isinstance(node, ProofNode):
                continue
            self.proof_graph.add_node(ref)
            self.__analyze_proof_node(ref, node)

        # root will likely be unit-resolution...
        self.proof_graph.add_node(self.root_ref)

        for ref in self.proof_graph.nodes:
            for child_ref in self.successors(ref):
                if child_ref in self.proof_graph.nodes:
                    self.proof_graph.add_edge(ref, child_ref)

        reachable = nx.descendants(self.proof_graph, self.root_ref)
        reachable.add(self.root_ref)
        assert set(self.proof_graph.nodes) == reachable
        log_debug(
            f"{len(self.proof_graph.nodes)} nodes, {len(self.proof_graph.edges)} edges, root {self.root_ref}"
        )

    def __analyze_proof_node(self, ref, node):
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
            or (ref in self.trivial_rewrites)
            or self.__collect_th_lemma(ref)
            or self.__collect_quant_inst(ref)
        ):
            return

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

    def __collect_rewrite(self, ref) -> bool:
        node = self.lookup_node(ref)
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
        node = self.lookup_node(ref)
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
        node = self.lookup_node(ref)
        if node.name != "th-lemma":
            return False
        children = self.resolve_children(ref)
        assumptions, conclusion = children[:-1], children[-1]
        assert self.is_proof_free(conclusion)
        self.th_lemmas[ref] = (assumptions, conclusion)
        return True

    def __collect_quant_inst(self, ref) -> bool:
        node = self.lookup_node(ref)
        if node.name != "quant-inst":
            return False
        node = self.resolve_child(ref)
        assert isinstance(node, AppNode)
        assert node.name == "or"
        children = self.resolve_children(node)
        l = children[0]
        inst = children[1:]
        assert isinstance(l, AppNode)
        assert l.name == "not"
        l = self.resolve_child(l)
        assert isinstance(l, QuantNode)
        self.quant_insts[ref] = (l, inst)
    
        if l.qid not in self.qi_infos:
            self.qi_infos[l.qid] = QuantInstInfo(l.qid)
        self.qi_infos[l.qid].add_inst(l, ref)

        return True

    def export_rewrite(self, ref):
        assert ref in self.rewrites
        rewrite = self.rewrites[ref]
        # print(f"rewrite: {ref}")
        return f"(define-fun foo () Bool (=\n\t{self.dump_node(rewrite.left)}\n\t{self.dump_node(rewrite.right)}))"

    def __export_assumptions(self, assumptions):
        items = []
        for assumption in assumptions:
            item = self.lookup_node(assumption)
            last = item.children[-1]
            items.append(self.dump_node(last))
        return items

    def __export_lemma(self, assumptions, conclusion):
        assumptions = self.__export_assumptions(assumptions)
        if len(assumptions) == 0:
            assumptions = ""
        elif len(assumptions) == 1:
            assumptions = assumptions[0]
        else:
            assumptions = "\n\t\t".join(assumptions)
            assumptions = f"(and\n\t\t{assumptions})"
        conclusion = self.dump_node(conclusion)
        if assumptions:
            conclusion = f"(=> {assumptions}\n\t{conclusion})"
        return f"(define-fun foo () Bool {conclusion})"

    def export_lemma(self, ref):
        assert ref in self.lemmas
        assumptions, conclusion = self.lemmas[ref]
        return self.__export_lemma(assumptions, conclusion)

    def export_th_lemma(self, ref):
        assert ref in self.th_lemmas
        assumptions, conclusion = self.th_lemmas[ref]
        return self.__export_lemma(assumptions, conclusion)

    def export_quant_inst(self, ref):
        assert ref in self.quant_insts
        quant, insts = self.quant_insts[ref]
        insts = [self.dump_node(inst) for inst in insts]
        if len(insts) == 1:
            insts = insts[0]
        else:
            insts = '\n\t'.join(insts)
            insts = f"(or \n\t{insts})"
        return f"; {ref} quant-inst: {quant.qid}\n(define-fun foo () Bool {insts})"

    def export_proof_node(self, ref) -> str:
        if ref in self.rewrites:
            return self.export_rewrite(ref)
        if ref in self.lemmas:
            return self.export_lemma(ref)
        if ref in self.th_lemmas:
            return self.export_th_lemma(ref)
        if ref in self.quant_insts:
            return self.export_quant_inst(ref)
        return f"NYI"

    def __analyze_quant_insts(self):
        for q_name in self.qi_infos:
            qi_info = self.qi_infos[q_name]
            print(f"{q_name}")
            print(f"{qi_info.get_quant_count()} quantifiers")
            print(f"{qi_info.get_inst_count()} instances")
            for inst in qi_info.get_insts():
                print(self.export_quant_inst(inst))
            print()

