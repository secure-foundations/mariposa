import hashlib
from typing import Dict, List, Set
import networkx as nx
from collections import Counter
from debugger.tree_parser import *
from debugger.symbol_table import TermTable
from utils.cache_utils import load_cache_or
from utils.system_utils import log_debug, log_error, log_warn

class RewriteTerm:
    def __init__(self, left, right):
        assert left != right
        self.left = left
        self.right = right

class QuantInstInfo:
    def __init__(self, qname):
        self.qname = qname
        # self.__proof_refs: Dict[QuantRef, NodeRef] = dict()
        self.__insts: Dict[QuantRef, Set[NodeRef]] = dict()
        self.__skolem_deps: Dict[NodeRef, Set[str]] = dict()

    def add_inst(self, quant, inst, skolem_deps):
        assert isinstance(quant, QuantNode)
        assert quant.qid == self.qname
        assert isinstance(inst, NodeRef)
        # assert isinstance(proof_ref, NodeRef)
        # self.__proof_refs[proof_ref] = inst
        if quant not in self.__insts:
            self.__insts[quant] = set()
        self.__insts[quant].add(inst)
        assert inst not in self.__skolem_deps
        self.__skolem_deps[inst] = skolem_deps

    def get_inst_count(self):
        return len(self.get_all_insts())

    def get_quant_count(self):
        return len(self.__insts)

    def get_all_insts(self):
        res = []
        for insts in self.__insts.values():
            res.extend(insts)
        return res

    def get_feasible_insts(self):
        res = []
        for inst in self.get_all_insts():
            if len(self.__skolem_deps[inst]) == 0:
                res.append(inst)
        return res

    def get_all_skolem_deps(self):
        res = set()
        for deps in self.__skolem_deps.values():
            res |= deps
        return res

class ProofAnalyzer(TermTable):
    def __init__(self, file_path):
        super().__init__(file_path)

        self.rewrites = dict()
        self.trivial_rewrites = set()
        self.lemmas = dict()
        self.th_lemmas = dict()

        # self.__ignored_proof_stats = dict()
        self.__proof_node_count = 0

        self.__qname_of_inst_ref: Dict[NodeRef, str] = dict()

        self.__skolemization_consequences: Dict[str, Counter] = dict()
        self.__insts_under_qname: Dict[str, QuantInstInfo] = dict()

        self.proof_graph = nx.DiGraph()
        self.__analyze_proof_nodes()

        # self.__analyze_quant_insts()

    def __analyze_proof_nodes(self):
        for ref in self.nodes():
            node = self.lookup_node(ref)
            if not isinstance(node, ProofNode):
                continue
            # self.proof_graph.add_node(ref)
            self.__analyze_proof_node(ref, node)

        # root will likely be unit-resolution...
        # self.proof_graph.add_node(self.root_ref)

        # for ref in self.proof_graph.nodes:
        #     for child_ref in self.successors(ref):
        #         if child_ref in self.proof_graph.nodes:
        #             self.proof_graph.add_edge(ref, child_ref)

        # reachable = nx.descendants(self.proof_graph, self.root_ref)
        # reachable.add(self.root_ref)

        # if set(self.proof_graph.nodes) != reachable:
        #     log_debug(f"[proof graph] graph is not connected, reachable: {len(reachable)}, total: {len(self.proof_graph.nodes)}")

        # log_debug(
        #     f"[proof graph] {len(self.proof_graph.nodes)} nodes, {len(self.proof_graph.edges)} edges, root {self.root_ref}"
        # )

    def __analyze_proof_node(self, ref, node):
        self.__proof_node_count += 1
        name = node.name
        assert name in PROOF_GRAPH_RULES

        conclusion = node.children[-1]

        if not self.is_proof_free(conclusion):
            log_warn(f"proof node conclusion is not grounded: {ref}")
            return

        if (
            self.__collect_lemma(ref)
            or self.__collect_rewrite(ref)
            or (ref in self.trivial_rewrites)
            or self.__collect_th_lemma(ref)
            or self.__collect_quant_inst(ref)
        ):
            return

        # if name in {
        #     "iff-true",
        #     "iff-false",
        #     "and-elim",
        #     "not-or-elim",
        #     "symm",
        #     # "nnf-pos",
        # }:
        #     # print(name, len(node.children))
        #     assert len(node.children) == 2
        # elif name in {
        #     "refl",
        #     "asserted",
        #     "hypothesis",
        #     "commutativity",
        #     "def-axiom",
        # }:
        #     assert len(node.children) == 1
        # elif name in {"mp~", "mp", "trans"}:
        #     assert len(node.children) == 3

        # if name not in self.__ignored_proof_stats:
        #     self.__ignored_proof_stats[name] = 0
        # self.__ignored_proof_stats[name] += 1

    def __collect_rewrite(self, ref) -> bool:
        node = self.lookup_node(ref)
        if node.name != "rewrite":
            return False
        assert len(node.children) == 1
        eq_node = self.resolve_child(ref)
        assert isinstance(eq_node, AppNode)
        if eq_node.name != "=":
            log_warn(f"rewrite node is not an equality: {ref}")
            self.pprint_node(eq_node, 10)
            return False
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
        if not self.is_leaf(left_last_children, "false"):
            log_warn(f"lemma node does not end with false?: {ref}")
            self.pprint_node(left_last_children, 10)
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
        if node.name != "or":
            log_error(f"quant-inst node is not an or: {ref}")
            self.pprint_node(node, 5)
            assert False

        children = self.resolve_children(node)
        l = children[0]
        inst = node.children[1:]
        assert isinstance(l, AppNode)
        assert l.name == "not"
        quant = self.resolve_child(l)
        qname = quant.qid

        assert isinstance(quant, QuantNode)
        assert all(isinstance(i, NodeRef) for i in inst)

        if len(inst) == 1:
            actual_inst_ref = inst[0]
        else:
            instance = AppNode("or", inst)
            actual_inst_ref = self.add_tree_node(instance)

        self.__qname_of_inst_ref[ref] = qname

        if qname not in self.__insts_under_qname:
            self.__insts_under_qname[qname] = QuantInstInfo(qname)

        skolem_deps = self.get_skolem_deps(actual_inst_ref)
        self.__insts_under_qname[qname].add_inst(quant, actual_inst_ref, skolem_deps)
        self.__record_skolem_deps(qname, skolem_deps)

        return True
    
    def __record_skolem_deps(self, qname, deps):
        if len(deps) == 0:
            return

        for dep in deps:
            if dep not in self.__skolemization_consequences:
                self.__skolemization_consequences[dep] = Counter()
            self.__skolemization_consequences[dep][qname] += 1

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

    # def export_quant_inst(self, ref):
    #     assert ref in self.__qname_of_inst_ref
    #     name = self.__qname_of_inst_ref[ref]
    #     # items = self.dump_node(i)
    #     symbol = ref.export_symbol()
    #     return symbol, f"; {ref} quant-inst: {quant.qid}\n(define-fun {symbol} () Bool {items})"

    def get_qname_of_inst_ref(self, ref):
        return self.__qname_of_inst_ref[ref]

    def export_proof_node(self, ref) -> str:
        if ref in self.rewrites:
            return self.export_rewrite(ref)
        if ref in self.lemmas:
            return self.export_lemma(ref)
        if ref in self.th_lemmas:
            return self.export_th_lemma(ref)
        # if ref in self.quant_insts:
        #     return self.export_quant_inst(ref)
        return f"NYI"

    def get_qi_counts(self):
        res = dict()
        for qname, qi_info in self.__insts_under_qname.items():
            res[qname] = qi_info.get_inst_count()
        return res

    def get_inst_info_under_qname(self, qname) -> QuantInstInfo:
        return self.__insts_under_qname[qname]

    def has_inst_info(self, qname):
        return qname in self.__insts_under_qname

    def has_skolemized_qname(self, qname):
        return qname in self.__skolemization_consequences

    def get_skolem_consequences(self):
        return self.__skolemization_consequences

    @staticmethod
    def from_proof_file(proof_path, clear=False) -> "ProofAnalyzer":
        m = hashlib.md5()
        m.update(str(proof_path).encode())
        pickle_name = m.hexdigest() + ".pickle"
        print(pickle_name)
        return load_cache_or(pickle_name, lambda: ProofAnalyzer(proof_path), clear)
