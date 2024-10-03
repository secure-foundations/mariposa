#!/usr/bin/env python3

import binascii
import time, pickle
from z3 import *
from typing import Dict, Optional, Set, Tuple

from tabulate import tabulate
from debugger.subs_mapper import SubsMapper
from enum import Enum
import networkx as nx
import re

from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.z3_utils import (
    AstVisitor,
    extract_sk_qid_from_name,
    extract_sk_qid_from_decl,
    match_qi,
)
from utils.system_utils import log_info, log_warn, subprocess_run


class InstError(Enum):
    UNMAPPED_VARS = 1
    NON_ROOT = 2
    SKOLEM_FUNS = 3
    BIND_ERROR = 4
    SKOLEM_SELF = 5


class QunatInstInfo:
    def __init__(self, qid, inst_count):
        self.qid = qid
        self.inst_count = inst_count
        self.errors = set()
        self.bindings = []
        self.skolem_deps = set()

    def add_binding(self, binding):
        self.bindings.append(binding)

    def add_error(self, error):
        self.errors.add(error)

    def add_skolem_dep(self, dep):
        self.skolem_deps.add(dep)


def hash_cons_name(id):
    return f"hcf_{id}_fch"


def hack_search_hash_cons(term: str):
    return re.findall("hcf_\d+_fch", term)


class HashConser(AstVisitor):
    def __init__(self):
        super().__init__()
        self._ref_counts = dict()
        self.defs = dict()
        self.depends = dict()
        self.__targets = set()

    def __get_fresh_name(self):
        return hash_cons_name(len(self.defs))

    def process_expr(self, e):
        self._count_refs(e)

    def _count_refs(self, e: ExprRef):
        if is_var(e) or is_const(e):
            return

        if self.visit(e):
            self._ref_counts[e] += 1
            return

        self._ref_counts[e] = 1

        for c in e.children():
            self._count_refs(c)

    def create_defs(self):
        for e, c in self._ref_counts.items():
            if c >= 1:
                self.__targets.add(e)

        for e in self.__targets:
            self._create_defs(e)

        res = list(self.defs.values())
        res = {r[0]: r[1:] for r in res}

        defs = []
        # this is to print the definitions in order
        for i in range(len(res)):
            name = hash_cons_name(i)
            defs.append((name, res[name][0], str(res[name][1])))
        return defs

    def _create_defs(self, e: ExprRef) -> Tuple[str, Set[str]]:
        if is_var(e) or is_quantifier(e):
            assert False

        if is_const(e):
            return (str(e), set())

        if e in self.defs:
            name = self.defs[e][0]
            return (name, {name})

        fun = e.decl().name()
        res = [fun]
        deps = set()

        for c in e.children():
            r, d = self._create_defs(c)
            res.append(r)
            deps.update(d)

        res = "(" + " ".join(res) + ")"

        if e in self.__targets:
            new_name = self.__get_fresh_name()
            self.depends[new_name] = deps
            self.defs[e] = (new_name, res, e.sort())
            return (new_name, {new_name})
        return (res, deps)

    def rewrite_expr(self, e: ExprRef):
        if is_const(e) or is_var(e):
            return str(e)

        if e in self.defs:
            return self.defs[e][0]

        args = [self.rewrite_expr(c) for c in e.children()]
        return f"({e.decl().name()} {' '.join(args)})"


class ProofInfo:
    def __init__(self, cur_skolem_funs):
        self.cur_skolem_funs = cur_skolem_funs
        self.new_skolem_funs = dict()
        self.qi_infos = dict()
        self.new_sk_qids = set()
        self.conser_defs = []
        self.expr_deps = dict()
        self.transitive_deps = dict()

    def add_qi(self, qid, m: SubsMapper, insts, conser: HashConser):
        qi = QunatInstInfo(qid, len(insts))

        if m.unmapped != 0:
            qi.add_error(InstError.UNMAPPED_VARS)
            self.qi_infos[qid] = qi
            return

        skf = SkolemFinder()

        for inst in insts:
            bind = m.map_inst(inst)

            if bind is None:
                qi.add_error.add(InstError.BIND_ERROR)
                log_warn("failed to map all variables when insting " + self.qid)
                continue

            for b in bind.values():
                skf.find_sk_fun(b)

            for b in bind.values():
                conser.process_expr(b)

            qi.add_binding(bind)

        for fun in skf.funs:
            if fun not in self.cur_skolem_funs:
                qi.add_error(InstError.SKOLEM_FUNS)
                qi.add_skolem_dep(fun)
                self.new_skolem_funs[fun] = skf.funs[fun]

        self.qi_infos[qid] = qi

    def hash_cons_bindings(self, conser: HashConser):
        for qi in self.qi_infos.values():
            for b in qi.bindings:
                for k, v in b.items():
                    b[k] = conser.rewrite_expr(v)

    def set_skolemized(self):
        for decl in self.new_skolem_funs.values():
            qid = extract_sk_qid_from_decl(decl)
            self.new_sk_qids.add(qid)
            if qid not in self.qi_infos:
                continue
            self.qi_infos[qid].errors.add(InstError.SKOLEM_SELF)

    def get_inst_count(self, qid):
        if qid not in self.qi_infos:
            return 0
        return self.qi_infos[qid].inst_count

    def has_qid(self, qid):
        return qid in self.qi_infos

    def as_frequency(self):
        res = dict()
        for qid in self.qi_infos:
            res[qid] = self.qi_infos[qid].inst_count
        return res

    def print_report(self):
        table = []
        for qid, info in self.qi_infos.items():
            e = len(info.errors)
            table.append((qid, info.inst_count, e))
        print(tabulate(table, headers=["qid", "insts", "errors"]))

        log_info("listing skolem functions:")
        for sk_fun in self.new_skolem_funs.values():
            print(sk_fun)

    @staticmethod
    def load(file_path) -> "ProofInfo":
        with open(file_path, "rb") as f:
            return pickle.load(f)

    def save(self, out_file_path):
        self.lb = None
        with open(out_file_path, "wb") as f:
            pickle.dump(self, f)

    def is_skolemized(self, qid):
        return qid in self.new_sk_qids


class ProofReader(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)

        # map qid to its quant-inst applications
        self.instantiations: Dict[str, Set[ExprRef]] = dict()

    def try_prove(self) -> Optional[ProofInfo]:
        start = time.time()
        self.proc_solver.set("timeout", 30000)
        res = self.proc_solver.check()
        self.proof_time = int((time.time() - start))

        if res != unsat:
            log_warn("[proof] query returned {0}".format(res))
            return None
        log_info(f"[proof] solver finished in {self.proof_time}(s)")

        p = self.proc_solver.proof()
        self.__collect_instantiations(p)
        self.reset_visit()
        log_info(f"[proof] instantiations collected")

        return self.__post_process()

    def __collect_instantiations(self, p):
        if self.visit(p) or is_const(p) or is_var(p):
            return

        if is_quantifier(p):
            p = p.body()

        res = match_qi(p)

        if res is not None:
            qid, qi = res
            if qid not in self.instantiations:
                self.instantiations[qid] = set()
            self.instantiations[qid].add(qi)

        for c in p.children():
            self.__collect_instantiations(c)

    def __post_process(self) -> ProofInfo:
        pi = ProofInfo(self.cur_skolem_funs)
        conser = HashConser()
        for qid, insts in self.instantiations.items():
            m = SubsMapper(self.quants[qid].quant)
            pi.add_qi(qid, m, insts, conser)
        defs = conser.create_defs()
        pi.conser_defs = defs
        pi.expr_deps = conser.depends
        pi.transitive_deps = dict()
        for k, v in conser.depends.items():
            t = [pi.transitive_deps[d] for d in v] + [v]
            pi.transitive_deps[k] = set.union(*t)
        pi.hash_cons_bindings(conser)
        pi.set_skolemized()
        return pi


class ProofAnalyzer(QueryLoader):
    def __init__(self, in_file_path, proof_info: ProofInfo):
        super().__init__(in_file_path)
        self.pi = proof_info
        # self.in_file_path = in_file_path
        self.G = nx.DiGraph()

        self._self_loops = set()
        self._nid_2_qid = dict()
        self._qid_2_nid = dict()

        self._build_graph()

    def get_nid(self, qid):
        if qid not in self._nid_2_qid:
            nid = len(self._nid_2_qid)
            self._nid_2_qid[qid] = nid
            self._qid_2_nid[nid] = qid
        else:
            nid = self._nid_2_qid[qid]
        return nid

    def _add_edge(self, src, dst, color="black"):
        src = self.get_nid(src)
        dst = self.get_nid(dst)
        self.G.add_edge(src, dst, color=color)

    def _build_graph(self):
        for qid, qi in self.pi.qi_infos.items():
            if len(qi.skolem_deps) != 0:
                for dep in qi.skolem_deps:
                    dep = extract_sk_qid_from_name(dep)
                    self._add_edge(dep, qid, "red")

            if qi.inst_count == 0 and not pi.is_skolemized(qid):
                continue

            if not self.is_root(qid):
                pid = self.get_parent(qid)
                self._add_edge(pid, qid)
                # G.add_edge(get_nid(pid), get_nid(qid), label=qi.inst_count)

        for qid in self.pi.new_skolem_funs:
            qid = extract_sk_qid_from_name(qid)
            if not self.is_root(qid):
                pid = self.get_parent(qid)
                self._add_edge(pid, qid)

        node_colors = dict()

        # remove self loop edges
        for n, _ in list(nx.selfloop_edges(self.G)):
            node_colors[n] = "red"
            self._self_loops.add(n)
            self.G.remove_edge(n, n)

        nx.set_node_attributes(self.G, node_colors, name="color")

        if not nx.is_directed_acyclic_graph(self.G):
            log_warn("proof QI graph is cyclic!")
            return

        log_info("proof QI graph is acyclic")

    def save_graph(self, dot_path):
        nx.drawing.nx_agraph.write_dot(self.G, dot_path)
        # dot -Tpdf test.dot -o test.pdf  -Grankdir=TB -Granksep=0.5
        subprocess_run(
            [
                "dot",
                "-Tpdf",
                dot_path,
                "-o",
                dot_path + ".pdf",
                "-Grankdir=TB",
                "-Granksep=0.5",
            ],
            debug=True,
            check=True,
        )

    def list_sources(self):
        nids = [n for n in self.G.nodes if self.G.in_degree(n) == 0]
        qids = {n: self._qid_2_nid[n] for n in nids}
        return qids


if __name__ == "__main__":
    set_param(proof=True)

    i = ProofReader(sys.argv[1])
    pi = i.try_prove()
    pi.save("cyclic.pickle")

    pi = ProofInfo.load("cyclic.pickle")
    # print(pi.expr_deps)
    pa = ProofAnalyzer(sys.argv[1], pi)
    

    # pa.save_graph("test.dot")
    srcs = pa.list_sources()
    
    G2 = nx.DiGraph()

    # for d in pa.pi.conser_defs:
    #     for dep in pi.expr_deps[d[0]]:
    #         G2.add_edge(d[0], dep)

    for d in pa.pi.conser_defs:
        print(d[0], d[1])

    deps = set()
    for n, q in srcs.items():
        for bind in pi.qi_infos[q].bindings:
            print("nid", n, q)
            for k, v in bind.items():
                print("\t", k, v)
                for dep in hack_search_hash_cons(v):
                    G2.add_node(n, shape="box")
                    G2.add_edge(dep, n)
                    deps.add(dep)

    t_deps = set()
    for u in deps:
        t_deps.update(pi.transitive_deps[u])
        t_deps.add(u)
    
    for u in t_deps:
        for v in pi.expr_deps[u]:
            G2.add_edge(v, u, color="red")

    dot_path = "test.dot"
    nx.drawing.nx_agraph.write_dot(G2, dot_path)
    # dot -Tpdf test.dot -o test.pdf  -Grankdir=TB -Granksep=0.5
    subprocess_run(
        [
            "dot",
            "-Tpdf",
            dot_path,
            "-o",
            dot_path + ".pdf",
            "-Grankdir=TB",
            "-Granksep=0.5",
        ],
        debug=True,
        check=True,
    )
