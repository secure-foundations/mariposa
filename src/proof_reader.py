#!/usr/bin/env python3

import time, pickle
from z3 import *
from typing import Dict, Optional, Set

from tabulate import tabulate
from debugger.subs_mapper import SubsMapper
from enum import Enum
import networkx as nx

from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.z3_utils import (
    collapse_sexpr,
    extract_sk_qid_from_name,
    extract_sk_qid_from_decl,
    match_qi,
)
from utils.system_utils import log_info, log_warn


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


class ProofInfo:
    def __init__(self, cur_skolem_funs):
        self.cur_skolem_funs = cur_skolem_funs
        self.new_skolem_funs = dict()
        self.qi_infos = dict()
        self.new_sk_qids = set()

    def add_qi(self, qid, m: SubsMapper, insts):
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

            bind = {k: collapse_sexpr(v.sexpr()) for k, v in bind.items()}

            qi.add_binding(bind)

        for fun in skf.funs:
            if fun not in self.cur_skolem_funs:
                qi.add_error(InstError.SKOLEM_FUNS)
                qi.add_skolem_dep(fun)
                self.new_skolem_funs[fun] = skf.funs[fun]

        self.qi_infos[qid] = qi

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
        self.proc_solver.set("timeout", 60000)
        res = self.proc_solver.check()
        self.proof_time = int((time.time() - start))

        if res != unsat:
            log_warn("[proof] query returned {0}".format(res))
            return None

        p = self.proc_solver.proof()
        self.__collect_instantiations(p)
        self.reset_visit()

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
        for qid, insts in self.instantiations.items():
            m = SubsMapper(self.quants[qid].quant)
            pi.add_qi(qid, m, insts)
        pi.set_skolemized()
        return pi


class ProofAnalyzer(QueryLoader):
    def __init__(self, in_file_path, proof_info: ProofInfo):
        super().__init__(in_file_path)
        self.pi = proof_info
        # self.in_file_path = in_file_path
        self.graph = nx.DiGraph()

        short_ids = dict()
        reverse_ids = dict()
        
        def get_short_id(qid):
            if qid not in short_ids:
                short_ids[qid] = len(short_ids)
                reverse_ids[short_ids[qid]] = qid
            return short_ids[qid]
        
        # print(self.pi.cur_skolem_funs)
        # print(self.pi.new_skolem_funs.keys())

        for qid, qi in self.pi.qi_infos.items():
            if len(qi.skolem_deps) != 0:
                for dep in qi.skolem_deps:
                    dep = extract_sk_qid_from_name(dep)
                    self.graph.add_edge(get_short_id(dep), get_short_id(qid), color="red")
            if qi.inst_count == 0 and not pi.is_skolemized(qid):
                continue
            if not self.is_root(qid):
                pid = self.get_parent(qid)
                self.graph.add_edge(get_short_id(pid), get_short_id(qid), label=qi.inst_count)

        for qid in self.pi.new_skolem_funs:
            qid = extract_sk_qid_from_name(qid)
            if not self.is_root(qid):
                pid = self.get_parent(qid)
                self.graph.add_edge(get_short_id(pid), get_short_id(qid), label=qi.inst_count)

        # assert pi.is_skolemized("user_lib__os_mem_util__preserves_mem_chunk_good_180")
        table = []
        for n in self.graph.nodes:
            qid = reverse_ids[n]
            table.append((qid, self.graph.in_degree(n), self.graph.out_degree(n)))
        
        table = sorted(table, key=lambda x: x[2], reverse=True)
        print(tabulate(table, headers=["qid", "in", "out"]))

        # for qid in short_ids:
        #     print(short_ids[qid], qid)

        # nx.drawing.nx_agraph.write_dot(self.graph, "test.dot")


if __name__ == "__main__":
    set_param(proof=True)

    # i = ProofReader(sys.argv[1])
    # pi = i.try_prove()
    # pi.save("cyclic.pickle")
    pi = ProofInfo.load("dbg/mimalloc--segment__segment_span_free.smt2/insts/rename.8072387806861946866")
    # pi.print_report()
    pa = ProofAnalyzer(sys.argv[1], pi)
