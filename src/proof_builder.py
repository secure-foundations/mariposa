#!/usr/bin/env python3

import binascii
import time, pickle
from tqdm import tqdm
from z3 import *
from typing import Dict, Optional, Set, Tuple

from tabulate import tabulate
from debugger.subs_mapper import SubsMapper
from enum import Enum

from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.term_table import TermTable
from debugger.z3_utils import (
    collapse_sexpr,
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
        if binding in self.bindings:
            return
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
        self.tt: TermTable = TermTable()

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
                qi.add_error(InstError.BIND_ERROR)
                log_warn("failed to map all variables when insting " + qid)
                continue

            for i, b in bind.items():
                bind[i] = self.tt.process_expr(b)
                skf.find_sk_fun(b)

            qi.add_binding(bind)

        for fun in skf.sk_funs:
            if fun not in self.cur_skolem_funs:
                qi.add_error(InstError.SKOLEM_FUNS)
                qi.add_skolem_dep(fun)
                self.new_skolem_funs[fun] = skf.sk_funs[fun]

        self.qi_infos[qid] = qi

    def finalize(self):
        log_info(f"[proof] finalizing proof info")

        for decl in self.tt.sk_funs.values():
            qid = extract_sk_qid_from_decl(decl)
            self.new_sk_qids.add(qid)
            if qid not in self.qi_infos:
                continue
            self.qi_infos[qid].errors.add(InstError.SKOLEM_SELF)

        self.tt.finalize()

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


class ProofBuilder(QueryLoader):
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
        log_info(f"[proof] solver finished in {self.proof_time} (s)")

        p = self.proc_solver.proof()
        # print(collapse_sexpr(p.sexpr()))

        self.__collect_instantiations(p)
        self.reset_visit()

        pi = ProofInfo(self.cur_skolem_funs)
        log_info(f"[proof] adding instantiations to proof ")
        for qid, insts in tqdm(self.instantiations.items()):
            # if qid != "internal_vstd!seq_lib.impl&__0.no_duplicates.?_definition":
            #     continue
            # print(qid)
            # print(collapse_sexpr(self.quants[qid].quant.sexpr()))
            m = SubsMapper(self.quants[qid].quant)
            pi.add_qi(qid, m, insts)
        pi.finalize()
        return pi

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


if __name__ == "__main__":
    set_param(proof=True)

    query_file = sys.argv[1]
    pb = ProofBuilder(query_file)
    pi = pb.try_prove()
    pi.save("cyclic.pickle")
    pi = ProofInfo.load("cyclic.pickle")

    # pi.tt.debug()

    for qid in pi.qi_infos:
        bindings = pi.qi_infos[qid].bindings
        symbols = set()
        esize = 0
        for i, bind in enumerate(bindings):
            for k, v in bind.items():
                if v.startswith("hcf_"):
                    symbols.add(v)
                else:
                    esize += len(v)
        esize += pi.tt.estimate_size(symbols)
