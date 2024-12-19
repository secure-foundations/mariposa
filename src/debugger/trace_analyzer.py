from enum import Enum
from typing import Dict, List

from tabulate import tabulate
from debugger.mut_info import MutantInfo
from debugger.quant_graph import TheirAnalysis
from debugger.query_loader import GroupedCost, InstCost
from debugger.edit_info import EditAction, EditInfo
from debugger.z3_utils import extract_sk_qid_from_name, format_expr_flat
from proof_builder import InstError, ProofInfo, QueryLoader, QunatInstInfo
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from tqdm import tqdm
import networkx as nx


def shorten_qid(qid):
    if len(qid) <= 80:
        return qid
    return qid[:80] + "..."


def is_prelude_qid(qid):
    return (
        qid.startswith("prelude_")
        or qid.startswith("internal_vstd")
        or qid.startswith("internal_core")
    )


class ProofAnalyzer(QueryLoader):
    def __init__(self, in_file_path, proof_info: ProofInfo):
        super().__init__(in_file_path)
        self.pi = proof_info
        self.G = nx.DiGraph()

        self._self_loops = set()
        self._nid_2_qid = dict()
        self._qid_2_nid = dict()

        self._build_graph()

    def get_nid(self, qid, add_missing=False):
        if qid not in self._nid_2_qid:
            assert add_missing
            nid = len(self._nid_2_qid)
            self._nid_2_qid[qid] = nid
            self._qid_2_nid[nid] = qid
        else:
            nid = self._nid_2_qid[qid]
        return nid

    def _add_edge(self, src, dst, color="black"):
        src = self.get_nid(src, True)
        dst = self.get_nid(dst, True)
        self.G.add_edge(src, dst, color=color)

    def _build_graph(self):
        for qid, qi in self.pi.qi_infos.items():

            if len(qi.skolem_deps) != 0:
                for dep in qi.skolem_deps:
                    dep = extract_sk_qid_from_name(dep)
                    self._add_edge(dep, qid, "red")

            if qi.inst_count == 0 and not self.pi.is_skolemized(qid):
                continue

            if not self.is_root(qid):
                pid = self.get_parent(qid)
                self._add_edge(pid, qid)
            else:
                self.G.add_node(self.get_nid(qid, True))

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
        qids = {self._qid_2_nid[n]: n for n in nids}
        return qids

    def list_nodes(self):
        return [(n, self._qid_2_nid[n]) for n in self.G.nodes]

    def list_self_loops(self):
        return [self._qid_2_nid[n] for n in self._self_loops]


class InstDiffer(ProofAnalyzer):
    def __init__(self, query_path, pi: ProofInfo, ti: MutantInfo):
        super().__init__(query_path, pi)

        self.pi = pi
        self.ti = ti
        ti.run_analysis()

        self.trace_count = self.group_costs(ti.as_flat_inst_counts())
        self.proof_count = self.group_costs(pi.as_flat_inst_counts())

        self.sources = self.list_sources()
        self.sloop = self.list_self_loops()
        self.actions = self.get_actions()

    def get_available_action(self, qid):
        if qid not in self.all_qids:
            log_warn(f"qid {qid} not found in query")
            return EditAction.NONE

        if qid in self.pi.qi_infos:
            errors = self.pi.qi_infos[qid].errors

            if errors == {InstError.SKOLEM_SELF}:
                return EditAction.DSPLIT

            if len(errors) != 0:
                # print(qid, self.pi.qi_infos[qid].errors)
                return EditAction.ERROR

        if qid not in self.proof_count:
            log_warn(f"qid {qid} is not a root")
            rid = self.get_root(qid)
            if self.proof_count[rid][qid] == 0 and not self.pi.is_skolemized(qid):
                return EditAction.ERASE
            return EditAction.NONE

        if self.pi.is_skolemized(qid):
            if self.proof_count[qid].subtotal == 0:
                # not instantiated but skolemized
                return EditAction.SKOLEMIZE
            else:
                # instantiated and skolemized
                return EditAction.DSPLIT

        if self.proof_count[qid].subtotal == 0:
            return EditAction.ERASE

        # self loop cannot be easily instantiated
        if qid in self.sources and qid not in self.sloop:
            return EditAction.INSTANTIATE

        return EditAction.NONE

    def get_actions(self):
        actions = dict()
        qids = self.filter_root_qids()

        for rid in qids:
            action = self.get_available_action(rid)

            if action not in {EditAction.NONE, EditAction.ERROR}:
                actions[rid] = action

        return actions

    def filter_root_qids(self):
        filtered = set()

        for rid in self.trace_count:
            t = self.trace_count[rid]
            p = self.proof_count[rid]
            # print(rid, t.subtotal, p.subtotal, self.pi.is_skolemized(rid))
    
            if (t.subtotal == 0 
                and p.subtotal == 0 
                and not self.pi.is_skolemized(rid)):
                continue

            filtered.add(rid)
        return filtered

    def get_simple_report(self):
        lines = ["qid,action,trace count,proof count"]

        line = ["all", "-", str(self.trace_count.total), str(self.proof_count.total)]

        lines.append(",".join(line))

        for qid in self.filter_root_qids():
            t: InstCost = self.trace_count[qid]
            p: InstCost = self.proof_count[qid]
            action = self.get_available_action(qid)
            line = ['"' + qid + '"', action.value, str(t.subtotal), str(p.subtotal)]
            lines.append(",".join(line))

        return "\n".join(lines)

    def get_report(self):
        self.graph2.useless = self.get_useless_counts()
        self.graph2.trace_freq = self.trace_count

        lines = ["qid,action,trace count,proof count,v0,v1,v2,v3,v4,v5"]

        line = ["all", "-", str(self.trace_count.total), str(self.proof_count.total)]
        lines.append(",".join(line))

        for qid in tqdm(self.filter_root_qids()):
            t: InstCost = self.trace_count[qid]
            p: InstCost = self.proof_count[qid]
            action = self.get_available_action(qid)
            line = ['"' + qid + '"', action.value, str(t.subtotal), str(p.subtotal)]

            for cost_fun in [
                self.graph2.estimate_cost_v0,
                self.graph2.estimate_cost_v1,
                self.graph2.estimate_cost_v2,
                self.graph2.estimate_cost_v3,
                self.graph2.estimate_cost_v4,
                self.graph2.estimate_cost_v5,
            ]:
                try:
                    line.append(str(cost_fun(qid)))
                except KeyError:
                    line.append("-1")

            line = ",".join(line)
            lines.append(line)

        return "\n".join(lines)

    def needed_for_skolem(self, qid):
        for pi in self.proofs:
            if qid in pi.new_skolem_funs:
                return True
        return False

    def debug_quantifier(self, qid):
        print("qid:", qid)
        q = self.quants[qid]
        print(format_expr_flat(q.assertion))    
    
        # if qid not in self.pi.qi_infos:
        #     log_warn(f"qid {qid} not found in proof")
        #     return
        # qi = self.pi.qi_infos[qid]

        # for bind in qi.bindings:
        #     for b in bind.values():
        #         print(self.pi.tt.expand_def(b))

    def get_useless_counts(self):
        res = dict()
        for rid in self.proof_count:
            for qid in self.trace_count[rid]:
                res[qid] = (self.trace_count[rid][qid], self.proof_count[rid][qid])
        return res

    # def do_stuff(self, eis: List[EditInfo]):
    #     # import scipy.stats as ss
    #     ress = dict()


    #         filtered = {qid: cost for qid, cost in costs.items() if qid in self.actions}
    #         sorted_keys = sorted(filtered, key=filtered.get, reverse=True)

    #         ranks = {key: rank + 1 for rank, key in enumerate(sorted_keys)}

    #         for qid in ress:
    #             ress[qid].append(ranks[qid])

    #     table = []

    #     for ei in eis:
    #         qid, action = ei.get_singleton_edit()
    #         table.append([qid, action.value, ei.get_id()[:5], *ress[qid], ei.time])
    #         # print(qid, ress[qid], ei.time)

    #     print(
    #         tabulate(
    #             table,
    #             headers=[
    #                 "qid",
    #                 "action",
    #                 "hash",
    #                 "v0",
    #                 "v1",
    #                 "v2",
    #                 "v3",
    #                 "v4",
    #                 "v5",
    #                 "time",
    #             ],
    #         )
    #     )
