from enum import Enum
from typing import Dict, List

from tabulate import tabulate
from debugger.query_loader import QueryInstFreq
from debugger.z3_utils import extract_sk_qid_from_name
from proof_builder import InstError, ProofInfo, QueryLoader, QunatInstInfo
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
import networkx as nx


def shorten_qid(qid):
    if len(qid) <= 75:
        return qid
    return qid[:75] + "..."


def is_prelude_qid(qid):
    return (
        qid.startswith("prelude_")
        or qid.startswith("internal_vstd")
        or qid.startswith("internal_core")
    )


# class TraceAnalyzer(QueryLoader):
#     def __init__(self, query_path, proofs: List[ProofInfo]):
#         super().__init__(query_path)
#         log_check(len(proofs) != 0, "no proofs provided")
#         self.proofs = proofs
#         self.pf_freqs = []

#         for proof in proofs:
#             freq = proof.as_frequency()
#             freq = self.group_frequencies(freq)
#             self.pf_freqs.append(freq)

#     def group_frequencies(self, freq: Dict[str, int]) -> Dict[str, GroupInstFreq]:
#         res = dict()
#         for qid in self.all_qids:
#             if qid not in freq:
#                 freq[qid] = 0
#             rid = self.get_root(qid)
#             if rid not in res:
#                 res[rid] = GroupInstFreq(rid)
#             res[rid][qid] = freq[qid]
#         for rid in res:
#             res[rid].finalize()
#         return res

#     def get_proof_inst_counts(self, rid, qid=None):
#         res = []
#         for i, pf_freq in enumerate(self.pf_freqs):
#             if qid is not None:
#                 res.append(pf_freq[rid][qid])
#                 if self.proofs[i].is_skolemized(qid):
#                     res.append("s")
#                 else:
#                     res.append("-")
#             else:
#                 res.append(pf_freq[rid].total_count)
#                 if self.proofs[i].is_skolemized(rid):
#                     res.append("s")
#                 else:
#                     res.append("-")
#         return res

#     def get_proof_total_inst_counts(self):
#         gsums = [0] * len(self.proofs)
#         for i, pi in enumerate(self.proofs):
#             pf = pi.as_frequency()
#             for rid in pf:
#                 gsums[i] += pf[rid]
#         return gsums

#     def get_report(self, trace_freq: Dict[str, int], table_limit=None):
#         if table_limit is None:
#             table_limit = 1e9

#         report = "traced instantiations:\n"
#         t_freq = self.group_frequencies(trace_freq)
#         missing = self.__get_missing_rids(t_freq)
#         group_sums = [0] * (1 + len(self.proofs) * 2)
#         ia = InstAnalyzer(self.in_file_path, self.proofs[0])
#         srcs = ia.list_sources()

#         t_freq: List[(str, GroupInstFreq)] = sorted(
#             t_freq.items(), key=lambda x: x[1].total_count, reverse=True
#         )
#         table = []

#         for rid, tg in t_freq:
#             action = "-"
#             inst_needed = self.pf_freqs[0][rid].total_count != 0

#             if rid in srcs.values():
#                 if self.has_conflicts(rid):
#                     action = "X"
#                 elif self.needed_for_skolem(rid):
#                     assert not inst_needed
#                     action = "S"
#                 else:
#                     action = "I"
#             elif not inst_needed:
#                 if self.needed_for_skolem(rid):
#                     action = "S"
#                 else:
#                     action = "E"

#             group_sums[0] += tg.total_count
#             ptotals = self.get_proof_inst_counts(rid)

#             row = [shorten_qid(rid), action, tg.total_count]

#             for i in range(len(self.proofs)):
#                 group_sums[i * 2 + 1] += ptotals[i * 2]

#             if tg.is_singleton():
#                 table.append(row + ptotals)
#                 continue

#             table.append(row)
#             table.append(
#                 ["- [root]", "", tg.root_count] + self.get_proof_inst_counts(rid, rid)
#             )
#             for qid in tg:
#                 if qid == rid:
#                     continue
#                 row = ["- " + shorten_qid(qid), "", tg[qid]] + self.get_proof_inst_counts(
#                     rid, qid
#                 )
#                 table.append(row)

#         headers = ["QID", "Action", "T"]

#         for i in range(len(self.proofs)):
#             headers.append(f"P{i}#")
#             headers.append("")

#         if len(table) > table_limit:
#             row = [f"... eliding {len(table) - table_limit} more rows ..."] + [
#                 "..."
#             ] * (len(headers) - 1)
#             table = table[:table_limit]
#             table.append(row)
#         table.append(["total", ""] + group_sums)
#         report += tabulate(table, headers=headers)

#         table = []
#         for rid in missing:
#             row = [shorten_qid(rid)] + self.get_proof_inst_counts(rid)
#             table.append(row)

#         headers = ["QID"] + [f"P{i}" for i in range(len(self.proofs))]

#         if len(table) > table_limit:
#             row = [f"... eliding {len(table) - table_limit} more rows ..."] + [
#                 "..."
#             ] * (len(headers) - 1)
#             table = table[:table_limit]
#             table.append(row)

#         if len(table) != 0:
#             # log_info("missing instantiations:")
#             report += "\n\nmissing instantiations:\n"
#             report += tabulate(table, headers=headers)

#         skids = set()

#         for (i, pi) in enumerate(self.proofs):
#             for qid in pi.new_sk_qids:
#                 skids.add(qid)

#         if len(skids) != 0:
#             report += "\n\nskolemized qids:\n"
#             for qid in skids:
#                 report += qid + "\n"

#         return report

#     def __get_missing_rids(self, traced_qids: Dict[(str, GroupInstFreq)]):
#         used, res = set(), set()
#         for pf_freq in self.pf_freqs:
#             for rid, pg in pf_freq.items():
#                 if pg.total_count != 0:
#                     used.add(rid)
#         for rid, tg in traced_qids.items():
#             if tg.total_count == 0 and rid in used:
#                 res.add(rid)
#         return res

#     def needed_for_skolem(self, qid):
#         for pi in self.proofs:
#             if qid in pi.new_skolem_funs:
#                 return True
#         return False


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


class EditAction(Enum):
    NONE = "-"
    ERASE = "erase"
    SKOLEMIZE = "skolemize"
    DSPLIT = "dsplit"
    INSTANTIATE = "instantiate"
    ERROR = "error"


class InstDiffer(ProofAnalyzer):
    def __init__(self, query_path, pi: ProofInfo, trace_freq: Dict[str, int]):
        super().__init__(query_path, pi)

        # TODO: this seems odd?
        self.pi = pi

        self.trace_freq = QueryInstFreq(self, trace_freq)
        self.proof_freq = QueryInstFreq(self, pi.as_frequency())
        self.sources = self.list_sources()
        self.sloop = self.list_self_loops()

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

        if qid not in self.proof_freq:
            log_warn(f"qid {qid} is not a root")
            rid = self.get_root(qid)
            if self.proof_freq[rid][qid] == 0 and not self.pi.is_skolemized(qid):
                return EditAction.ERASE
            return EditAction.NONE

        if self.pi.is_skolemized(qid):
            if self.proof_freq[qid].total_count == 0:
                # not instantiated but skolemized
                return EditAction.SKOLEMIZE
            else:
                # instantiated and skolemized
                return EditAction.DSPLIT

        if self.proof_freq[qid].total_count == 0:
            return EditAction.ERASE

        # self loop cannot be easily instantiated
        if qid in self.sources and qid not in self.sloop:
            return EditAction.INSTANTIATE

        return EditAction.NONE

    def get_actions(self, root_only=True):
        actions = dict()
        qids = self.proof_freq.freqs if root_only else self.all_qids

        for rid in qids:
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]
            if (
                t.total_count == 0
                and p.total_count == 0
                and not self.pi.is_skolemized(rid)
            ):
                # skip qids not instantiated at all
                continue
            action = self.get_available_action(rid)

            if action not in {EditAction.NONE, EditAction.ERROR}:
                actions[rid] = action

        return actions

    def get_actions_v1(self):
        qids = self.proof_freq.freqs

        res = []

        for rid in qids:
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]

            if (
                t.total_count == 0
                and p.total_count == 0
                and not self.pi.is_skolemized(rid)
            ):
                # skip qids not instantiated at all
                continue

            action = self.get_available_action(rid)
            if action in {EditAction.NONE, EditAction.ERROR}:
                continue
            if action == EditAction.ERASE:
                res.append((t.total_count, 0, rid))
            elif action == EditAction.INSTANTIATE:
                res.append((t.total_count, t.total_count / p.total_count, rid))

        res = sorted(res, reverse=True)
        res = [(rid, c, r) for c, r, rid in res]
        return res

    def get_report(self, table_limit=None):
        table = []

        for rid in self.trace_freq.order_by_freq():
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]

            if t.total_count == 0 and p.total_count == 0:
                # skip qids not instantiated at all
                continue

            action = self.get_available_action(rid)
            table.append([shorten_qid(rid), t.total_count, p.total_count, action.value])
            if not t.is_singleton():
                table.append(["- [root]", t.root_count, p.root_count, ""])
                for qid in t:
                    if qid == rid:
                        continue
                    row = ["- " + shorten_qid(qid), t[qid], p[qid], ""]
                    table.append(row)

        table.append(
            ["total", self.trace_freq.total_count, self.proof_freq.total_count, ""]
        )

        return tabulate(table, headers=["qid", "trace", "proof", "action"])

    def needed_for_skolem(self, qid):
        for pi in self.proofs:
            if qid in pi.new_skolem_funs:
                return True
        return False
    
    def debug_quantifier(self, qid):
        if qid not in self.pi.qi_infos:
            log_warn(f"qid {qid} not found in proof")
            return
        qi = self.pi.qi_infos[qid]

        for bind in qi.bindings:
            for b in bind.values():
                print(self.pi.tt.expand_def(b))

