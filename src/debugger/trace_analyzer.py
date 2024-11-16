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

    def get_report(self, version):
        if version == 1:
            return self.get_report_v1()
        elif version == 2:
            return self.get_report_v2()
        elif version == 3:
            return self.get_report_v3()
        else:
            log_warn(f"[report] unknown report version {version}")

    def get_report_v1(self):
        table = []

        for rid in self.trace_freq.order_by_freq():
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]

            action = self.get_available_action(rid)
            table.append(
                [
                    shorten_qid(rid),
                    t.total_count,
                    p.total_count,
                    action.value,
                    self.quants[rid].get_size(),
                ]
            )
            if not t.is_singleton():
                table.append(["- [root]", t.root_count, p.root_count, "", ""])
                for qid in t:
                    if qid == rid:
                        continue
                    row = ["- " + shorten_qid(qid), t[qid], p[qid], "", ""]
                    table.append(row)

        table.append(
            [
                "total",
                self.trace_freq.total_count,
                self.proof_freq.total_count,
                self.quants[rid].get_size(),
                "",
            ]
        )

        return tabulate(table, headers=["qid", "trace", "proof", "action", "size"])

    def get_report_v2(self):
        qids = self.proof_freq.freqs

        res = dict()

        for rid in qids:
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]

            # skip qids not instantiated at all
            if (
                t.total_count == 0
                and p.total_count == 0
                and not self.pi.is_skolemized(rid)
            ):
                continue

            action = self.get_available_action(rid)

            impact = (t.root_count - p.root_count) * self.quants[rid].get_size()
            res[rid] = (impact, t.is_singleton(), action.value, p.root_count)

        res = sorted(res.items(), key=lambda x: x[1], reverse=True)
        table = []

        for rid, (impact, singleton, action, pi_count) in res:
            table.append([shorten_qid(rid), impact, singleton, action, pi_count])

        return tabulate(table, headers=["qid", "size", "singleton", "action", "pi count"])

    def get_report_v3(self):
        qids = self.proof_freq.freqs

        res = dict()
        
        weights = dict()

        for line in open("report").readlines():
            qid, weight = line.strip().split(":")
            weights[qid] = int(weight)

        for rid in qids:
            t = self.trace_freq[rid]
            p = self.proof_freq[rid]

            # skip qids not instantiated at all
            if (
                t.total_count == 0
                and p.total_count == 0
                and not self.pi.is_skolemized(rid)
            ):
                continue

            action = self.get_available_action(rid)

            impact = (t.root_count - p.root_count) * weights[rid]
            res[rid] = (impact, t.is_singleton(), action.value, p.root_count)

        res = sorted(res.items(), key=lambda x: x[1], reverse=True)
        table = []

        for rid, (impact, singleton, action, pi_count) in res:
            table.append([shorten_qid(rid), impact, singleton, action, pi_count])

        return tabulate(table, headers=["qid", "size", "singleton", "action", "pi count"])


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
