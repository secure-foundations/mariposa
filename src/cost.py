from typing import Dict
import networkx as nx
import numpy as np
from tqdm import tqdm


def sort_by_value(d):
    return {k: v for k, v in sorted(d.items(), key=lambda item: item[1], reverse=True)}


def parse_item(item):
    item = item.split(" ")
    qid = item[0]
    inst = item[1]
    assert inst.startswith("(")
    # assert inst.endswith("%)")
    assert inst.endswith(")")
    frac = inst[1:-1].split("/")
    return qid, float(frac[0]), float(frac[1])


class InstCause:
    def __init__(self, qid, cost):
        self.qid = qid
        self.parents = dict()
        self.cost = cost
        self.count = 0
        self._q = 0

    def add_cause(self, qid, p, q):
        if self.count == 0:
            assert not np.isclose(q, 0)
            self.count = q
        assert self.count == q
        if qid not in self.parents:
            self.parents[qid] = p
        else:
            self.parents[qid] += p
        self._q += p
        assert self._q < self.count or np.isclose(self._q, self.count)

    def merge(self, other: "InstCause"):
        self.cost += other.cost
        self.count += other.count
        # self._q += other._q

        for qid, p in other.parents.items():
            if qid not in self.parents:
                self.parents[qid] = p
            else:
                self.parents[qid] += p
            self._q += p
        assert np.isclose(self._q, self.count)

    def debug(self):
        print(self.qid, self.count, self.cost)
        for parent in self.parents:
            print(f"\t{parent} ({self.parents[parent]}/{self.count})")


def merge_causes(causes):
    start = causes[0]
    for profile in causes[1:]:
        start.merge(profile)
    return start


def parse_profiler_log(log_path):
    collected = dict()

    for line in open(log_path, "r").readlines():
        if line == "Z3 4.13.0\n":
            continue
        line = line.strip().split(" -> ")
        current, ct, to = parse_item(line[0])

        if np.isclose(ct, 0):
            continue

        if current not in collected:
            collected[current] = []

        ic = InstCause(current, ct)

        if len(line) == 2:
            items = line[1].split(", ")
            for item in items:
                qid, p, q = parse_item(item)
                ic.add_cause(qid, p, q)

        collected[current].append(ic)

    merged = dict()

    for qid, profiles in collected.items():
        if len(profiles) == 0:
            continue
        if len(profiles) == 1:
            merged[qid] = profiles[0]
            continue
        cause = merge_causes(profiles)
        merged[qid] = cause

    return merged


class QuantGraph:
    def __init__(self, log_path) -> None:
        self.graph: nx.DiGraph = nx.DiGraph()
        self.causes: Dict[str, InstCause] = parse_profiler_log(log_path)
        self.__init_graph()

    def __init_graph(self):
        for qid, qc in self.causes.items():
            self.graph.add_node(qid, count=qc.count, cost=qc.cost)

        for qid, qc in self.causes.items():
            for parent in qc.parents:
                self.graph.add_edge(parent, qid, weight=qc.parents[parent])

    def rank_by_cost(self, cost_func):
        costs = dict()
        for qid in tqdm(self.causes):
            # print(qid)
            costs[qid] = cost_func(qid)
        ranked = sorted(costs.items(), key=lambda x: x[1], reverse=True)
        ranked = {qid: (i, c) for i, (qid, c) in enumerate(ranked)}
        return ranked

    def estimate_cost_v0(self, qid):
        return self.causes[qid].count

    def estimate_cost_v1(self, qid):
        return self.causes[qid].cost

    def estimate_cost_v2(self, qid):
        icount = self.causes[qid].count

        for succ in self.graph.successors(qid):
            icount += self.graph[qid][succ]["weight"]

        return icount

    def estimate_cost_v3(self, start):
        icount = self.causes[start].count
        dfs = nx.dfs_tree(self.graph, start)

        sub_counts = {start: icount}
        iterations = 0
        last = dict()
        converged = {start}

        while len(converged) < len(dfs.nodes):
            for qid in dfs.nodes:
                if qid in converged:
                    continue

                res = None

                for pred in self.graph.predecessors(qid):
                    if pred not in sub_counts:
                        continue

                    if res is None:
                        res = 0

                    if self.causes[pred].count != 0:
                        res += (
                            self.graph[pred][qid]["weight"]
                            * sub_counts[pred]
                            / self.causes[pred].count
                        )

                if res is None:
                    continue

                sub_counts[qid] = res

                if qid in last and np.isclose(res, last[qid], atol=1):
                    converged.add(qid)
                else:
                    last[qid] = res

            iterations += 1

        for qid in sort_by_value(sub_counts):
            assert int(sub_counts[qid]) <= int(self.causes[qid].count)

        total = sum(sub_counts.values())
        return total


def main():
    g = QuantGraph("woot2")
    qid = "internal_lib!page_organization.valid_ll.?_definition"
    # qid = "internal_vstd__ptr__PointsTo<lib!types.SegmentHeader.>_unbox_axiom_definition"

    # ranked = g.rank_by_cost(g.estimate_cost_v1)
    # ranked = g.rank_by_cost(g.estimate_cost_v2)
    ranked = g.rank_by_cost(g.estimate_cost_v3)

    # for qid in ranked:
    #     print(qid, ranked[qid])
    # print(ranked[qid])

    # e = g.estimate_cost_v3(qid)
    # print(e)


if __name__ == "__main__":
    main()
