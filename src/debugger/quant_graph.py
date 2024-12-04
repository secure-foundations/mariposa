from typing import Dict
import networkx as nx
import numpy as np
from tqdm import tqdm
from utils.cache_utils import *


def sort_by_value(d):
    return {k: v for k, v in sorted(d.items(), key=lambda item: item[1], reverse=True)}


def parse_item(item, is_int=False):
    item = item.split(" ")
    qid = item[0]
    inst = item[1]
    assert inst.startswith("(")
    # assert inst.endswith("%)")
    assert inst.endswith(")")
    frac = inst[1:-1].split("/")
    if is_int:
        return qid, int(frac[0]), int(frac[1])
    return qid, float(frac[0]), float(frac[1])


class InstBlames:
    def __init__(self, qid, cost):
        self.qid = qid
        self.reasons = dict()
        self.cost = cost
        self.count = 0
        self._q = 0

    def add_reason(self, qid, p, q):
        if self.count == 0:
            assert not np.isclose(q, 0)
            self.count = q
        assert self.count == q
        if qid not in self.reasons:
            self.reasons[qid] = p
        else:
            self.reasons[qid] += p
        self._q += p
        assert self._q < self.count or np.isclose(self._q, self.count)

    def merge(self, other: "InstBlames"):
        self.cost += other.cost
        self.count += other.count
        # self._q += other._q

        for qid, p in other.reasons.items():
            if qid not in self.reasons:
                self.reasons[qid] = p
            else:
                self.reasons[qid] += p
            self._q += p
        assert np.isclose(self._q, self.count)

    def debug(self):
        print(self.qid)
        print(f"\tcount: {self.count}")
        print(f"\tcost: {self.cost}")
        for parent in self.reasons:
            print(f"\t{parent} ({self.reasons[parent]}/{self.count})")


def merge_causes(causes):
    start = causes[0]
    for profile in causes[1:]:
        start.merge(profile)
    return start


def parse_profiler_log_merged(log_path):
    collected = dict()

    for line in open(log_path, "r").readlines():
        if line == "Z3 4.13.0\n":
            continue

        line = line.strip().split(" -> ")
        qid, cost, to = parse_item(line[0])

        if cost == 0:
            # TODO: skipping zero cost?
            assert len(line) == 1
            continue

        if qid not in collected:
            collected[qid] = []

        ib = InstBlames(qid, cost)

        if len(line) == 2:
            items = line[1].split(", ")
            for item in items:
                p_qid, p, q = parse_item(item, is_int=True)
                ib.add_reason(p_qid, p, q)

        collected[qid].append(ib)

    merged = dict()
    merged_qids = set()

    for qid, profiles in collected.items():
        if len(profiles) == 0:
            continue
        if len(profiles) == 1:
            merged[qid] = profiles[0]
            continue
        cause = merge_causes(profiles)
        merged[qid] = cause
        merged_qids.add(qid)

    return merged, merged_qids


# def parse_profiler_log(log_path):
#     collected = dict()
#     blames = dict()

#     for line in open(log_path, "r").readlines():
#         if line == "Z3 4.13.0\n":
#             continue

#         line = line.strip().split(" -> ")
#         qid, cost, to = parse_item(line[0])

#         if qid not in collected:
#             collected[qid] = 0
#         else:
#             collected[qid] += 1
#             qid = f"{qid}_vv{collected[qid]}"

#         ic = InstBlames(qid, cost)

#         if len(line) == 2:
#             items = line[1].split(", ")
#             for item in items:
#                 p_qid, p, q = parse_item(item, is_int=True)
#                 ic.add_reason(p_qid, p, q)
#             blames[qid] = ic

#     return blames


def parse_freq_log(log_path):
    start = False
    counts = dict()

    for line in open(log_path, "r").readlines():
        if line == "top-instantiations=\n":
            start = True
            continue

        if not start:
            continue

        line = line.strip().split(" = ")
        qid, count = line[1], int(line[0])
        if qid not in counts:
            counts[qid] = 0
        counts[qid] += count

    counts = {k: v for k, v in counts.items() if v != 0}

    return counts


class QuantGraph:
    def __init__(self, dep_log_path, clear=False):
        self.graph: nx.DiGraph = nx.DiGraph()
        blames, merged = parse_profiler_log_merged(dep_log_path)
        self.blames: Dict[str, InstBlames] = blames
        self.__init_graph()
        ratio_cache = dep_log_path + ".ratios.pickle"

        self.sub_ratios = load_cache_or(
            ratio_cache, lambda: self.compute_all_sub_ratios(), clear
        )


    def __init_graph(self):
        for qid, qc in self.blames.items():
            self.graph.add_node(qid, count=qc.count, cost=qc.cost)

        for qid, qc in self.blames.items():
            for pid in qc.reasons:
                self.graph.add_edge(pid, qid, ratio=qc.reasons[pid] / qc.count)

    def get_sources(self):
        sources = []
        for qid in self.blames:
            if len(list(self.graph.predecessors(qid))) == 0:
                sources.append(qid)
        return sources

    def debug_qid(self, qid):
        print("qid:", qid)
        print("count:", self.blames[qid].count)
        print("cost:", self.blames[qid].cost)
        print("parents:")
        for pred in self.graph.predecessors(qid):
            print(f"\t{pred} ({self.graph[pred][qid]['ratio']})")
        print("children:")
        for succ in self.graph.successors(qid):
            print(f"\t{succ} ({self.graph[qid][succ]['ratio']})")

    def estimate_cost_v0(self, qid):
        return self.blames[qid].count

    def estimate_cost_v1(self, qid):
        return self.blames[qid].cost

    def estimate_cost_v2(self, qid):
        icount = self.blames[qid].count

        for succ in self.graph.successors(qid):
            icount += self.graph[qid][succ]["ratio"] * self.blames[succ].count

        return icount

    def compute_sub_ratios(self, start, debug=False):
        reached = nx.dfs_tree(self.graph, start).nodes

        sub_ratios = {start: 1}
        iterations = 0
        last = dict()
        converged = {start}

        while len(converged) < len(reached):
            for qid in reached:
                if qid in converged:
                    continue

                res = None

                for pred in self.graph.predecessors(qid):
                    if pred not in sub_ratios:
                        continue

                    if res is None:
                        res = 0

                    res += self.graph[pred][qid]["ratio"] * sub_ratios[pred]

                if res is None:
                    continue

                sub_ratios[qid] = res

                if qid in last and np.isclose(res, last[qid]):
                    converged.add(qid)
                else:
                    last[qid] = res

            iterations += 1

        if not debug:
            return sub_ratios

        assert set(sub_ratios.keys()) == set(reached)
        print(iterations)

        for qid in sub_ratios:
            upper_bound = 0
            for pred in self.graph.predecessors(qid):
                if pred not in sub_ratios:
                    continue
                upper_bound += self.graph[pred][qid]["ratio"]
            if qid != start:
                assert sub_ratios[qid] <= upper_bound
                print(qid, sub_ratios[qid], upper_bound, self.blames[qid].cost)

        return sub_ratios

    def compute_all_sub_ratios(self):
        res = dict()
        for qid in tqdm(self.blames):
            res[qid] = self.compute_sub_ratios(qid)
        return res

    def compute_sub_root_ratios(self, root, debug=False):
        assert root in self.trace_freq
        if self.trace_freq[root].is_singleton():
            return self.sub_ratios[root]
    
        reached = set(nx.dfs_tree(self.graph, root).nodes)
        sub_ratios = {root: 1}
        converged = {root}
        for qid in self.trace_freq[root]:
            if qid not in self.blames:
                continue
            reached.update(set(nx.dfs_tree(self.graph, qid).nodes))
            sub_ratios[qid] = 1
            converged.add(qid)

        iterations = 0
        last = dict()

        while len(converged) < len(reached):
            for qid in reached:
                if qid in converged:
                    continue

                res = None

                for pred in self.graph.predecessors(qid):
                    if pred not in sub_ratios:
                        continue

                    if res is None:
                        res = 0

                    res += self.graph[pred][qid]["ratio"] * sub_ratios[pred]

                if res is None:
                    continue

                sub_ratios[qid] = res

                if qid in last and np.isclose(res, last[qid]):
                    converged.add(qid)
                else:
                    last[qid] = res

            iterations += 1

        return sub_ratios

    def estimate_cost_v3(self, start):
        total = 0

        for (qid, ratio) in self.sub_ratios[start].items():
            assert ratio <= 1
            total += ratio * self.blames[qid].cost

        return total

    def estimate_cost_v4(self, start):
        total = 0

        for (qid, ratio) in self.sub_ratios[start].items():
            assert ratio <= 1
            if qid not in self.useless:
                # print("not logged", qid)
                discount = 1
            else:
                t, p = self.useless[qid]
                discount = (t - p) / t
            total += ratio * self.blames[qid].cost * discount

        return total

    def estimate_cost_v5(self, start):
        if start not in self.trace_freq:
            return 0

        total = 0

        for (qid, ratio) in self.compute_sub_root_ratios(start).items():
            # print(start, qid, ratio)
            assert ratio <= 1 or np.isclose(ratio, 1)
            if qid not in self.useless:
                # print("not logged", qid)
                discount = 1
            else:
                t, p = self.useless[qid]
                discount = (t - p) / t
            total += ratio * self.blames[qid].cost * discount

        return total

    def estimate_all_costs(self, cost_func):
        costs = dict()
        for qid in tqdm(self.blames):
            # print(qid)
            costs[qid] = cost_func(qid)
        # ranked = sorted(costs.items(), key=lambda x: x[1], reverse=True)
        return costs

if __name__ == "__main__":
    # g = QuantGraph("/home/yizhou7/mariposa/dbg/mimalloc--queues__page_queue_push_back.smt2/graphs/rename.13176650426009283355.txt", "freq")

    g = QuantGraph(
        "dbg/mimalloc--segment__segment_span_free_coalesce_before.smt2/graphs/rename.3245445615577937346.txt"
    )
    qid = "internal_lib!page_organization.valid_ll.?_definition"
    g.debug_qid(qid)
    print(g.estimate_cost_v3(qid, debug=True))

    # for qid, c in g.rank_by_cost(g.estimate_cost_v3).items():
    #     print(qid, c)
