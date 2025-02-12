from typing import Dict
import networkx as nx
import numpy as np
from tqdm import tqdm


def sort_by_value(d):
    return {k: v for k, v in sorted(d.items(), key=lambda item: item[1], reverse=True)}


class InstBlame:
    def __init__(self, qidx, cost):
        self.qidx = qidx
        self.reasons = dict()
        self.cost = cost
        self.blamed_count = 0
        self.stat_count = None

    def add_reason(self, reason_qidx, count):
        if reason_qidx not in self.reasons:
            self.reasons[reason_qidx] = 0
        self.reasons[reason_qidx] += count
        self.blamed_count += count

    def merge(self, other):
        assert self.qidx == other.qidx
        self.cost += other.cost
        for reason_qidx, count in other.reasons.items():
            self.add_reason(reason_qidx, count)


def read_file_into_list(file_name):
    lines = open(file_name, "r").read().split("\n")
    if lines[-1] == "":
        lines = lines[:-1]
    return lines


def parse_qidx(item):
    _qidx = item
    assert _qidx[0] == "q"
    qidx = int(_qidx[1:])
    return qidx


class TheirParser:
    def __init__(self, graph_path, stats_path):
        self.qidx_to_name = dict()
        blames = self.__parse_into_blames(graph_path)
        self.__deduplicate_blames(blames)
        self.__parse_stats(stats_path)

    def __parse_into_blames(self, graph_path):
        lines = read_file_into_list(graph_path)
        line_no = 0
        assert lines[line_no] == "Z3 4.13.0"
        line_no += 1

        cur = None

        blames = []

        while line_no < len(lines):
            line = lines[line_no]
            if line[0] == "\t":
                items = line[1:].split(" ")
                qidx = parse_qidx(items[1])
                name, count = items[0], int(items[2])
                self.__register_name(qidx, name)
                cur.add_reason(qidx, count)
            else:
                items = line.split(" ")
                qidx = parse_qidx(items[1])
                name, cost = items[0], float(items[2])
                self.__register_name(qidx, name)
                cur = InstBlame(qidx, cost)
                blames.append(cur)
            line_no += 1

        return blames

    def __register_name(self, qidx, name):
        if qidx not in self.qidx_to_name:
            self.qidx_to_name[qidx] = name
        else:
            assert self.qidx_to_name[qidx] == name

    def __deduplicate_blames(self, blames):
        grouped = dict()
        for blame in blames:
            if blame.qidx not in grouped:
                grouped[blame.qidx] = []
            grouped[blame.qidx].append(blame)

        kept = dict()

        for qidx, group in grouped.items():
            non_zero_items = [b for b in group if b.cost != 0]
            if len(non_zero_items) >= 1:
                k = non_zero_items[0]
                for b in non_zero_items[1:]:
                    k.merge(b)
                kept[qidx] = k

        self.blames = kept
        kept = set(kept.keys())

        for qidx in set(self.qidx_to_name.keys()) - kept:
            del self.qidx_to_name[qidx]

    def __parse_stats(self, stats_path):
        lines = read_file_into_list(stats_path)
        line_no = 0
        start = False
        for line in lines:
            if line == "top-instantiations=":
                start = True
                continue
            if not start:
                continue
            items = line.split(" ")
            name, qidx, count = items[0], parse_qidx(items[1]), int(items[2])
            if qidx not in self.blames:
                if count != 0:
                    print(f"qidx {qidx} not found in blames", name, count)
                continue
            self.blames[qidx].stat_count = count


class TraceInstGraph:
    def __init__(self, graph_path, stats_path):
        parser = TheirParser(graph_path, stats_path)
        self.qidx_to_name = parser.qidx_to_name
        self.name_to_qidxs = dict()

        for qidx, name in self.qidx_to_name.items():
            if name not in self.name_to_qidxs:
                self.name_to_qidxs[name] = set()
            self.name_to_qidxs[name].add(qidx)

        self.blames = parser.blames
        self.graph = nx.DiGraph()

        for qidx, blame in self.blames.items():
            self.graph.add_node(qidx, name=self.qidx_to_name[qidx])

            for reason_qidx, count in blame.reasons.items():
                # assert blame.stat_count != 0 and blame.blamed_count >= count
                self.graph.add_edge(reason_qidx, qidx, ratio=count / blame.blamed_count)

    def get_qidx_checked(self, name):
        qidxs = self.name_to_qidxs[name]
        assert len(qidxs) == 1
        return list(qidxs)[0]

    def debug_name(self, name):
        qidx = self.get_qidx_checked(name)
        print(f"{name} [{qidx}]:")
        print(f"cost: {self.blames[qidx].cost}")
        print(f"stat_count: {self.blames[qidx].stat_count}")
        print(f"blamed_count: {self.blames[qidx].blamed_count}")
        print("predecessors:")
        for reason_qidx, count in self.blames[qidx].reasons.items():
            print(f"\t{self.qidx_to_name[reason_qidx]}: {count}")
        print("successors:")
        for child in self.graph.successors(qidx):
            print(f"\t{self.qidx_to_name[child]}: {self.graph[qidx][child]['ratio']}")

    def get_inst_count(self, name):
        count = 0
        for qidx in self.name_to_qidxs[name]:
            count += self.blames[qidx].stat_count
        return count

    def compute_sub_ratios(self, starts, debug=False):
        reached = set()
        sub_ratios = dict()
        converged = set()

        for qname in starts:
            if qname not in self.name_to_qidxs:
                continue
            for qidx in self.name_to_qidxs[qname]:
                reached.add(qidx)
                reached |= nx.dfs_tree(self.graph, qidx).nodes
                sub_ratios[qidx] = 1
                converged.add(qidx)

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

        if not debug:
            return sub_ratios

        assert set(sub_ratios.keys()) == set(reached)

        for qid in sub_ratios:
            upper_bound = 0
            for pred in self.graph.predecessors(qid):
                if pred not in sub_ratios:
                    continue
                upper_bound += self.graph[pred][qid]["ratio"]
            if qid not in starts:
                assert sub_ratios[qid] <= upper_bound
                print(qid, sub_ratios[qid], upper_bound, self.blames[qid].cost)

        return sub_ratios

    # def estimate_cost_v3(self, start):
    #     total = 0

    #     for (qid, ratio) in self.sub_ratios[start].items():
    #         if ratio > 1:
    #             assert np.isclose(ratio, 1)
    #             ratio = 1
    #         total += ratio * self.blames[qid].cost

    #     return total

    # def estimate_cost_v4(self, start):
    #     total = 0

    #     for (qid, ratio) in self.sub_ratios[start].items():
    #         if ratio > 1:
    #             assert np.isclose(ratio, 1)
    #             ratio = 1
    #         if qid not in self.useless:
    #             # print("not logged", qid)
    #             discount = 1
    #         else:
    #             t, p = self.useless[qid]
    #             discount = (t - p) / t
    #         total += ratio * self.blames[qid].cost * discount

    #     return total

    def estimate_cost_v5(self, start):
        if start not in self.name_to_qidxs:
            return 0

        total = 0

        for qid, ratio in self.compute_sub_root_ratios(start).items():
            if ratio > 1:
                assert np.isclose(ratio, 1)
                ratio = 1
            # if qid not in self.useless:
            #     # print("not logged", qid)
            #     discount = 1
            # else:
            total += ratio * self.blames[qid].cost

        return total
