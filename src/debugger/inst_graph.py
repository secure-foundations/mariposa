from typing import Dict
import networkx as nx
import numpy as np
from tqdm import tqdm


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


class TraceInstGraph(nx.DiGraph):
    def __init__(self, graph_path, stats_path):
        super().__init__()
        parser = TheirParser(graph_path, stats_path)
        self.qidx_to_name = parser.qidx_to_name
        self.name_to_qidxs = dict()

        for qidx, name in self.qidx_to_name.items():
            if name not in self.name_to_qidxs:
                self.name_to_qidxs[name] = set()
            self.name_to_qidxs[name].add(qidx)

        self.blames = parser.blames

        for qidx, blame in self.blames.items():
            self.add_node(qidx, name=self.qidx_to_name[qidx])

            for reason_qidx, count in blame.reasons.items():
                # assert blame.stat_count != 0 and blame.blamed_count >= count
                self.add_edge(reason_qidx, qidx, ratio=count / blame.blamed_count)

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

    def compute_sub_ratios(self, starts, debug=False, bootstrap=dict()):
        class Inter:
            def __init__(self, graph, starts, debug):
                self.ratios = dict()
                reachable = set()
                self.converged = set()
                self.iterations = 0
                self.graph = graph
                self.debug = debug

                for qname in starts:
                    if qname not in graph.name_to_qidxs:
                        continue
                    for qidx in graph.name_to_qidxs[qname]:
                        reachable.add(qidx)
                        reachable |= nx.dfs_tree(self.graph, qidx).nodes
                        self.ratios[qidx] = 1
                        self.converged.add(qidx)

                self.reachable = frozenset(reachable)

                for qidx in bootstrap:
                    assert qidx in self.reachable
                    assert 0 <= bootstrap[qidx] <= 1
                    self.ratios[qidx] = bootstrap[qidx]

            def has_converged(self):
                return len(self.converged) == len(self.reachable)
            
            def __update(self, qidx, curr):
                if np.isclose(curr, 1, atol=1e-3):
                    curr = 1

                assert 0 <= curr <= 1
                assert qidx not in self.converged
                if qidx not in self.ratios:
                    self.ratios[qidx] = curr
                    return

                prev = self.ratios[qidx]
                count = self.graph.blames[qidx].stat_count

                if (np.isclose(prev*count, curr*count, atol=1) or 
                    np.isclose(prev, curr, atol=1e-4)):
                    self.converged.add(qidx)

                self.ratios[qidx] = curr

            def __iterate(self):
                for qidx in self.reachable:
                    if qidx in self.converged:
                        continue

                    buf = []

                    for pred in self.graph.predecessors(qidx):
                        if pred not in self.ratios:
                            continue
                        buf.append((self.graph[pred][qidx]["ratio"], self.ratios[pred]))

                    if len(buf) == 0:
                        continue

                    buf = np.array(buf)
                    res = np.sum(buf[:, 0] * buf[:, 1])

                    self.__update(qidx, res)

                self.iterations += 1

            def compute(self):
                while not self.has_converged():
                    self.__iterate()
                    if self.debug:
                        print(f"iteration {self.iterations} {len(self.converged)} / {len(self.reachable)}")

                ratios = self.ratios
                self.ratios = None

                if self.debug:
                    for qid in ratios:
                        upper_bound = 0
                        for pred in self.graph.predecessors(qid):
                            if pred not in ratios:
                                continue
                            upper_bound += self.graph[pred][qid]["ratio"]
                        upper_bound = min(upper_bound, 1)
                        if qid not in starts:
                            assert ratios[qid] <= upper_bound
                        # print(qid, ratios[qid], upper_bound, self.graph.blames[qid].cost)

                return ratios

        i = Inter(self, starts, debug)
        ratios = i.compute()
        i = None
        return ratios

    def aggregate_scores(self, sub_ratios):
        if len(sub_ratios) == 0:
            return 0
        scores = []
        for qidx, ratio in sub_ratios.items():
            scores.append((ratio, self.blames[qidx].stat_count))
        scores = np.array(scores)
        return np.sum(scores[:, 0] * scores[:, 1])
