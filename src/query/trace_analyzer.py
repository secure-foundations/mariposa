from typing import Dict, List

from tabulate import tabulate
from query.instantiater import ProofInfo, QueryLoader
from utils.system_utils import log_check, log_info

# trace_qids
# traced = self.ins.accumulate_inst_count(trace_qids)


class GroupInstFreq:
    def __init__(self, rid):
        self.rid = rid
        self.group = dict()
        self.__finalized = False
        self.total_count = 0
        self.root_count = 0

    def __getitem__(self, qid):
        return self.group[qid]

    def __setitem__(self, qid, count):
        self.group[qid] = count

    def __iter__(self):
        assert self.__finalized
        return iter(self.group)

    def is_singleton(self):
        return len(self.group) == 1

    def finalize(self):
        assert not self.__finalized
        self.__finalized = True
        self.total_count = sum(self.group.values())
        self.root_count = self.group[self.rid]

    def is_user_only(self):
        if self.is_singleton():
            return self.rid.startswith("user_")

        for qid in self.group:
            if qid != self.rid and not qid.startswith("user_"):
                return False
        return True


def shorten_qid(qid):
    if len(qid) <= 75:
        return qid
    return qid[:75] + "..."


class TraceAnalzyer(QueryLoader):
    def __init__(self, query_path, proofs: List[ProofInfo]):
        super().__init__(query_path)
        log_check(len(proofs) != 0, "no proofs provided")
        self.proofs = proofs
        self.pf_freqs = []
        self.sk_funs = set()

        for proof in proofs:
            freq = proof.as_frequency()
            freq = self.group_frequencies(freq)
            self.pf_freqs.append(freq)
            self.sk_funs |= set(proof.sk_funs)

    def needed_for_skolem(self, qid):
        target = "$!skolem_" + qid + "!"
        for sk_fun in self.sk_funs:
            if target in sk_fun:
                return True
        return False

    def group_frequencies(self, freq: Dict[str, int]) -> Dict[str, GroupInstFreq]:
        res = dict()
        for qid in self.all_qids:
            if qid not in freq:
                freq[qid] = 0
            rid = self.get_root(qid)
            if rid not in res:
                res[rid] = GroupInstFreq(rid)
            res[rid][qid] = freq[qid]
        for rid in res:
            res[rid].finalize()
        assert self.root_qids == set(res.keys())
        return res

    def get_proof_inst_counts(self, rid, qid=None):
        res = []
        for pf_freq in self.pf_freqs:
            if qid is not None:
                res.append(pf_freq[rid][qid])
            else:
                res.append(pf_freq[rid].total_count)
        return res

    def get_report(self, trace_freq: Dict[str, int], table_limit):
        report = "traced instantiations:\n"
        t_freq = self.group_frequencies(trace_freq)
        missing = self.__get_missing_rids(t_freq)
        group_sums = [0] * (1 + len(self.proofs))

        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        table = []

        for rid, tg in t_freq:
            if tg.total_count == 0:
                continue
            row = [shorten_qid(rid), tg.total_count]
            group_sums[0] += tg.total_count
            ptotals = self.get_proof_inst_counts(rid)
            for i in range(len(ptotals)):
                group_sums[i + 1] += ptotals[i]

            if tg.is_singleton():
                table.append(row + ptotals)
                continue

            table.append(row)
            table.append(
                ["- [root]", tg.root_count] + self.get_proof_inst_counts(rid, rid)
            )
            for qid in tg:
                if qid == rid:
                    continue
                row = ["- " + shorten_qid(qid), tg[qid]] + self.get_proof_inst_counts(
                    rid, qid
                )
                table.append(row)

        headers = ["QID", "T"] + [f"P{i}" for i in range(len(self.proofs))]

        if len(table) > table_limit:
            row = [f"... eliding {len(table) - table_limit} more rows ..."] + [
                "..."
            ] * (len(headers) - 1)
            table = table[:table_limit]
            table.append(row)
        table.append(["total"] + group_sums)
        report += tabulate(table, headers=headers)

        table = []
        for rid in missing:
            row = [shorten_qid(rid)] + self.get_proof_inst_counts(rid)
            table.append(row)

        if len(table) > table_limit:
            headers = ["QID"] + [f"P{i}" for i in range(len(self.proofs))]
            row = [f"... eliding {len(table) - table_limit} more rows ..."] + [
                "..."
            ] * (len(headers) - 1)
            table = table[:table_limit]
            table.append(row)

        if len(table) != 0:
            # log_info("missing instantiations:")
            report += "\n\nmissing instantiations:\n"
            report += tabulate(table, headers=headers)

        return report

    def __get_missing_rids(self, traced_qids: Dict[(str, GroupInstFreq)]):
        used, res = set(), set()
        for pf_freq in self.pf_freqs:
            for rid, pg in pf_freq.items():
                if pg.total_count != 0:
                    used.add(rid)
        for rid, tg in traced_qids.items():
            if tg.total_count == 0 and rid in used:
                res.add(rid)
        return res

    def select_qids_v1(self, trace_freq: Dict[str, int], top_n):
        t_freq = self.group_frequencies(trace_freq)
        # missing = self.__get_missing_rids(t_freq)
        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        selected = set()
        for rid, tg in t_freq:
            if tg.total_count == 0:
                continue
            necessary = all([c != 0 for c in self.get_proof_inst_counts(rid)])

            if self.needed_for_skolem(rid):
                continue

            if not necessary:
                selected.add(rid)

            if len(selected) >= top_n:
                break

        return selected

    def select_qids_v2(self, trace_freq: Dict[str, int], top_n):
        t_freq = self.group_frequencies(trace_freq)
        # missing = self.__get_missing_rids(t_freq)
        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        selected = set()
        for rid, tg in t_freq:
            if tg.total_count == 0:
                continue

            # skip prelude qids
            if rid.startswith("prelude_"):
                continue

            if len(selected) >= top_n:
                break

            if self.needed_for_skolem(rid):
                continue

            useless = all([c == 0 for c in self.get_proof_inst_counts(rid)])

            if rid.startswith("user_") and useless:
                selected.add(rid)
                continue

            if tg.is_user_only() and useless:
                selected.add(rid)
                continue

            for qid in tg:
                useless = all([c == 0 for c in self.get_proof_inst_counts(rid, qid)])
                # if there is a nested quantifier that is not needed
                if (
                    tg[qid] != 0
                    and useless
                    and qid.startswith("user_")
                    and not self.needed_for_skolem(qid)
                ):
                    selected.add(qid)

        return selected

    # def accumulate_inst_count(self, trace) -> Dict[str, GroupInstCounter]:
    #     roots = dict()
    #     # attribute the count to the root quantifier
    #     for qid, count in trace.items():
    #         root = self.get_root(qid)
    #         if root not in roots:
    #             roots[root] = GroupInstCounter(root)
    #         roots[root][qid] = count
    #     for qid in roots:
    #         roots[qid].finalize()
    #     return roots
