from typing import Dict, List

from tabulate import tabulate
from debugger.query_writer import QueryWriter, add_qids_to_query
from debugger.z3_utils import collapse_sexpr
from proof_reader import InstError, ProofInfo, QueryLoader
from utils.system_utils import log_check, log_info, log_warn


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


def is_prelude_qid(qid):
    return (
        qid.startswith("prelude_")
        or qid.startswith("internal_vstd")
        or qid.startswith("internal_core")
    )


class TraceAnalyzer(QueryLoader):
    def __init__(self, query_path, proofs: List[ProofInfo]):
        super().__init__(query_path)
        log_check(len(proofs) != 0, "no proofs provided")
        self.proofs = proofs
        self.pf_freqs = []

        for proof in proofs:
            freq = proof.as_frequency()
            freq = self.group_frequencies(freq)
            self.pf_freqs.append(freq)

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
        return res

    def get_proof_inst_counts(self, rid, qid=None):
        res = []
        for i, pf_freq in enumerate(self.pf_freqs):
            if qid is not None:                    
                res.append(pf_freq[rid][qid])
                if self.proofs[i].is_skolemized(qid):
                    res.append("s")
                else:
                    res.append("-")
            else:
                res.append(pf_freq[rid].total_count)
                if self.proofs[i].is_skolemized(rid):
                    res.append("s")
                else:
                    res.append("-")
        return res

    def get_proof_total_inst_counts(self):
        gsums = [0] * len(self.proofs)
        for i, pi in enumerate(self.proofs):
            pf = pi.as_frequency()
            for rid in pf:
                gsums[i] += pf[rid]
        return gsums

    def get_report(self, trace_freq: Dict[str, int], table_limit):
        report = "traced instantiations:\n"
        t_freq = self.group_frequencies(trace_freq)
        missing = self.__get_missing_rids(t_freq)
        group_sums = [0] * (1 + len(self.proofs) * 2)

        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        table = []

        for rid, tg in t_freq:
            if tg.total_count == 0:
                continue
            conflict = "c" if self.has_conflicts(rid) else ""
            row = [shorten_qid(rid), conflict, tg.total_count]
            group_sums[0] += tg.total_count
            ptotals = self.get_proof_inst_counts(rid)
            for i in range(len(self.proofs)):
                group_sums[i * 2 + 1] += ptotals[i * 2]
            if tg.is_singleton():
                table.append(row + ptotals)
                continue

            table.append(row)
            table.append(
                ["- [root]", "", tg.root_count] + self.get_proof_inst_counts(rid, rid)
            )
            for qid in tg:
                if qid == rid:
                    continue
                row = ["- " + shorten_qid(qid), "", tg[qid]] + self.get_proof_inst_counts(
                    rid, qid
                )
                table.append(row)

        headers = ["QID", "C", "T"]

        for i in range(len(self.proofs)):
            headers.append(f"P{i}#")
            headers.append("")

        if len(table) > table_limit:
            row = [f"... eliding {len(table) - table_limit} more rows ..."] + [
                "..."
            ] * (len(headers) - 1)
            table = table[:table_limit]
            table.append(row)
        table.append(["total", ""] + group_sums)
        report += tabulate(table, headers=headers)

        table = []
        for rid in missing:
            row = [shorten_qid(rid)] + self.get_proof_inst_counts(rid)
            table.append(row)

        headers = ["QID"] + [f"P{i}" for i in range(len(self.proofs))]

        if len(table) > table_limit:
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
    
    def needed_for_skolem(self, qid):
        for pi in self.proofs:
            if qid in pi.new_skolem_funs:
                return True
        return False

    def select_qids_v1(self, trace_freq: Dict[str, int], top_n):
        t_freq = self.group_frequencies(trace_freq)
        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        selected = set()

        for rid, tg in t_freq:
            if len(selected) >= top_n:
                break
            if tg.total_count == 0:
                continue

            useless = any([c == 0 for c in self.get_proof_inst_counts(rid)])
            if not self.needed_for_skolem(rid) and useless:
                selected.add(rid)

        return selected

    def select_qids_v2(self, trace_freq: Dict[str, int], top_n):
        t_freq = self.group_frequencies(trace_freq)
        t_freq: List[(str, GroupInstFreq)] = sorted(
            t_freq.items(), key=lambda x: x[1].total_count, reverse=True
        )
        selected = set()
        for rid, tg in t_freq:
            if len(selected) >= top_n:
                break

            if tg.total_count == 0:
                continue

            # skip prelude qids
            if is_prelude_qid(rid):
                continue

            if self.needed_for_skolem(rid):
                log_info(f"skolem needed: {rid}")
                continue

            # useless = all([c == 0 for c in self.get_proof_inst_counts(rid)])
            useless = any([c == 0 for c in self.get_proof_inst_counts(rid)])

            if useless:
                selected.add(rid)
                continue

            for qid in tg:
                useless = all([c == 0 for c in self.get_proof_inst_counts(rid, qid)])
                # if there is a nested quantifier that is not needed
                if (
                    tg[qid] != 0
                    and useless
                    and not is_prelude_qid(qid)
                    and not self.needed_for_skolem(qid)
                ):
                    selected.add(qid)

        return selected

