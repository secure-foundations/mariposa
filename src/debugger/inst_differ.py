from debugger.proof_analyzer import ProofAnalyzer
from debugger.mutant_info import MutantInfo
from debugger.edit_info import EditAction
from debugger.query_loader import QueryLoader, Z3QuantWrapper
from utils.system_utils import log_debug, log_warn
from pandas import DataFrame as df


class InstGroupStat:
    def __init__(self, quant: Z3QuantWrapper):
        self.quant: Z3QuantWrapper = quant
        assert quant.is_root()
        self.root_name = quant.name

        self.__group_counts = {n: None for n in quant.group_qnames}
        self.__finalized = False

        self.total_count = 0
        self.root_count = 0

    def __getitem__(self, qid):
        return self.__group_counts[qid]

    def __setitem__(self, qid, count):
        assert not self.__finalized
        assert self.__group_counts[qid] is None
        self.__group_counts[qid] = count

    def __iter__(self):
        assert self.__finalized
        return iter(self.__group_counts)

    def is_singleton(self):
        return len(self.__group_counts) == 1

    def finalize(self):
        assert not self.__finalized
        self.__finalized = True
        for name, count in self.__group_counts.items():
            if count is None:
                self.__group_counts[name] = 0
        self.total_count = sum(self.__group_counts.values())
        self.root_count = self.__group_counts[self.root_name]


class QueryInstStat:
    def __init__(self, qi_counts, loader: QueryLoader):
        group_stats = dict()
        self.loader = loader

        for qname, count in qi_counts.items():
            if qname not in loader:
                log_warn(f"[differ] qid {qname} not found in {loader.query_path}")
                continue
            root_name = loader[qname].get_root_qname()
            quant = loader[root_name]

            if root_name not in group_stats:
                group_stats[root_name] = InstGroupStat(quant)
            group_stats[root_name][qname] = count

        for qname, quant in loader.items(root_only=True):
            if qname in group_stats:
                continue
            group_stats[qname] = InstGroupStat(quant)

        for gs in group_stats.values():
            gs.finalize()

        self.__group_stats = group_stats

    def get_group_stat(self, qname) -> InstGroupStat:
        return self.__group_stats[qname]

    def __contains__(self, qname):
        return qname in self.loader


class QueryInstDiffer(QueryLoader):
    def __init__(self, query_path: str, pa: ProofAnalyzer, ti: MutantInfo):
        super().__init__(query_path)
        self.proof = pa
        self.trace = ti

        self.proof_stats = QueryInstStat(pa.get_qi_counts(), self)
        self.trace_stats = QueryInstStat(ti.get_qi_counts(), self)

        # self.trace_missing = set()
        self.ignored = set()

        for root_name in self.list_qnames(root_only=True):
            t_group = self.trace_stats.get_group_stat(root_name)
            p_group = self.proof_stats.get_group_stat(root_name)
            if (
                t_group.total_count == 0
                and p_group.total_count == 0
                and (not self.group_should_be_skolemized(root_name))
            ):
                self.ignored.add(root_name)

    def get_root_action(self, qname):
        if qname not in self:
            log_warn(f"[differ] qid {qname} not found in {self.query_path}")
            return EditAction.NONE

        p_stat = self.proof_stats.get_group_stat(qname)
        try:
            qi_info = self.proof.get_inst_info_under_qname(qname)
            skolem_deps = qi_info.get_all_skolem_deps()
        except KeyError:
            skolem_deps = set()
            
        should_be_skolemized = self.group_should_be_skolemized(qname)

        if p_stat.total_count == 0:
            if should_be_skolemized:
                return EditAction.SKOLEMIZE
            assert len(skolem_deps) == 0
            return EditAction.ERASE

        if len(skolem_deps) == 0:
            # does not depend on any skolem functions
            return EditAction.INST_REPLACE

        usable_insts = qi_info.get_usable_insts()
        if len(usable_insts) != 0:
            # cannot remove the quantifier,
            # but can use some instances ...
            return EditAction.INST_KEEP

        if should_be_skolemized:
            return EditAction.SKOLEMIZE

        # TODO: some sanity check here?

        # print(f"[differ] qid {qname} has skolem deps but no usable insts")
        # for i in qi_info.get_all_insts():
        #     print(self.proof.dump_node(i))
        # print("")

        return EditAction.ERROR

    def group_should_be_skolemized(self, group_qname):
        assert self.is_root(group_qname)
        return any(
            (
                qname not in self.existing_sk_decls
                and self.proof.has_skolemized_qname(qname)
            )
            for qname in self[group_qname].group_qnames
        )

    def get_report(self, skip_ignored=True):
        table = []
        for qname, quant in self.items(root_only=True):
            if skip_ignored and qname in self.ignored:
                continue
            action = self.get_root_action(qname)
            t_group = self.trace_stats.get_group_stat(qname)
            p_group = self.proof_stats.get_group_stat(qname)

            table.append(
                [
                    qname,
                    t_group.total_count,
                    p_group.total_count,
                    action.value,
                ]
            )
            for dname in quant.group_qnames:
                if dname == qname:
                    continue
                table.append(
                    [
                        "-- " + dname,
                        t_group[dname],
                        p_group[dname],
                        "",
                    ]
                )
        return df(table, columns=["name", "trace count", "proof count", "action"])
