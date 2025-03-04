import os
from typing import Dict, List, Set
from debugger.proof_analyzer import ProofAnalyzer
from debugger.mutant_info import MutantInfo
from debugger.edit_info import EditAction, EditInfo
from debugger.inst_graph import TraceInstGraph, TheirParser
from debugger.query_editor import QueryEditor
from debugger.query_loader import QueryLoader, Z3QuantWrapper
from utils.system_utils import log_debug, log_warn
from pandas import DataFrame


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

    def items(self):
        assert self.__finalized
        return self.__group_counts.items()

    def keys(self):
        assert self.__finalized
        return self.__group_counts.keys()

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


def choose_action(actions):
    if EditAction.ERASE in actions:
        return EditAction.ERASE
    if EditAction.INST_REPLACE in actions:
        return EditAction.INST_REPLACE
    if EditAction.INST_KEEP in actions:
        return EditAction.INST_KEEP
    if EditAction.SKOLEMIZE in actions:
        return EditAction.SKOLEMIZE
    return EditAction.NONE


class InformedEditor(QueryEditor):
    def __init__(self, query_path: str, pa: ProofAnalyzer, ti: MutantInfo):
        super().__init__(query_path)
        assert isinstance(pa, ProofAnalyzer)
        self.proof: ProofAnalyzer = pa
        assert isinstance(ti, MutantInfo)
        self.trace: MutantInfo = ti

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

        self.__root_actions: Dict[str, Set[EditAction]] = dict()

        for qname in self.list_qnames(root_only=True):
            self.__root_actions[qname] = self.__get_root_actions(qname)

    def __get_root_actions(self, qname) -> Set[EditAction]:
        p_stat = self.proof_stats.get_group_stat(qname)
        should_be_skolemized = self.group_should_be_skolemized(qname)
        allowed = set()

        if should_be_skolemized:
            allowed.add(EditAction.SKOLEMIZE)

        if not self.proof.has_inst_info(qname) or p_stat.total_count == 0:
            if not should_be_skolemized:
                return {EditAction.ERASE}
            return allowed

        qi_info = self.proof.get_inst_info_under_qname(qname)
        skolem_deps = qi_info.get_all_skolem_deps()

        if len(skolem_deps) == 0:
            # does not depend on any skolem functions
            # we should be able to instantiate it all
            allowed.add(EditAction.INST_REPLACE)
            allowed.add(EditAction.INST_KEEP)
            return allowed

        usable_insts = qi_info.get_feasible_insts()

        if len(usable_insts) != 0:
            allowed.add(EditAction.INST_KEEP)
            # cannot remove the quantifier,
            # but can use some instances ...
            return allowed

        if len(allowed) == 0:
            # print(qname, len(usable_insts), len(skolem_deps), should_be_skolemized)
            return {EditAction.ERROR}

        return allowed

    def group_should_be_skolemized(self, group_qname):
        assert self.is_root(group_qname)
        return any(
            (
                qname not in self.existing_sk_decls
                and self.proof.has_skolemized_qname(qname)
            )
            for qname in self[group_qname].group_qnames
        )

    def get_singleton_actions(self, skip_ignored=True, skip_infeasible=True) -> List:
        results = []
        for qname, actions in self.__root_actions.items():
            if skip_ignored and qname in self.ignored:
                continue
            if skip_infeasible and EditAction.ERROR in actions:
                continue
            for action in actions:
                results.append({qname: action})
        return results

    def get_quant_actions(self, qname) -> Set[EditAction]:
        if qname not in self:
            log_warn(f"[differ] qid {qname} not found in {self.query_path}")
            return {EditAction.NONE}
        return self.__root_actions[qname]

    def edit_by_qname(self, qname, action=None):
        if action is None:
            action = choose_action(self.__get_root_actions(qname))

        if action in {EditAction.ERROR, EditAction.NONE}:
            log_warn(f"[edit] qid {qname} has no feasible actions")
            return False

        if action == EditAction.ERASE:
            return self._erase_qid(qname)

        if action in {EditAction.INST_KEEP, EditAction.INST_REPLACE}:
            qii = self.proof.get_inst_info_under_qname(qname)
            insts = []
            for inst in qii.get_feasible_insts():
                insts.append("(assert " + self.proof.dump_node(inst) + ")")
            erase = EditAction.INST_REPLACE == action
            return self._instantiate_qid(qname, insts, erase=erase)

        if action == EditAction.SKOLEMIZE:
            return self._skolemize_qid(qname)

        log_warn(f"[edit] unhandled action {action} for qid {qname}")
        return False

    def edit_by_info(self, ei: EditInfo):
        ok = True
        for qname, action in ei.items():
            ok &= self.edit_by_qname(qname, action)
        if not ok:
            self._reset_state()
            return False
        return self.save(ei.query_path)

    def debug_qanme(self, qname):
        if qname not in self:
            log_warn(f"[debug] qid {qname} not found in {self.query_path}")
            return
        if qname in self.ignored:
            log_warn(f"[debug] qid {qname} is ignored")
            return

        qii = self.proof.get_inst_info_under_qname(qname)

        for inst in qii.get_all_insts():
            print(self.proof.dump_node(inst))

        deps = qii.get_all_skolem_deps()

        if len(deps) == 0:
            return

        for dep in deps:
            print(dep)

    def get_inst_report(self, skip_ignored=True):
        table = []
        for qname, quant in self.items(root_only=True):
            if skip_ignored and qname in self.ignored:
                continue
            # action = self.get_quant_action(qname)
            t_group = self.trace_stats.get_group_stat(qname)
            p_group = self.proof_stats.get_group_stat(qname)
            skolem = self.group_should_be_skolemized(qname)

            table.append(
                [
                    qname,
                    t_group.total_count,
                    p_group.total_count,
                    skolem,
                ]
            )
        return DataFrame(
            table, columns=["qname", "trace_count", "proof_count", "skolem"]
        )

    def get_sub_ratios(self, clear):
        from tqdm import tqdm

        sub_ratios = dict()
        graph = self.trace.get_trace_graph(clear)
        for root_name in tqdm(self.list_root_qnames()):
            t_group = self.trace_stats.get_group_stat(root_name)
            res = graph.compute_sub_ratios(t_group.keys())
            sub_ratios[root_name] = res
        return sub_ratios

    def list_root_qnames(self, skip_ignored=True):
        for root_name in self.list_qnames(root_only=True):
            if skip_ignored and root_name in self.ignored:
                continue
            yield root_name

    def choose_qanme_to_skolemize(self) -> str:
        consequences = self.proof.get_skolem_consequences()

        if len(consequences) == 0:
            return None
        # assert len(consequences) > 0

        creating_insts = dict()
        # impacting_quants = dict()
        chosen = None
        max_insts = 0

        for skv in consequences:
            creating_insts[skv] = sum(consequences[skv].values())
            if creating_insts[skv] > max_insts:
                chosen = skv
                max_insts = creating_insts[skv]

        return chosen
