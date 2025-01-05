from debugger.proof_analyzer import ProofAnalyzer
from debugger.mutant_info import MutantInfo
from debugger.edit_info import EditAction
from debugger.query_loader import QueryLoader
from utils.system_utils import log_warn
from pandas import DataFrame as df


class InstDiffer(QueryLoader):
    def __init__(self, query_path: str, pa: ProofAnalyzer, ti: MutantInfo):
        super().__init__(query_path)
        self.proof = pa
        self.trace = ti

        self.trace_counts = self.trace.get_qi_counts()
        self.proof_counts = self.proof.get_qi_counts()

        for name in self.trace_counts:
            if name not in self.all_qnames:
                log_warn(f"[differ] traced qid {name} is not directly present in {self.query_path}")

        for name in self.proof_counts:
            if name not in self.all_qnames:
                log_warn(f"[differ] proof qid {name} is not directly present in {self.query_path}")

        self.trace_missing = set()
        self.ignored = set()

        for name, count in self.trace_counts.items():
            proof_count = self.proof_counts.get(name, 0)
            if count == 0 and proof_count == 0:
                self.ignored.add(name)
                continue
            if count == 0 and proof_count != 0:
                self.trace_missing.add(name)
                continue

    def get_available_action(self, qname):
        if qname not in self.all_qnames:
            log_warn(f"[differ] qid {qname} not found in {self.query_path}")
            return EditAction.NONE

        if qname in self.proof_counts:
            qi_info = self.proof.get_inst_info_under_qname(qname)
            skolem_deps = qi_info.get_all_skolem_deps()
            assert self.proof_counts[qname] != 0
            if len(skolem_deps) == 0:
                return EditAction.INST_ERASE
            if qi_info.get_usable_insts():
                return EditAction.INST_KEEP
            return EditAction.ERROR

        if self.proof.has_skolemized_qname(qname) and qname not in self.existing_sk_decls:
            return EditAction.SKOLEMIZE
        return EditAction.ERASE

    def get_report(self, skip_ignored=True):
        table = []
        for name in self.all_qnames:
            if skip_ignored and name in self.ignored:
                continue
            action = self.get_available_action(name)
            table.append(
                [
                    name,
                    self.trace_counts.get(name, 0),
                    self.proof_counts.get(name, 0),
                    action,
                ]
            )
        return df(table, columns=["name", "trace count", "proof count", "action"])
