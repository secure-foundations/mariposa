from z3 import *
from debugger.z3_utils import Z3AstVisitor
from utils.system_utils import log_warn


class SubsMapper(Z3AstVisitor):
    def __init__(self, qref: QuantifierRef):
        super().__init__()
        self.app_map = dict()
        self.unmapped = 0

        self.num_vars = qref.num_vars()
        self.__find_apps(qref, 0)

        mapped = set()
        self.app_map = {k: v for k, v in self.app_map.items() if v != []}

        for _, idxs in self.app_map.items():
            for idx, _ in idxs:
                mapped.add(idx)

        for i in range(self.num_vars):
            if i not in mapped:
                self.unmapped += 1

        # for fun, idxs in self.app_map.items():
        #     print(f"Mapping for {fun}: {idxs}")

    def __find_apps(self, exp, offset):
        if self.visit(exp) or is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self.__find_apps(exp.body(), offset + exp.num_vars())
            return

        fun, idxs = exp.decl().name(), []

        for i, c in enumerate(exp.children()):
            if not is_var(c):
                continue
            idx = get_var_index(c)
            idx = offset - idx - 1
            # idx < 0: from a nested quantifier
            # idx >= self.num_vars: from a parent quantifier
            if idx < 0 or idx >= self.num_vars:
                continue
            idxs.append((idx, i))

        if fun in self.app_map:
            idxs_ = self.app_map[fun]
            consistent = len(idxs_) == len(idxs)
            if consistent:
                consistent = all([idxs[i] == idxs_[i] for i in range(len(idxs))])
            if not consistent:
                self.app_map[fun] = []
        else:
            # print(f"Found new mapping for {fun}: {idxs}")
            self.app_map[fun] = idxs

        for c in exp.children():
            self.__find_apps(c, offset)

    def map_inst(self, exp):
        assert self.unmapped == 0
        var_bindings = dict()
        self._match_vars(exp, var_bindings)
        failed = any([i not in var_bindings for i in range(self.num_vars)])
        if failed:
            return None
        return var_bindings

    def _match_vars(self, exp, bindings):
        if is_const(exp) or is_var(exp):
            return

        if is_quantifier(exp):
            self._match_vars(exp.body(), bindings)
            return

        fun = exp.decl().name()

        if fun in self.app_map:
            idxs = self.app_map[fun]
            for i, j in idxs:
                bindings[i] = exp.children()[j]

        for c in exp.children():
            self._match_vars(c, bindings)
