from copy import deepcopy
import math
import os, random, subprocess
from base.solver import RCode, Solver
from utils.query_utils import format_query, get_asserts, key_set
from utils.system_utils import *

class CoreCompleter:
    def __init__(self, input_query, core_query, solver, output_query, timeout):
        log_check(os.path.exists(input_query), f"input query {input_query} does not exist")

        self.solver: Solver = solver
        self.time_limit = timeout

        name_hash = get_name_hash(input_query)
        self.name_hash = name_hash
        self.exp_path = f"gen/{name_hash}.core.comp.smt2"

        self._setup_diff(input_query, core_query)
        self._setup_hint(core_query)
        self.try_complete_core(output_query)

    def _setup_hint(self, hint_path):
        hint_commands = open(hint_path).readlines()

        i = len(hint_commands) - 1
        while i >= 0:
            if hint_commands[i].startswith("(check-sat)"):
                break
            i -= 1
        i -= 1
        # lets try to keep the goal as the second last command 
        log_check(i > 0, "hint has not enough commands?")
        self.prelude = hint_commands[:i]
        self.postlude = hint_commands[i:]
    
    def _setup_diff(self, orig_path, hint_path):
        self.fmt_path = f"gen/{self.name_hash}.fmt.smt2"

        if not os.path.exists(self.fmt_path):
            format_query(orig_path, self.fmt_path)
    
        orig_asserts = get_asserts(self.fmt_path)
        hint_asserts = get_asserts(hint_path)

        is_subset = key_set(hint_asserts).issubset(key_set(orig_asserts))
        log_check(is_subset, "hint is not a subset of orig")
        log_check(len(hint_asserts) > 0, "hint has no asserts")

        diff_asserts = []

        for i in orig_asserts.keys() - hint_asserts.keys():
            diff_asserts.append(orig_asserts[i] + "\n")

        self.diff_asserts = diff_asserts

    def _write_exp(self, next_diff):
        exp_file = open(self.exp_path, "w")
        exp_file.writelines(self.prelude)
        exp_file.writelines(next_diff)
        exp_file.writelines(self.postlude)
        exp_file.close()

    def clear_temp_files(self):
        remove_file(self.exp_path)
        remove_file(self.fmt_path)

    def binary_search(self, cur_diff):
        if len(cur_diff) <= 4:
            return cur_diff

        logn = int(math.log(len(cur_diff), 2))
        max_trials = logn * 16
        trails = 0

        while trails < max_trials:
            next_diff = random.sample(cur_diff, k=len(cur_diff) // 2)
            log_info(f"trying diff len: {len(next_diff)}, trails: {trails+1}/{max_trials}")
            self._write_exp(next_diff)
            rc, et = self.solver.run(self.exp_path, self.time_limit)

            if rc == RCode.UNSAT:
                self.time_limit = min(self.time_limit, int(et / 800 + 1))
                log_info(f"narrowed to diff len: {len(next_diff)}")
                log_info(f"time limit adjusted to: {self.time_limit}")
                # just in case something weird happens
                self.working_diff = deepcopy(next_diff)
                return next_diff
            trails += 1
        return cur_diff

    def try_complete_core(self, output_path):
        cur_diff = self.diff_asserts

        while 1:
            next_diff = self.binary_search(cur_diff)
            if len(next_diff) == len(cur_diff):
                log_info(f"quitting bisection search at diff len: {len(cur_diff)}" )
                break
            cur_diff = next_diff

        self.clear_temp_files()
        log_check(len(cur_diff) < len(self.diff_asserts),
                  "fail to complete the core")
        self._write_exp(self.working_diff)
        os.system(f"mv {self.exp_path} {output_path}")
