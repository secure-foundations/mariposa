from copy import deepcopy
import math
import os, random
from base.solver import RCode, Solver
from utils.query_utils import Mutation, emit_mutant_query, format_query, get_asserts, key_set
from utils.system_utils import *

class CoreCompleter:
    def __init__(self, input_query, core_query, output_query, solver, timeout, stop_diff=4):
        log_check(os.path.exists(input_query), f"input query {input_query} does not exist")

        self.solver: Solver = solver
        self.time_limit = timeout
        self.stop_diff = stop_diff
        self.output_path = output_query

        name_hash = get_name_hash(input_query)
        self.name_hash = name_hash
        self.exp_path = f"gen/{name_hash}.core.comp.smt2"

        self._setup_diff(input_query, core_query)
        self.output_query = output_query
        self.input_query = input_query

        self._setup_hint(core_query)
        


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
        print(self.fmt_path)
        orig_asserts = get_asserts(self.fmt_path)
        hint_asserts = get_asserts(hint_path)
        print(f"orig asserts: {len(orig_asserts)}, hint asserts: {len(hint_asserts)}")
        print(f"not in orig: {len(key_set(hint_asserts) - key_set(orig_asserts))}")
        
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
        if len(cur_diff) <= self.stop_diff:
            return cur_diff

        logn = int(math.log(len(cur_diff), 2))
        max_trials = logn * 16
        trials = 0

        while trials < max_trials:
            next_diff = random.sample(cur_diff, k=len(cur_diff) // 2)
            log_info(f"trying diff len: {len(next_diff)}, trials: {trials+1}/{max_trials}")
            self._write_exp(next_diff)
            rc, et = self.solver.run(self.exp_path, self.time_limit)

            if rc == RCode.UNSAT:
                self.time_limit = min(self.time_limit, int(et / 800 + 1))
                log_info(f"narrowed to diff len: {len(next_diff)}")
                log_info(f"time limit adjusted to: {self.time_limit}")
                # just in case something weird happens
                self.working_diff = deepcopy(next_diff)
                return next_diff
            trials += 1
        return cur_diff

    def run(self):
        cur_diff = self.diff_asserts

        if len(self.diff_asserts) <= self.stop_diff:
            log_warn(f"diff is too small: {len(self.diff_asserts)}")
            return self.__handle_small_diff()
            

        print(f"initial diff len: {len(cur_diff)}")

        while 1:
            next_diff = self.binary_search(cur_diff)
            if len(next_diff) == len(cur_diff):
                log_info(f"quitting bisection search at diff len: {len(cur_diff)}" )
                break
            cur_diff = next_diff

        self.clear_temp_files()

        if len(cur_diff) >= len(self.diff_asserts):
            return False

        self._write_exp(self.working_diff)
        os.system(f"mv {self.exp_path} {self.output_path}")
        return True

    def __handle_small_diff(self):
        for _ in range(10):
            remove_file(self.exp_path)

            s = random.randint(0, 0xffffffffffffffff)
            emit_mutant_query(self.input_query,
                              self.exp_path, 
                              Mutation.COMPOSE, s)
            rc, et = self.solver.run(self.exp_path, self.time_limit)

            if rc == RCode.UNSAT:
                os.system(f"cp {self.input_query} {self.output_query}")
                remove_file(self.exp_path)
                return True

        # exit_with("the original query is unsolvable with a small diff")
        return False