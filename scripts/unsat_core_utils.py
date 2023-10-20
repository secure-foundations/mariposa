from basic_utils import *
from diff_smt import *
import random
import math
import zlib 

class Expander:    
    def __init__(self, orig_path, hint_path, remove_cache=False):
        self.name_hash = str(zlib.adler32(orig_path.encode()))
        self._setup_diff(orig_path, hint_path, remove_cache)
        hint_commands = open(hint_path).readlines()

        i = len(hint_commands) - 1
        while i >= 0:
            if hint_commands[i].startswith("(push "):
                break
            i -= 1

        self.pre_push = hint_commands[:i]
        self.post_push = hint_commands[i:]
        
        self.exp_path = f"gen/{self.name_hash}.exp.smt2"
        self.timeout = 30

        # first test using all diffs
        std, _, time = self._run_exp(self.diff_asserts)
        message = "the initial round is not unsat"
        exit_with_on_fail(std == "unsat", message)
        self.timeout = max(2 * time // 1000, 10)

        print("timeout is set to: ", self.timeout)

    def _setup_diff(self, orig_path, hint_path, remove_cache):
        fmt_path = f"gen/{self.name_hash}.fmt.smt2"
        diff_path = f"gen/{self.name_hash}.diff.smt2"

        if remove_cache:
            os.system(f"rm -r {fmt_path} {diff_path}")

        if not os.path.exists(fmt_path):
            mariposa_format(orig_path, fmt_path)
        
        if not os.path.exists(diff_path):
            orig_asserts = get_asserts(fmt_path)
            hint_asserts = get_asserts(hint_path)
            
            is_subset = key_set(hint_asserts).issubset(key_set(orig_asserts))
            message = f"hint is not a subset of orig:\n{hint_path}\n{orig_path}"
            exit_with_on_fail(is_subset, message)

            self.diff_asserts = []

            for i in orig_asserts.keys() - hint_asserts.keys():
                self.diff_asserts.append(orig_asserts[i] + "\n")

            open(diff_path, "w").writelines(self.diff_asserts)
        else:
            self.diff_asserts = open(diff_path).readlines()

    def _run_exp(self, next_diff):
        exp_file = open(self.exp_path, "w")
        ext_commands = self.pre_push + next_diff + self.post_push
        exp_file.writelines(ext_commands)
        exp_file.close()
        std, err, time  = subprocess_run(f"./solvers/z3-4.8.5 {self.exp_path} -T:{self.timeout}")
        return std, err, time 

    def binary_search(self, cur_diff):
        logn = int(math.log(len(cur_diff), 2))
        trails = 0

        while trails < logn * 2:
            next_diff = random.sample(cur_diff, k=len(cur_diff) // 2)
            std = self._run_exp(next_diff)[0]
            if std == "unsat":
                print("narrowed to diff len: ", len(next_diff))
                return next_diff
            trails += 1

        print("give up bisection search at diff len: ", len(cur_diff))
        return cur_diff

    def try_complete_core(self):
        cur_diff = self.diff_asserts
        while 1:
            next_diff = self.binary_search(cur_diff)
            if len(next_diff) != len(cur_diff):
                cur_diff = next_diff
            else:
                break
    # print("give up bisection search at diff len: ", len(next_diff))

if __name__ == "__main__":
    e = Expander(sys.argv[1], sys.argv[2])
    e.try_complete_core()

