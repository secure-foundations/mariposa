from basic_utils import *
from diff_smt import *
import random, math, hashlib
from copy import deepcopy

def run_z3(query_path, timeout):
    assert timeout < 200
    std, err, time  = subprocess_run(f"./solvers/z3-4.12.2 {query_path} -T:{timeout}")
    return std, err, time 

class Reducer:
    def __init__(self, working_path):
        self.working_path = working_path
        self.name_hash = hashlib.sha256(working_path.encode()).hexdigest()
        self.exp_path = f"gen/{self.name_hash}.exp.smt2"
        print("exp path: " + self.exp_path)
        self.timeout = 30
        
        std, _, time = run_z3(working_path, self.timeout)
        message = "the initial round is not unsat"
        exit_with_on_fail(std == "unsat", message)

        self.timeout = max(2 * time // 1000, 10)
        print("timeout is set to: ", self.timeout)
        
        self.all_cmds = open(working_path).readlines()

        self.working_indies = set()
        self.retain_indies = set()

        for i in range(len(self.all_cmds)):
            if self.all_cmds[i].startswith("(assert"):
                self.working_indies.add(i)
            else:
                self.retain_indies.add(i)

        self.initial_retain_size = len(self.retain_indies)

    def nary_search(self):
        print("starting nary search, working set at", len(self.working_indies))
        # while self.drop_divisor < 10:
        working_size = len(self.working_indies)
        drop_size = working_size // 4
        if drop_size <= 1:
            return "no progress"
        # print("drop size: ", drop_size)
        trails = 0

        max_trials = int(math.log(working_size, 4)) * 3
        while trails < max_trials:
            # we need to keep other commands
            drop_indies = set(random.sample(self.working_indies, k=drop_size))
            test_indies = self.working_indies - drop_indies
            if self._run_exp(test_indies)[0] == "unsat":
                self.working_indies = test_indies
                print("progress, working set at", len(self.working_indies))
                return "progress"
            trails += 1
            # print("no progress, increasing drop divisor", drop_size, self.drop_divisor)
            # self.drop_divisor += 1
        print("finished nary search, working set at", len(self.working_indies))
        return "no progress"

    def linear_search(self, max_trails=100):
        trails = 0
        untested = deepcopy(self.working_indies)
        # max_trails = max(len(self.working_indies), 100)
        print("starting linear search, working set at", len(self.working_indies))

        while len(untested) != 0 and trails < max_trails:
            test_index = untested.pop()
            test_indies = self.working_indies - {test_index}
            if self._run_exp(test_indies)[0] == "unsat":
                self.working_indies.remove(test_index)
                # print("progress, working set at", len(self.working_indies))
            else:
                self.retain_indies.add(test_index)
                # print("added to retain set", test_index)
            trails += 1
        print("finished linear search, working set at", len(self.working_indies))

    def try_reduce_query(self, output_path=None):
        for _ in range(3):
            self.linear_search()
            while self.nary_search() == "progress":
                pass
        print("finished all", len(self.working_indies), 
              len(self.retain_indies) - self.initial_retain_size)

        if output_path is not None:
            self._write_exp(self.working_indies)
            os.system(f"cp {self.exp_path} {output_path}")

    def _run_exp(self, keep_indies):
        self._write_exp(keep_indies)
        return run_z3(self.exp_path, self.timeout)
    
    def _write_exp(self, keep_indies):
        exp_file = open(self.exp_path, "w")
        exp_cmds = []
        for i in range(len(self.all_cmds)):
            if i in self.retain_indies or i in keep_indies:
                exp_cmds.append(self.all_cmds[i])
        exp_file.writelines(exp_cmds)
        exp_file.close()

class Expander:
    def __init__(self, orig_path, hint_path):
        seed = (orig_path + hint_path).encode() 
        self.name_hash = hashlib.sha256(seed).hexdigest()
        self._setup_diff(orig_path, hint_path)
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
        print("initial round: " + self.exp_path)
        std, _, time = self._run_exp(self.diff_asserts)
        message = "the initial round is not unsat"
        exit_with_on_fail(std == "unsat", message)
        self.timeout = max(2 * time // 1000, 10)
        self.working_diff = self.diff_asserts

        print("timeout is set to: ", self.timeout)

    def _setup_diff(self, orig_path, hint_path):
        fmt_path = f"gen/{self.name_hash}.fmt.smt2"
        diff_path = f"gen/{self.name_hash}.diff.smt2"

        mariposa_format(orig_path, fmt_path)
    
        orig_asserts = get_asserts(fmt_path)
        hint_asserts = get_asserts(hint_path)
        
        is_subset = key_set(hint_asserts).issubset(key_set(orig_asserts))
        message = f"hint is not a subset of orig:\n{hint_path}\n{orig_path}"
        exit_with_on_fail(is_subset, message)

        self.diff_asserts = []

        for i in orig_asserts.keys() - hint_asserts.keys():
            self.diff_asserts.append(orig_asserts[i] + "\n")

        open(diff_path, "w").writelines(self.diff_asserts)

    def _write_exp(self, next_diff):
        exp_file = open(self.exp_path, "w")
        ext_commands = self.pre_push + next_diff + self.post_push
        exp_file.writelines(ext_commands)
        exp_file.close()

    def _run_exp(self, next_diff):
        self._write_exp(next_diff)
        return run_z3(self.exp_path, self.timeout)

    def binary_search(self, cur_diff):
        logn = int(math.log(len(cur_diff), 2))
        trails = 0

        while trails < logn * 3:
            next_diff = random.sample(cur_diff, k=len(cur_diff) // 2)
            std = self._run_exp(next_diff)[0]
            if std == "unsat":
                print("narrowed to diff len: ", len(next_diff))
                # just in case something weird happens
                self.working_diff = deepcopy(next_diff)
                return next_diff
            trails += 1

        print("give up bisection search at diff len: ", len(cur_diff))
        return cur_diff

    def try_complete_core(self, output_path=None):
        cur_diff = self.diff_asserts
        while 1:
            next_diff = self.binary_search(cur_diff)
            if len(next_diff) != len(cur_diff):
                cur_diff = next_diff
            else:
                break

        if output_path is not None:
            self._write_exp(self.working_diff)
            os.system(f"cp {self.exp_path} {output_path}")

if __name__ == "__main__":
    # e = Expander(sys.argv[1], sys.argv[2])
    # e.try_complete_core(sys.argv[3])
    r = Reducer(sys.argv[1])
    r.try_reduce_query(sys.argv[2])
