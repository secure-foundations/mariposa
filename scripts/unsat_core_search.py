from basic_utils import *
from diff_smt import *
import random, math, hashlib
from copy import deepcopy
import pickle
import numpy as np

UNSTABLE_TRIALS = 4

def run_z3(query_path, timeout):
    assert timeout < 100
    std, err, rtime  = subprocess_run(f"./solvers/z3-4.12.2 {query_path} -T:{timeout}")
    # print(std)
    return std, err, rtime

class Reducer:
    def __init__(self, working_path):
        random.seed(time.time())
        self.working_path = working_path
        self.name_hash = hashlib.sha256(working_path.encode()).hexdigest()
        self.exp_path = f"gen/{self.name_hash}.exp.smt2"
        self.retain_path = f"gen/{self.name_hash}.retain"
        self.mut_path = f"gen/{self.name_hash}.mut.smt2"
        print("exp path: " + self.exp_path)

        self.all_cmds = open(working_path).readlines()

        self.working_indices = set()
        self.retain_indices = set()
        self.non_assert_indices = set()
        
        self.unstable_count = 0
        self.exp_count = 0
        self.enable_mut = False

        for i in range(len(self.all_cmds)):
            if self.all_cmds[i].startswith("(assert"):
                self.working_indices.add(i)
            else:
                self.non_assert_indices.add(i)

        self.timeout = 30

        self.load_retain_indices()

        std, _, rtime = self._run_exp(self.working_indices)
        message = "the initial round is not unsat"
        exit_with_on_fail(std == "unsat", message)

        self.timeout = int(2 * rtime // 1000)
        self.timeout = max(self.timeout, 3)

        print("timeout is set to: ", self.timeout)
        
    def load_retain_indices(self):
        if not os.path.exists(self.retain_path):
            return

        with open(self.retain_path, 'rb') as f:
            retain_hashes = pickle.load(f)

        for (i, c) in enumerate(self.all_cmds):
            if c in retain_hashes:
                self.retain_indices.add(i)

        self.working_indices -= self.retain_indices

    def save_retain_indices(self):
        retain_hashes = set()
        for (i, c) in enumerate(self.all_cmds):
            if i in self.retain_indices:
                retain_hashes.add(c)
        print("saving retain indices", len(retain_hashes))
        with open(self.retain_path, 'wb+') as f:
            pickle.dump(retain_hashes, f)

    def pick_test_indices(self, drop_size):
        # assert self.working_indices.isdisjoint(self.retain_indices)
        drop_indices = set(random.sample(self.working_indices, k=drop_size))
        # print("dropping indices: ", drop_indices)
        test_indices = self.working_indices - drop_indices
        return test_indices

    def nary_search(self, drop_size):
        print("starting nary search", drop_size, self.get_stats())
        if drop_size <= len(self.working_indices):
            return "no progress"
        trails = 0
        while trails < 20:
            test_indices = self.pick_test_indices(drop_size)
            if self._run_exp(test_indices)[0] == "unsat":
                self.working_indices = test_indices
                print(f"progress {trails} {self.get_stats()}")
                return "progress"
            trails += 1
        print("finished nary search", self.get_stats())
        return "no progress"

    def get_stats(self):
        return f"working set {len(self.working_indices)}, retain set {len(self.retain_indices)}"

    def linear_search(self, max_trails=50):
        trials = 0
        success_count = 0
        untested = list(self.working_indices)
        random.shuffle(untested)
        # max_trails = max(len(self.working_indices), 100)
        print("starting linear search", self.get_stats())

        while len(untested) != 0 and trials < max_trails:
            test_index = untested.pop()
            test_indices = self.working_indices - {test_index}
            if self._run_exp(test_indices)[0] != "unsat":
                self.retain_indices.add(test_index)
                print("added to retain set", test_index)
            else:
                success_count += 1
            self.working_indices.remove(test_index)
            trials += 1
        print(f"finished linear search", self.get_stats())
        if trials == 0:
            return None
        return success_count / trials

    def get_drop_size(self, success_rate):
        esti_size = 1
        working_size = len(self.working_indices)

        if success_rate >= 0.98:
            success_rate = 0.98
        if success_rate <= 0.05:
            # probably not worth it...
            return working_size

        while 1:
            prob = math.pow(success_rate, esti_size) 
            if prob < 0.05:
                break
            if math.comb(working_size, esti_size) < 30:
                break
            esti_size += 1
        # print(esti_size, prob, working_size)
        return esti_size

    def try_reduce_query(self, output_path=None):
        for _ in range(8):
            success_rate = self.linear_search()
            print("success rate: ", success_rate)
            if success_rate == None:
                break

            drop_size = self.get_drop_size(success_rate)
            if drop_size >= len(self.working_indices):
                continue

            while self.nary_search(drop_size) == "progress":
                drop_size = max(int(drop_size * 1.1), drop_size + 1)
        if output_path is not None:
            self._write_exp(self.working_indices)
            os.system(f"cp {self.exp_path} {output_path}")
        self.save_retain_indices()

    def _run_exp(self, keep_indices):
        self._write_exp(keep_indices)

        std, err, rtime  = run_z3(self.exp_path, self.timeout)
        if std == "unsat":
            return std, err, rtime 

        if not self.enable_mut:
            return std, err, time

        if self.unstable_count == 0 and self.exp_count == 10:
            self.enable_mut = False
            print("disabling mutation")
            return std, err, time

        for _ in range(UNSTABLE_TRIALS):
            os.system(f"./target/release/mariposa -i {self.exp_path} -o {self.mut_path} -m all")
            std, err, rtime  = run_z3(self.mut_path, self.timeout)
            if std == "unsat":
                self.unstable_count += 1
                print("found unstable")
                return std, err, time

        self.exp_count += 1
        return std, err, time

    def _write_exp(self, keep_indices):
        assert keep_indices.isdisjoint(self.retain_indices)
        assert keep_indices.isdisjoint(self.non_assert_indices)

        exp_file = open(self.exp_path, "w")
        exp_cmds = []
        for i in range(len(self.all_cmds)):
            if i in self.non_assert_indices or i in keep_indices or i in self.retain_indices:
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
        std, _, rtime = self._run_exp(self.diff_asserts)
        message = "the initial round is not unsat"
        exit_with_on_fail(std == "unsat", message)
        self.timeout = max(2 * rtime // 1000, 10)
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
        if len(cur_diff) <= 1:
            return cur_diff
        logn = int(math.log(len(cur_diff), 2))
        trails = 0

        if len(cur_diff) // 4 == 0:
            return cur_diff

        while trails < logn * 8:
            next_diff = random.sample(cur_diff, k=len(cur_diff) // 4)
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
    op = sys.argv[1]
    
    if op == "complete":
        e = Expander(sys.argv[2], sys.argv[3])
        e.try_complete_core(sys.argv[4])
    elif op == "reduce":
        r = Reducer(sys.argv[2])
        r.try_reduce_query(sys.argv[3])
