import sys
from basic_utils import *
import hashlib
import numpy as np
import re

def get_asserts(filename):
    cmds0 = dict()
    if filename is None:
        return cmds0
    with open(filename) as f:
        for line in f.readlines():
            if line.startswith("(assert "):
                cmds0[line.replace(" ", "").strip()] = line.strip()
    return cmds0

def get_name_hash(filename):
    return hashlib.sha256(filename.encode()).hexdigest()

def check_assert_subset(orig_path, reduced_path):
    original = get_asserts(orig_path)
    reduced = get_asserts(reduced_path)
    assert len(reduced) != 0
    if not key_set(reduced).issubset(key_set(original)):
        print(len(original), len(reduced))
        for i in key_set(reduced) - key_set(original):
            print(reduced[i])
            break
        assert False

def get_assert_count(filename):
    output = subprocess_run(r'rg -e "\(assert" -c' + " " + filename)[0]
    if output == "":
        return np.inf
    return int(output)

def print_diff_stats(path1, path2):
    # count1 = get_assert_count(path1)
    # count2 = get_assert_count(path2)
    # print(count1, count2)
    lines1 = set(open(path1).readlines())
    lines2 = set(open(path2).readlines())
    for i in lines1 - lines2:
        print(i, end="")

s_expr_start = re.compile(r"^\(([^ ]+) ")

def get_scores_for_core(score_file, core_file):
    core_asserts = get_asserts(core_file)
    # scores = dict()
    layers = dict()

    with open(score_file) as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip().split("|||")
            it = int(line[0])
            if it not in layers:
                layers[it] = []
            layers[it].append((float(line[1]), line[2]))

        for it in sorted(layers.keys()):
            min_score = 1
            max_score = 0

            scores = []
            for i in sorted(layers[it]):
                nline = i[1].replace(" ", "").strip()
                print(i[1])
                if nline in core_asserts and "forall" in i[1]:
                    min_score = min(i[0], min_score)
                    max_score = max(i[0], max_score)
                    print("\tis core:", it, i[0])
                else:
                    print("\tnone core:", it, i[0])
                    pass

                scores.append(i[0])
            scores = np.array(scores)
            print("===layer summary===")
            print(it, min_score, max_score, np.sum([scores <= max_score]), len(scores))

    # for i in core_asserts.keys():
    #     if i in scores:
    #         print(scores[i])

def key_set(d):
    return set(d.keys())

def value_set(d):
    return set(d.values())

if __name__ == "__main__":
    # a = get_asserts(sys.argv[1])
    # b = get_asserts(sys.argv[2])
    # for i in a.keys() - b.keys():
    #     print(a[i])
    # print(len(a), len(b), len(a.keys() & b.keys()))
    op = sys.argv[1]
    if op == "subset-check":
        check_assert_subset(sys.argv[2], sys.argv[3])
    elif op == "diff-stats":
        print_diff_stats(sys.argv[2], sys.argv[3])
    elif op == "core":
        get_scores_for_core(sys.argv[2], sys.argv[3])

    # a = get_asserts(sys.argv[1])
    # b = get_asserts(sys.argv[2])
    # for i in a.keys() - b.keys():
    #     print(a[i])
    # print(len(a), len(b), len(a.keys() & b.keys()))        
