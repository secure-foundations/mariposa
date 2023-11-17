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
    # scores = dict()
    layers = dict()
    covered = set()
    olines = get_asserts(core_file)
    core_asserts = key_set(olines)

    # cores = set(core_asserts.keys())
    with open(score_file) as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip().split("|||")
            it = int(line[0])
            if it not in layers:
                layers[it] = set()
            nl = line[1].replace(" ", "").strip()
            olines[nl] = line[1]

            layers[it].add(nl)

        for it in sorted(layers.keys()):
            print(f"===layer {it} summary===")
            print(f"core asserts: {len(core_asserts & layers[it])}/{len(layers[it])}")
            for nl in layers[it]:
                covered.add(nl)
                if nl in core_asserts:
                    print("[c] ", end="")
                print(olines[nl])

    print("===missing summary===")

    for i in core_asserts - covered:
        print(olines[i])



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
