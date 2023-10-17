import sys
from diff_smt import get_asserts

def parse_stamps(filename):
    cmds0 = dict()
    for line in open(filename):
        line = line.split("|||")
        stamp = int(line[0].strip())
        line = line[1].replace(" ", "").strip().strip()
        cmds0[line] = stamp
    return cmds0

a = parse_stamps(sys.argv[1])
b = get_asserts(sys.argv[2])

# import numpy as np
# for i in b:
# print(a[i])


# for i in b.keys() - a.keys():
#     print(b[i])

# print(len(a), len(b), len(a.keys() & b.keys()))