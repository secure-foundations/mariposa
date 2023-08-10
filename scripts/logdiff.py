import os, sys
from tabulate import tabulate
import numpy as np

file_paths = []

for root, _, files in os.walk(sys.argv[1]):
    for file in files:
        file_paths.append(os.path.join(root, file))

usats = dict()
unknowns = dict()

for file_path in file_paths:
    # print(file_path)
    with open(file_path, "r") as f:
        unsat = False
        for line in f.readlines():
            line = line.strip()
            if "unsat" in line:
                unsat = True
            elif "unknown" in line:
                assert not unsat
            elif line == "":
                continue
            else:
                if line.endswith(")"):
                    line = line[:-1]
                if line.startswith("("):
                    line = line[1:]
                kv = line.split(" ")
                key = kv[0]
                value = kv[-1]
                try:
                    value = int(value)
                except:
                    try:
                        value = float(value)
                    except:
                        print(line)
                        assert False
                if unsat:
                    if key not in usats:
                        usats[key] = []
                    usats[key].append(value)
                else:
                    if key not in unknowns:
                        unknowns[key] = []
                    unknowns[key].append(value)
rows = []
for key in sorted(set(usats.keys()) | set(unknowns.keys())):
    avg1 = None
    if key in usats:
        avg1 = round(sum(usats[key]) / len(usats[key]), 2), round(np.std(usats[key]), 2)
    avg2 = None
    if key in unknowns:
        avg2 = round(sum(unknowns[key]) / len(unknowns[key]), 2), round(np.std(unknowns[key]), 2)
    ratio = 1000
    if avg1 is not None:
        ratio = avg2[0] / avg1[0]
    rows.append((key, avg1, avg2, ratio))
rows = sorted(rows, key=lambda x:x[-1], reverse=True)
print(tabulate(rows, tablefmt="github"))

# print(usats)
# print(unknowns)