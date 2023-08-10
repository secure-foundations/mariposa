import os, sys
from basic_utils import *

file_paths = []

# for root, _, files in os.walk(sys.argv[1]):
#     for file in files:
#         file_paths.append(os.path.join(root, file))
file_paths = list_smt2_files(sys.argv[1])

for f in file_paths:
    f = open(f"{f}.log")
    lines = f.read()
    if "Refutation found." in lines:
        print("unsat")
    
    
    # print(f)
    # print(f"solvers/vampire-4.8 {f} > {f}.log")



# for f in file_paths:
#     parts = f.split(".")[-3:-1]
#     parts.append("log")
#     parts = ".".join(parts)
#     print(f"solvers/z3-4.12.2 {f} -st > logs/{parts}")

