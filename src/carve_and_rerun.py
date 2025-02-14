#!/usr/bin/env python3


import sys, os
from utils.system_utils import list_smt2_files, log_info, log_warn

project_dir = sys.argv[1]

if project_dir.endswith("/"):
    project_dir = project_dir[:-1]

if not project_dir.endswith(".filtered/base.z3"):
    assert project_dir.endswith("/base.z3")

    exp_command = f"./src/exper_wizard.py manager -e verify --total-parts 12 -s z3_4_13_0 -i {project_dir} --clear"
    os.system(exp_command)

    filter_command = f"./src/analysis_wizard.py filter -s z3_4_13_0 -i {project_dir}"
    os.system(filter_command)
    filter_dir = project_dir.replace("/base.z3", ".filtered/base.z3")
else:
    filter_dir = project_dir 

last_count = -1

for i in range(8):
    query_count = len(list_smt2_files(filter_dir))

    if last_count != query_count:
        last_count = query_count
    elif (query_count <= 12 and i > 4) or query_count == 0:
        break

    exp_command = f"./src/exper_wizard.py manager -e filter --total-parts 12 -s z3_4_13_0 -i {filter_dir} --clear"
    log_info(f"iteration {i}, current query count: {query_count}, experimenting...")
    os.system(exp_command)

    carve_command = f"./src/analysis_wizard.py carve -e filter -s z3_4_13_0 -i {filter_dir}"
    log_info(f"iteration {i}, current query count: {query_count}, carving...")
    os.system(carve_command)

query_count = len(list_smt2_files(filter_dir))

if query_count == 0:
    log_warn("no queries left!")

print(f"carving done, running full stability test... on {query_count} queries")
exp_command = f"./src/exper_wizard.py manager -e default --total-parts 12 -s z3_4_13_0 -i {filter_dir} --clear"
os.system(exp_command)