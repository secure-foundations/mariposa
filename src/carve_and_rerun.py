import sys, os
from utils.system_utils import list_smt2_files, log_info

project_dir = sys.argv[1]
assert project_dir.endswith(".filtered/base.z3")
# last_count = None

for i in range(8):
    query_count = len(list_smt2_files(project_dir))

    # if last_count != query_count:
    #     last_count = query_count
    # else:
    #     log_info(f"no change in query count, breaking...")
    #     break

    if query_count <= 10:
        break

    exp_command = f"./src/exper_wizard.py manager -e filter --total-parts 10 -s z3_4_13_0 -i {project_dir} --clear"
    log_info(f"iteration {i}, current query count: {query_count}, experimenting...")
    os.system(exp_command)

    carve_command = f"./src/analysis_wizard.py carve -e filter -s z3_4_13_0 -i {project_dir}"
    log_info(f"iteration {i}, current query count: {query_count}, carving...")
    os.system(carve_command)

query_count = len(list_smt2_files(project_dir))

if query_count == 0:
    log_info("no queries left, exiting...")
    sys.exit(0)

print(f"carving done, running full stability test... on {query_count} queries")
exp_command = f"./src/exper_wizard.py manager -e default --total-parts 10 -s z3_4_13_0 -i {project_dir} --clear"
os.system(exp_command)