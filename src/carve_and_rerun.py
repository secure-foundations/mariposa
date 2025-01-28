import sys, os
from utils.system_utils import list_smt2_files, log_info

project_dir = sys.argv[1]
assert project_dir.endswith(".filtered/base.z3")

for i in range(5):
    query_count = len(list_smt2_files(project_dir))
    if query_count <= 10:
        break
    log_info(f"iteration {i}, current query count: {query_count}, carving...")
    carve_command = f"./src/analysis_wizard.py carve -e filter -s z3_4_13_0 -i {project_dir}"
    exp_command = f"./src/exper_wizard.py manager -e filter --total-parts 10 -s z3_4_13_0 -i {project_dir} --clear"
    os.system(carve_command)
    os.system(exp_command)

if query_count == 0:
    log_info("No queries left, exiting...")
    sys.exit(0)

exp_command = f"./src/exper_wizard.py manager -e default --total-parts 10 -s z3_4_13_0 -i {project_dir} --clear"
os.system(exp_command)