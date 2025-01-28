from debugger.demo_utils import *
from debugger3 import Debugger3
from utils.system_utils import list_smt2_files
from utils.analysis_utils import Categorizer

statuses = Categorizer()

for query in UNSTABLE_MARIPOSA:
    dbg = Debugger3(query)
    ba = get_singleton_status(dbg)
    if isinstance(ba, str):
        statuses.add_item(ba, query)
    else:
        statuses.add_item("finished", dbg.singleton_dir)

statuses.finalize()
statuses.print_status()

with open("run.sh", "a") as f:
    for item in statuses["finished"]:
        f.write("./src/analysis_wizard.py singleton -e verify -s z3_4_13_0 -i " + item + "\n")

# print(len(build_failures))
# print(len(parse_failures))
# for q in tested_counts:
#     print(q, tested_counts[q])