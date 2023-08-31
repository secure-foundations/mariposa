from basic_utils import *
from db_utils import *
from vbkv_filemap import *

from plot_utils import *
from configer import Configer

c = Configer()

# mini = c.load_known_project("d_lvbkv_uc")

# prefix = "data/unsat_cores/d_lvbkv_uc/min_asserts_no_trigger"

# for q in mini.list_queries():
#     base = q.split("/")[-1]
#     print(f"./target/release/mariposa --in-file-path {q} --out-file-path {prefix}/{base} -m remove-trigger")

mini = c.load_known_project("fs_vwasm_uc")
prefix = "data/unsat_cores/fs_vwasm_z3/min_asserts_no_trigger2"

# for q in mini.list_queries():
#     base = q.split("/")[-1]
#     print(f"./target/release/mariposa --in-file-path {q} --out-file-path {prefix}/{base} -m remove-trigger")

diff = 0

for q in mini.list_queries():
    base = q.split("/")[-1]
    out_file = f"{prefix}/{base}"
    # diff out_file with q
    # print(out_file)
    o, _, _ = subprocess_run(f"diff {q} {out_file}")
    if o == "":
        os.remove(out_file)

# print(diff)