from basic_utils import *
from db_utils import *
from vbkv_filemap import *

from plot_utils import *
from configer import Configer

c = Configer()

mini = c.load_known_project("d_lvbkv_uc")

prefix = "data/unsat_cores/d_lvbkv_uc/min_asserts_no_trigger"

for q in mini.list_queries():
    base = q.split("/")[-1]
    print(f"./target/release/mariposa --in-file-path {q} --out-file-path {prefix}/{base} -m remove-trigger")
