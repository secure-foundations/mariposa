from basic_utils import *
from db_utils import *
from vbkv_filemap import *

from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from cache_utils import cache_load, cache_save

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

# for q in mini.list_queries():
#     base = q.split("/")[-1]
#     out_file = f"{prefix}/{base}"
#     # diff out_file with q
#     # print(out_file)
#     o, _, _ = subprocess_run(f"diff {q} {out_file}")
#     if o == "":
#         os.remove(out_file)

for q in list_smt2_files(prefix):
    print(f"./target/release/mariposa --in-file-path {q}")
# def plot_quanti():
#     for orgi_name in PAIRS.keys():
#         fig, ax = plt.subplots()
#         orgi = c.load_known_project(orgi_name)
#         if os.path.exists(f"cache/{orgi_name}_quanti.pkl"):
#             pts = cache_load(f"{orgi_name}_quanti.pkl")
#         else:
#             pts = np.zeros((len(orgi.list_queries()), 3))
#             for i, q in enumerate(tqdm(orgi.list_queries())):
#                 c1, c2, c3 = get_quanti_stats(q, "fs" in orgi_name)
#                 pts[i] = [c1, c2, c3]
#             cache_save(pts, f"{orgi_name}_quanti.pkl")

#         xs = np.arange(0, len(pts[:, 1]), 1)
#         # 0 fcount, 1 ecount, 2 total
#         pts = pts[pts[:, 2].argsort()]
#         plt.fill_between(xs, pts[:, 2], pts[:, 0]+pts[:, 1], color="#332288")
#         plt.fill_between(xs, pts[:, 0] + pts[:, 1], pts[:, 0], color="#44AA99")
#         plt.fill_between(xs, pts[:, 0], np.zeros(len(xs)), color="#88CCEE")

#         print(np.mean(pts[:, 0] / pts[:, 2]) * 100 )
#         print(np.mean(pts[:, 1] / pts[:, 2]) * 100 )
#         print(np.mean((pts[:, 2] - pts[:, 0] - pts[:, 1])/ pts[:, 2]) * 100 )
#         print("")

#         plt.ylim(0)
#         plt.xlim(0, len(xs))
#         plt.savefig(f"fig/quanti/{orgi_name}.png", dpi=200)
#         plt.close()

# plot_quanti()
