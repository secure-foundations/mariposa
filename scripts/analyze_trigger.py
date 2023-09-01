from basic_utils import *
from db_utils import *
from vbkv_filemap import *

from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from cache_utils import cache_load, cache_save
import random

c = Configer()

def remove_some_triggers():
    orgi = c.load_known_project("d_komodo")
    pruned = c.load_known_project("d_komodo_trigger_10")
    prefix = pruned.clean_dir

    for q in orgi.list_queries():
        base = q.split("/")[-1]
        rs = random.randint(0, 0xffffffffffffffff)
        print(f"./target/release/mariposa --in-file-path {q} --out-file-path {prefix}/{base} -m remove-trigger --seed {rs}")

    # for q in list_smt2_files(prefix):
    #     print(f"./target/release/mariposa --in-file-path {q}")

def format_item(count, total):
    return f"{int(count)} ({round(count * 100 / total, 0)}%)"

def print_assertion_distribution():
    tpts = []

    for orgi_name in PAIRS.keys():
        pts = load_quanti_stats(orgi_name)
        total = pts[:, 2] + pts[:, 3] + pts[:, 4]
        pts = pts[(pts[:, 2]/total).argsort()]
        total = pts[:, 2] + pts[:, 3] + pts[:, 4]
        qf, nqf, others = pts[:, 2], pts[:, 3], pts[:, 4]

        row = [orgi_name]
        tt = np.median(total)
        row.append(int(tt))
        row.append(format_item(np.median(others), tt))
        row.append(format_item(np.median(qf), tt))
        row.append(format_item(np.median(nqf), tt))

        qf, nqf, others = qf * 100 /total, nqf * 100 /total, others * 100 /total
    
        xs = np.arange(0, len(pts[:, 1]), 1)
        fig, ax = plt.subplots()
        plt.fill_between(xs, nqf, label="Q-assert")
        plt.fill_between(xs, nqf, nqf + qf, label="QF-assert")
        plt.fill_between(xs, nqf + qf, nqf + qf + others, label="N-assert")
        plt.ylim(0)
        plt.xlim(0, len(xs))
        plt.legend()
        plt.savefig(f"fig/quanti/{orgi_name}_commands.png", dpi=200)
        plt.close()
        tpts.append(row)

    print(tabulate(tpts, ["project", "total", "n-assert", "qf-assert", "q-assert"], tablefmt="latex"))

def print_quantifier_distribution():
    tpts = []

    for orgi_name in PAIRS.keys():
        orgi = c.load_known_project(orgi_name)
        
        if os.path.exists(f"cache/{orgi_name}_quanti.pkl"):
            pts = cache_load(f"{orgi_name}_quanti.pkl")
        else:
            pts = np.zeros((len(orgi.list_queries()), 5))
            for i, q in enumerate(tqdm(orgi.list_queries())):
                pts[i] = get_quanti_stats(q)
            cache_save(pts, f"{orgi_name}_quanti.pkl")
        nqfs = pts[:, 3]
        forall, exists = pts[:, 0], pts[:, 1]

# def plot_prelude():
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

if __name__ == "__main__":
    # remove_some_triggers()
    print_assertion_distribution()
    # print(get_quanti_stats(sys.argv[1]))
