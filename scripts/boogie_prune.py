from basic_utils import *
import numpy as np
from tqdm import tqdm
from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from analyze_trigger import load_quanti_stats

def export_smt_from_bpl(bgs):
    bgs = list_files_ext("boogies", ".bpl")
    for bg in bgs:
        print(f"dotnet tool run boogie {bg} /proverLog:unpruned/@FILE@.@PROC@.smt2 /timeLimit:1")

c = Configer()

# unpruned = c.load_known_project("d_fvbkv_unpruned")
# pruned = c.load_known_project("d_fvbkv_pruned")

# unpruned_queries = unpruned.list_queries()
# unpruned_queries = {q.split("/")[-1] for q in unpruned_queries}

# pruned_queries = pruned.list_queries()
# pruned_queries = {q.split("/")[-1] for q in pruned_queries}

# there are few not mapped, because of spliting at the VCG level
# print(pruned_queries - unpruned_queries)

def get_prune_keep(orgi_name, mini_name):
    TG = c.load_known_experiment("triggers")
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)
    items0, ps0, tally0 = load(orgi, TG)
    items1, ps0, tally1 = load(mini, TG)
    keep = tally0 & tally1
    # print(len(keep))

    # item00 = dict()
    # for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
    #     item00[cat] = items0[cat] - keep
    #     print(len(item00[cat]))
    # ps0, _ = get_category_percentages(item00)
    # print(ps0)

    for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        items0[cat] = items0[cat] & keep
        items1[cat] = items1[cat] & keep

    keeps = dict()
    for query in keep:
        orgi_path = orgi.clean_dir + "/" + query
        mini_path = mini.clean_dir + "/" + query
        keeps[query] = (orgi_path, mini_path)
    return items0, items1, keeps

def analyze_d_fvbkv_prune():
    items0, items1, keep = get_prune_keep("d_fvbkv_unpruned", "d_fvbkv_pruned")

    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)

    table = [["", "stable", "unstable", "unsolvable"]]
    table.append(["unpruned"] + [ps0[i] for i in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]] )
    table.append(["pruned"] + [ps1[i] for i in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]])

    pts0 = load_quanti_stats("d_fvbkv_unpruned", set([keep[k][0] for k in keep]))
    pts1 = load_quanti_stats("d_fvbkv_pruned", set([keep[k][1] for k in keep]))
    pts2 = load_quanti_stats("d_fvbkv_shaked", set(["data/d_fvbkv_shaked/" + k for k in keep]))

    xs, ys = get_cdf_pts((pts1[:, 2] + pts1[:, 3]) * 100 / (pts0[:, 0] + pts0[:, 1]))
    # print(xs[:4], ys[:4])
    plt.plot(xs, ys, label="pruned")

    xs, ys = get_cdf_pts((pts2[:, 2] + pts2[:, 3]) * 100 / (pts0[:, 0] + pts0[:, 1]))
    # print(xs[:4], ys[:4])
    plt.plot(xs, ys, label="shaked")
    
    plt.xlim(0.001, 100)
    plt.xscale("log")
    plt.ylim(0)
    plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    plt.savefig(f"fig/boogie_prune.png", dpi=200)
    
    # for q in items0[Stability.STABLE] & items1[Stability.UNSOLVABLE]:
    #     print(keep[q])
    print(tabulate(table, headers="firstrow", tablefmt="github"))

def shake_d_fvbkv():
    orgi = c.load_known_project("d_fvbkv_unpruned")

    for q in orgi.list_queries():
        print(f"echo '{q}'")
        print(f"./target/release/mariposa --mutation tree-shake  --in-file-path {q} --out-file-path data/d_fvbkv_shaked/{q.split('/')[-1]}")

# shake_d_fvbkv()

analyze_d_fvbkv_prune()

# pts = np.array(pts)
# fig, ax = plt.subplots()
# xs, ys = get_cdf_pts(pts[:, 0])
# plt.plot(xs, ys, label="unpruned")

# # xs, ys = get_cdf_pts(pts[:, 1])
# # plt.plot(xs, ys, label="pruned")




# os.system(f"wc -l {up} {p}")


# for bg in bgs:
#     print(f"dotnet tool run boogie {bg} /proverLog:unpruned/@FILE@.@PROC@.smt2 /timeLimit:1")