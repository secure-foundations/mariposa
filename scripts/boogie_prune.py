from basic_utils import *
import numpy as np
from tqdm import tqdm
from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from analyze_trigger import load_quanti_stats

def export_smt_from_bpl():
    bgs = list_files_ext("boogies", ".bpl")
    for bg in bgs:
        # print(f"dotnet tool run boogie {bg} /proverLog:unpruned/@FILE@.@PROC@.smt2 /timeLimit:1")
        print(f"dotnet tool run boogie {bg} /proverLog:unpruned_new/@FILE@.@PROC@.smt2  /timeLimit:1 /proverOpt:O:auto_config=false /proverOpt:O:type_check=true /proverOpt:O:smt.case_split=3 /proverOpt:O:smt.qi.eager_threshold=100 /proverOpt:O:smt.delay_units=true")

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
    PN = c.load_known_experiment("pruned")

    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)
    shake = c.load_known_project("d_fvbkv_shaked")
    
    items0, _, tally0 = load(orgi, TG)
    items1, _, tally1 = load(mini, TG)
    items2, _, tally2 = load(shake, PN)

    keep = tally0 & tally1
    # print(len(keep))

    # item00 = dict()
    # for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
    #     item00[cat] = items0[cat] - keep
    #     print(len(item00[cat]))
    # ps0, _ = get_category_percentages(item00)
    # print(ps0)

    for cat in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        items0[cat] = items0[cat] & keep
        items1[cat] = items1[cat] & keep
        items2[cat] = items2[cat] & keep

    for i in items0[Stability.UNSOLVABLE]:
        print(i)

    keeps = dict()
    for query in keep:
        orgi_path = orgi.clean_dir + "/" + query
        mini_path = mini.clean_dir + "/" + query
        shake_path = shake.clean_dir + "/" + query
        keeps[query] = (orgi_path, mini_path, shake_path)
    return items0, items1, items2, keeps

def analyze_d_fvbkv_prune():
    items0, items1, items2, keep = get_prune_keep("d_fvbkv_unpruned", "d_fvbkv_pruned")

    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)
    ps2, _ = get_category_percentages(items2)

    table = [["", "unknown", "stable", "unstable", "unsolvable"]]
    table.append(["unpruned"] + [ps0[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]] )
    table.append(["pruned"] + [ps1[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]])
    table.append(["shaked"] + [ps2[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]])

    pts0 = load_quanti_stats("d_fvbkv_unpruned", set([keep[k][0] for k in keep]))
    pts1 = load_quanti_stats("d_fvbkv_pruned", set([keep[k][1] for k in keep]))
    pts2 = load_quanti_stats("d_fvbkv_shaked", set([keep[k][2] for k in keep]))

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

    print(tabulate(table, headers="firstrow", tablefmt="github"))

def shake_d_fvbkv():
    orgi = c.load_known_project("d_fvbkv_unpruned")

    for q in orgi.list_queries():
        print(f"echo '{q}'")
        print(f"./target/release/mariposa --mutation tree-shake  --in-file-path {q} --out-file-path data/d_fvbkv_shaked/{q.split('/')[-1]}")

export_smt_from_bpl()

# def shake_fs_dice():
#     # orgi = c.load_known_project("fs_dice")
#     # for q in orgi.list_queries():
#     #     print(f"echo '{q}'")
#     #     print(f"./target/release/mariposa --mutation tree-shake  --in-file-path {q} --out-file-path data/fs_dice_shaked/{q.split('/')[-1]}")

#     pts0 = load_quanti_stats("fs_dice")
#     pts1 = load_quanti_stats("fs_dice_shaked")
#     xs, ys = get_cdf_pts((pts1[:, 2] + pts1[:, 3]) * 100 / (pts0[:, 0] + pts0[:, 1]))
#     # print(xs[:4], ys[:4])
#     plt.plot(xs, ys, label="shaked")
    
#     plt.xlim(0.001, 100)
#     plt.xscale("log")
#     plt.ylim(0)
#     plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
#     plt.savefig(f"fig/dice_prune.png", dpi=200)
    
# shake_fs_dice()

# shake_d_fvbkv()
# analyze_d_fvbkv_prune()

# TG = c.load_known_experiment("triggers")
# orgi = c.load_known_project("d_fvbkv_unpruned")
# items0, ps0, tally0 = load(orgi, TG)
# print(ps0)

# pts = np.array(pts)
# fig, ax = plt.subplots()
# xs, ys = get_cdf_pts(pts[:, 0])
# plt.plot(xs, ys, label="unpruned")

# # xs, ys = get_cdf_pts(pts[:, 1])
# # plt.plot(xs, ys, label="pruned")

# os.system(f"wc -l {up} {p}")


# for bg in bgs:
#     print(f"dotnet tool run boogie {bg} /proverLog:unpruned/@FILE@.@PROC@.smt2 /timeLimit:1")