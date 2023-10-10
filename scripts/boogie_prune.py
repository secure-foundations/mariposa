from basic_utils import *
import numpy as np
from tqdm import tqdm
from plot_utils import *
from configer import Configer
from analyze_unsat_core import *
from analyze_trigger import load_quanti_stats

def export_smt_from_bpl():
    bgs = list_files_ext("boogies", ".bpl")
    print("""rule boogie
  command = timeout 60s dotnet tool run boogie $in /proverLog:pruned_new/@FILE@.@PROC@.smt2  /timeLimit:1 /prune /proverOpt:O:auto_config=false /proverOpt:O:type_check=true /proverOpt:O:smt.case_split=3 /proverOpt:O:smt.qi.eager_threshold=100 /proverOpt:O:smt.delay_units=true && touch $out""")

    for bg in bgs:
        # print(f"dotnet tool run boogie {bg} /proverLog:unpruned/@FILE@.@PROC@.smt2 /timeLimit:1")
        print(f"build {bg}.done : boogie {bg}")

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
    # TG = c.load_known_experiment("triggers")
    PN = c.load_known_experiment("pruned")

    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)
    # shake = c.load_known_project("d_fvbkv_shaked")
    
    items0, _, tally0 = load(orgi, PN)
    items1, _, tally1 = load(mini, PN)
    # items2, _, tally2 = load(shake, PN)

    keep = tally0 & tally1
    
    # keep = keep - items0[Stability.UNSOLVABLE]
    # keep = keep - items1[Stability.UNSOLVABLE]
    
    for cat in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        items0[cat] = items0[cat] & keep
        items1[cat] = items1[cat] & keep
        # items2[cat] = items2[cat] & keep

    werid = items1[Stability.UNSOLVABLE] & items0[Stability.STABLE]

    keeps = dict()
    for query in keep:
        orgi_path = orgi.clean_dir + "/" + query
        mini_path = mini.clean_dir + "/" + query
        # shake_path = shake.clean_dir + "/" + query
        keeps[query] = (orgi_path, mini_path)
    return items0, items1, keeps, werid

def analyze_d_fvbkv_prune():
    items0, items1, keep, werid = get_prune_keep("d_fvbkv_unpruned_new", "d_fvbkv_pruned_new")

    for i in werid:
        print(i)

    # PN = c.load_known_experiment("pruned")

    # mini = c.load_known_project("d_fvbkv_pruned_new")

    # rows = load_sum_table(mini, Z3_4_12_2, PN)
    # items = ANA.categorize_queries(rows, tally=True)
    # items = stem_file_paths(items)

    # for query_row in rows:
    #     plain_path = query_row[0]
    #     res, votes = ANA.categorize_query(query_row[2])
    #     if plain_path.split("/")[-1] in werid:
    #         print(plain_path)
            # ANA.dump_query_status(PN.enabled_muts, query_row[2])
            # print("")
            # print(plain_path, res, votes)

    # if proj.name == "d_fvbkv":
    #     for item in items:
    #         keep = set()
    #         for k in items[item]:
    #             for a in DF_FILES:
    #                 if k.startswith(a):
    #                     keep.add(k)
    #                     break
    #         items[item] = keep

    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)
    # ps2, _ = get_category_percentages(items2)

    table = [["", "unknown", "stable", "unstable", "unsolvable"]]
    table.append(["unpruned"] + [ps0[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]] )
    table.append(["pruned"] + [ps1[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]])
    # table.append(["shaked"] + [ps2[i] for i in [Stability.UNKNOWN, Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]])
    print(tabulate(table, headers="firstrow", tablefmt="github"))

    # pts0 = load_quanti_stats("d_fvbkv_unpruned", # 

    # plt.plot(xs, ys, label="pruned")

    # # xs, ys = get_cdf_pts((pts2[:, 2] + pts2[:, 3]) * 100 / (pts0[:, 0] + pts0[:, 1]))
    # # print(xs[:4], ys[:4])
    # plt.plot(xs, ys, label="shaked")
    
    # plt.xlim(0.001, 100)
    # plt.xscale("log")
    # plt.ylim(0)
    # plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    # plt.savefig(f"fig/boogie_prune.png", dpi=200)


def shake_d_fvbkv():
    orgi = c.load_known_project("d_fvbkv_unpruned")

    for q in orgi.list_queries():
        print(f"echo '{q}'")
        print(f"./target/release/mariposa --mutation tree-shake  --in-file-path {q} --out-file-path data/d_fvbkv_shaked/{q.split('/')[-1]}")

# export_smt_from_bpl()

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
analyze_d_fvbkv_prune()

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
