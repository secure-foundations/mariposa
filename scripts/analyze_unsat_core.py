from basic_utils import *
from db_utils import *
from vbkv_filemap import *
from cache_utils import *

from plot_utils import *
from configer import Configer

c = Configer()

def stem_file_paths(items):
    new_items = {}
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
    return new_items

Z3_4_12_2 = c.load_known_solver("z3_4_12_2")
ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")

def load(proj, exp):
    rows = load_sum_table(proj, Z3_4_12_2, exp)
    if rows is None:
        return None, None, None
    items = ANA.categorize_queries(rows, tally=True)
    items = stem_file_paths(items)
    tally = items.pop(Stability.TALLY)
    ps, _ = get_category_percentages(items)
    return items, ps, tally

def print_compare_table(items0, ps0, items1, ps1):
    table = [["category", "original", "minimized"]]
    for cat in items0:
        r0 = round(ps0[cat], 2)
        r1 = round(ps1[cat], 2)
        if r0 == 0 and r1 == 0:
            continue
        table.append([cat, f"{len(items0[cat])} ({r0})", f"{len(items1[cat])} ({r1})"])
    print(tabulate(table, headers="firstrow", tablefmt="github"))

def hacky_convert_file_path(path):
    return path.replace("dfyxxx", "dfy.").replace("1.smt2", "smt2")

def get_basic_keep(orgi_name, mini_name):
    c = Configer()
    UC = c.load_known_experiment("min_asserts")
    OP = c.load_known_experiment("opaque")
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)

    exp = OP if orgi_name == "d_lvbkv_closed" else UC
    items0, ps0, tally0 = load(orgi, exp)
    items1, ps1, tally1 = load(mini, UC)

    if orgi_name == "d_lvbkv_closed":
        for k, v in items0.items():
            items0[k] = set([hacky_convert_file_path(x) for x in v])
            tally0 = set([hacky_convert_file_path(x) for x in tally0])

    keep = set()
    # print(len(tally1 - tally0))

    for query in tally0:
        if query in items0[Stability.UNSOLVABLE]:
            continue
        if query not in tally1:
            continue
        if query in items1[Stability.UNSOLVABLE]:
            continue
        keep.add(query)

    if orgi_name == "d_fvbkv":
        keep_ = set()
        for k in keep:
            for a in DF_FILES:
                if k.startswith(a):
                    keep_.add(k)
                    break
        keep = keep_

    for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        items0[cat] = items0[cat] & keep
        items1[cat] = items1[cat] & keep

    keeps = dict()
    for query in keep:
        orgi_path = orgi.clean_dir + "/" + query
        if not os.path.exists(orgi_path):
            orgi_path = orgi_path.replace("dfy.", "dfyxxx")
        if not os.path.exists(orgi_path):
            orgi_path = orgi_path.replace(".smt2", ".1.smt2")
        mini_path = mini.clean_dir + "/" + query
        # print(orgi_path, mini_path)
        keeps[query] = (orgi_path, mini_path)

    return items0, items1, keeps

PAIRS = {
    "d_komodo": "d_komodo_uc",
    "d_fvbkv": "d_fvbkv_uc",
    "d_lvbkv_closed": "d_lvbkv_uc",
    "fs_dice": "fs_dice_uc",
    "fs_vwasm": "fs_vwasm_uc",
}

def plot_instability_reduction():
    fig, ax = plt.subplots()
    x = 0

    # pts = np.zeros((len(PAIRS), 4))
    # for i, origi in enumerate(PAIRS):
    #     mini = PAIRS[origi]
    #     items0, items1, keep = get_basic_keep(origi, mini)
    #     ps0, _ = get_category_percentages(items0)
    #     ps1, _ = get_category_percentages(items1)
    #     pts[i] = ps0[Stability.UNSTABLE], len(items0[Stability.UNSTABLE]), ps1[Stability.UNSTABLE], len(items1[Stability.UNSTABLE])
    # print(pts.tolist())

    pts = [[5.583756345177665, 110.0, 1.6751269035532994, 33.0], [3.187721369539551, 162.0, 1.338055883510429, 68.0], [3.920031360250882, 200.0, 1.1760094080752646, 60.0], [1.0980966325036603, 15.0, 0.36603221083455345, 5.0], [0.06134969325153374, 1.0, 0.18404907975460122, 3.0]]

    ticks = []

    for i, k in enumerate(PAIRS.keys()):    
        plt.bar(x, height=pts[i][0], label="original")
        plt.text(x, pts[i][0], f"{int(pts[i][1])}")
        ticks.append(x + 0.5)
        plt.bar(x+1, height=pts[i][2], label="reduced")
        plt.text(x+1, pts[i][2], f"{int(pts[i][3])}")
        x += 4

    plt.title("Unsat Core Instability Difference")
    plt.xticks(ticks, PAIRS.keys())
    plt.ylabel("percentage of unstable queries")
    plt.savefig("fig/unsat_core/instability_reduction.png", dpi=200)
    plt.close()

def get_quanti_stats(query_path, fs):
    fcount = 0
    ecount = 0
    total = 0
    for line in open(query_path).readlines():
        quanti = False
        if not line.startswith("(assert"):
            continue
        if "(forall" in line:
            quanti = True
            fcount += 1
            total += 1
        if "(exists" in line:
            quanti = True
            ecount += 1
            total += 1
        if not quanti:
            total += 1
    return fcount, ecount, total

def compare_queries(orgi_name, mini_name):
    items0, items1, keep = get_basic_keep(orgi_name, mini_name)

    if os.path.exists(f"cache/{orgi_name}_{mini_name}_query_stats.pkl"):
        pts = cache_load(f"{orgi_name}_{mini_name}_query_stats.pkl")
    else:
        pts = np.zeros((len(keep), 6))
        for i, query in enumerate(tqdm(keep)):
            orgi_path, mini_path = keep[query]
            c1, c2, c3 = get_quanti_stats(orgi_path, "fs" in orgi_name)
            pts[i][0] = c1
            pts[i][1] = c2
            pts[i][2] = c3
            c1, c2, c3 = get_quanti_stats(mini_path, "fs" in orgi_name)
            pts[i][3] = c1
            pts[i][4] = c2
            pts[i][5] = c3
        cache_save(pts, f"{orgi_name}_{mini_name}_query_stats.pkl")
    return pts

def get_assert_size(query_path):
    size = 0
    for line in open(query_path).readlines():
        if line.startswith("(assert"):
            size += len(line)
    return size

def plot_context_reduction():
    fig, ax = plt.subplots()

    for k in PAIRS.keys():
        pts = compare_queries(k, PAIRS[k])
        xs, ys = get_cdf_pts(pts[:, 5] * 100 / pts[:, 2])
        plt.plot(xs, ys, marker=",", label=k, linewidth=2)

    plt.ylabel("cumulative percentage of queries")
    plt.xlabel("percentage of assertions retained in unsat core (log scale)")
    plt.title("Unsat Core Context Retention")
    plt.legend()
    plt.xscale("log")
    plt.xscale("log")
    plt.xlim(0.001, 100)
    plt.ylim(0)
    plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    plt.savefig("fig/unsat_core/context_reduction.png", dpi=200)
    plt.close()

    fig, ax = plt.subplots()

    for k in PAIRS.keys():
        items0, items1, keep = get_basic_keep(k, PAIRS[k])
        if os.path.exists(f"cache/{k}_assert_size.pkl"):
            pts = cache_load(f"{k}_assert_size.pkl")
        else:
            pts = np.zeros((len(keep),), dtype=np.float64)
            for i, q in enumerate(tqdm(keep)):
                orgi_path, mini_path = keep[q]
                # print(orgi_path, mini_path)
                # get file size
                fs0 = get_assert_size(orgi_path)
                fs1 = get_assert_size(mini_path)
                pts[i] = fs1 / fs0
            cache_save(pts, f"{k}_assert_size.pkl")            
        xs, ys = get_cdf_pts(pts * 100)
        plt.plot(xs, ys, marker=",", label=k, linewidth=2)

    plt.ylabel("cumulative percentage of queries")
    plt.xlabel("percentage of assert bytes retained in unsat core (log scale)")
    plt.legend()
    plt.title("Unsat Core Size Retention")
    plt.ylim(0)
    # plt.xlim(0)
    plt.xscale("log")
    plt.xlim(0.001, 100)
    plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    # ax.xaxis.set_major_formatter(mtick.PercentFormatter(xmax=1.0, decimals=3))
    plt.savefig("fig/unsat_core/size_reduction.png", dpi=200)

def plot_quanti():
    for orgi_name in PAIRS.keys():
        fig, ax = plt.subplots()
        orgi = c.load_known_project(orgi_name)
        if os.path.exists(f"cache/{orgi_name}_quanti.pkl"):
            pts = cache_load(f"{orgi_name}_quanti.pkl")
        else:
            pts = np.zeros((len(orgi.list_queries()), 3))
            for i, q in enumerate(tqdm(orgi.list_queries())):
                c1, c2, c3 = get_quanti_stats(q, "fs" in orgi_name)
                pts[i] = [c1, c2, c3]
            cache_save(pts, f"{orgi_name}_quanti.pkl")

        xs = np.arange(0, len(pts[:, 1]), 1)
        # 0 fcount, 1 ecount, 2 total
        pts = pts[pts[:, 2].argsort()]
        # plt.plot(xs, pts[:, 2], "bo", markersize=1)
        # plt.plot(xs, pts[:, 1] + pts[:, 0], "bo", markersize=1)
        plt.fill_between(xs, pts[:, 2], pts[:, 0]+pts[:, 1], color="#332288")
        plt.fill_between(xs, pts[:, 0]+pts[:, 1], pts[:, 0], color="#44AA99")
        plt.fill_between(xs, pts[:, 0], np.zeros(len(xs)), color="#88CCEE")
        # plt.plot(xs, pts[:, 1], "bo", markersize=1)
        # plt.fill_between(xs, pts[:, 2], pts[:, 0]+pts[:, 1], color='grey', alpha=0.5)
        # plt.plot(xs, pts[:, 0]+pts[:, 1], marker="o", color="blue", markersize=1)
        # xs, ys = get_cdf_pts(pts[:, 5]/ pts[:, 2])
        # plt.plot(xs, ys, marker=",", label=k, linewidth=2)
        plt.ylim(0)
        plt.xlim(0, len(xs))
        plt.savefig(f"fig/quanti/{orgi_name}.png", dpi=200)
        plt.close()

# plot_instability_reduction()

# def print_basics(orgi_name, mini_name):
#     UC = c.load_known_experiment("min_asserts")
#     items0, items1, keep = get_basic_keep(orgi_name, mini_name)
#     print("")

#     print_compare_table(items0, ps0, items1, ps1)

#     if orgi_name == "d_lvbkv_closed":
#         p = "d_lvbkv_"
#     elif orgi_name == "d_fvbkv":
#         p = "d_fvbkv_"
#     elif orgi_name == "d_komodo":
#         p = "d_komodo_uc_"

#     table = {Stability.STABLE: [], Stability.UNSTABLE: [], Stability.UNSOLVABLE: []}
#     for label in NON_GOAL_LABELS:
#         pname = p + label
#         proj = c.load_known_project(pname)
#         items, ps, tally = load(proj, UC)
#         if items is None:
#             for k in table.keys():
#                 table[k].append("-")
#             continue
#         for k in table.keys():
#             table[k].append(len(items[k] & keep))

#     table_ = [["category"] + NON_GOAL_LABELS]
#     for k in table.keys():
#         table_.append([k] + table[k])
#     print(tabulate(table_, headers="firstrow", tablefmt="github"))

# def print_asserts(orgi_name, mini_name):
#     _, _, keep = get_basic_keep(orgi_name, mini_name)
#     orgi = c.load_known_project(orgi_name)
#     mini = c.load_known_project(mini_name)

#     pts0 = []
#     pts1 = []
#     for query in tqdm(keep):
#         # if "Impl.i" not in query:
#         #     continue
#         orgi_path = orgi.clean_dir + "/" + query
#         if not os.path.exists(orgi_path):
#             orgi_path = orgi_path.replace("dfy.", "dfyxxx")
#         if not os.path.exists(orgi_path):
#             orgi_path = orgi_path.replace(".smt2", ".1.smt2")
#         asserts = get_dfy_asserts(orgi_path)

#         row = []
#         for k in ASSERT_LABELS:
#             row.append(asserts[k])
#         assert (asserts["goal"] == 1)
#         pts0.append(row)

#         mini_path = mini.clean_dir + "/" + query
#         asserts = get_dfy_asserts(mini_path)
#         row = []
#         for k in ASSERT_LABELS:
#             row.append(asserts[k])
#         assert (asserts["goal"] == 1)
#         pts1.append(row)

#     # print(pts0)
#     # print(pts1)
    
#     pts0 = np.array(pts0, dtype=np.float64)
#     pts1 = np.array(pts1, dtype=np.float64)

#     # for i in range(pts0.shape[0]):
#     #     pts0[i, :] = pts0[i, :] * 100 / np.sum(pts0[i, :])
#     #     pts1[i, :] = pts1[i, :] * 100 / np.sum(pts1[i, :])

#     table = [ASSERT_LABELS]
#     table.append(np.round(np.mean(pts0, axis=0), 2))
#     table.append(np.round(np.mean(pts1, axis=0), 2))
#     table.append(np.round(np.divide(np.mean(pts0, axis=0), np.mean(pts1, axis=0)), 2))
#     print(tabulate(table, headers="firstrow", tablefmt="github"))

# orgi = c.load_known_project("fs_vwasm")
# for i, q in enumerate(orgi.list_queries()):
#     # get file size
#     fs0 = get_assert_size(q)
#     print(fs0, q)

# plot_quanti()

# def get_fstar_assert_label():
#     # f = open("woot.smt2", "r")
#     o, _, _ = subprocess_run('grep -E "qid [^\)]+" -o woot.smt2')
#     qids = o.split("\n")
#     prelude = 0
#     typing = 0
#     lowstar = 0
#     others = 0
#     for qid in sorted(qids):
#         if "FStar" in qid:
#             prelude += 1
#         elif "Prims" in qid:
#             prelude += 1
#         # elif "qid typing" in qid or "kinding" in qid:
#         #     typing += 1
#         # elif "LowStar" in qid:
#         #     lowstar += 1
#         # else:
#         #     others +=1 
#             print(qid)
#     print(prelude, typing, lowstar, others)

# get_fstar_assert_label()

# plot_context_reduction()