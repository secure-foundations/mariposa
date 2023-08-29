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

def print_as_table(items, ps):
    pp_table = [["category", "count", "percentage"]]
    total = 0
    for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        if len(items[cat]) == 0:
            continue
        pp_table.append([cat, len(items[cat]), round(ps[cat], 2)])
        total += len(items[cat])
    pp_table.append(["total", total, "-"])
    print(tabulate(pp_table, headers="firstrow", tablefmt="github"))
    print("")

ASSERT_LABELS = ["qfree", "others", "prelude", "type", "heap", "goal"]
NON_GOAL_LABELS = ["qfree", "others", "prelude", "type", "heap"]

import re

def get_dfy_assert_label(line):
    qid_pat = re.compile(r"qid \|([^\|])*\|")

    if not line.startswith("(assert"):
        return None
    
    if line.startswith("(assert (not (=>") or  \
        line.startswith("(assert (not (let"):
        return "goal"

    qid = re.search(qid_pat, line)
    if qid is None:
        if "forall" in line:
            return "others"
        else:
            return "qfree"
    qid = qid.group(0)
    if "DafnyPre" in qid:
        return "prelude"
    elif "funType" in qid:
        return "type"
    elif "Heap" in line:
        return "heap"
    else:
        return "others"

def add_back_dfy_asserts(label, origi_file, mini_file, out_file):
    assert label in ASSERT_LABELS
    adding = set()
    for line in open(origi_file, "r").readlines():
        if get_dfy_assert_label(line) == label:
            adding.add(line)
    out_file = open(out_file, "w")
    for line in open(mini_file, "r").readlines():
        if line in adding:
            continue
        if line.startswith("(check-sat)"):
            out_file.write("".join(adding))
            out_file.write(line)
            break
        out_file.write(line)

def get_dfy_asserts(file):
    f = open(file, "r")
    lines = f.readlines()
    labels = {k: 0 for k in ASSERT_LABELS}

    for line in lines:
        line = line.strip()
        label = get_dfy_assert_label(line)
        if label is not None:
            labels[label] += 1
    return labels

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

# for label in NON_GOAL_LABELS:
#     if os.path.exists(f"data/d_fvbkv_asserts/{label}"):
#         continue
#     os.mkdir(f"data/d_fvbkv_asserts/{label}") 

#     for query in stabilized:
#         orgi_path = orgi.clean_dir + "/" + query
#         # if not os.path.exists(orgi_path):
#         #     orgi_path = orgi_path.replace("dfy.", "dfyxxx")
#         # if not os.path.exists(orgi_path):
#         #     orgi_path = orgi_path.replace(".smt2", ".1.smt2")
#         mini_path = mini.clean_dir + "/" + query
#         out_path = f"data/d_fvbkv_asserts/{label}/{query}"
#         add_back_dfy_asserts(label, orgi_path, mini_path, out_path)

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

    print_compare_table(items0, ps0, items1, ps1)

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

    return items0, items1, keep

def print_basics(orgi_name, mini_name):
    UC = c.load_known_experiment("min_asserts")
    items0, items1, keep = get_basic_keep(orgi_name, mini_name)
    print("")
    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)
    print_compare_table(items0, ps0, items1, ps1)

    if orgi_name == "d_lvbkv_closed":
        p = "d_lvbkv_"
    elif orgi_name == "d_fvbkv":
        p = "d_fvbkv_"
    elif orgi_name == "d_komodo":
        p = "d_komodo_uc_"

    table = {Stability.STABLE: [], Stability.UNSTABLE: [], Stability.UNSOLVABLE: []}
    for label in NON_GOAL_LABELS:
        pname = p + label
        proj = c.load_known_project(pname)
        items, ps, tally = load(proj, UC)
        if items is None:
            for k in table.keys():
                table[k].append("-")
            continue
        for k in table.keys():
            table[k].append(len(items[k] & keep))

    table_ = [["category"] + NON_GOAL_LABELS]
    for k in table.keys():
        table_.append([k] + table[k])
    print(tabulate(table_, headers="firstrow", tablefmt="github"))

def print_asserts(orgi_name, mini_name):
    _, _, keep = get_basic_keep(orgi_name, mini_name)
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)

    pts0 = []
    pts1 = []
    for query in tqdm(keep):
        # if "Impl.i" not in query:
        #     continue
        orgi_path = orgi.clean_dir + "/" + query
        if not os.path.exists(orgi_path):
            orgi_path = orgi_path.replace("dfy.", "dfyxxx")
        if not os.path.exists(orgi_path):
            orgi_path = orgi_path.replace(".smt2", ".1.smt2")
        asserts = get_dfy_asserts(orgi_path)

        row = []
        for k in ASSERT_LABELS:
            row.append(asserts[k])
        assert (asserts["goal"] == 1)
        pts0.append(row)

        mini_path = mini.clean_dir + "/" + query
        asserts = get_dfy_asserts(mini_path)
        row = []
        for k in ASSERT_LABELS:
            row.append(asserts[k])
        assert (asserts["goal"] == 1)
        pts1.append(row)

    # print(pts0)
    # print(pts1)
    
    pts0 = np.array(pts0, dtype=np.float64)
    pts1 = np.array(pts1, dtype=np.float64)

    # for i in range(pts0.shape[0]):
    #     pts0[i, :] = pts0[i, :] * 100 / np.sum(pts0[i, :])
    #     pts1[i, :] = pts1[i, :] * 100 / np.sum(pts1[i, :])

    table = [ASSERT_LABELS]
    table.append(np.round(np.mean(pts0, axis=0), 2))
    table.append(np.round(np.mean(pts1, axis=0), 2))
    table.append(np.round(np.divide(np.mean(pts0, axis=0), np.mean(pts1, axis=0)), 2))
    print(tabulate(table, headers="firstrow", tablefmt="github"))

def get_query_stats(query_path):
    f = open(query_path, "r")
    count = 0
    for line in f.readlines():
        if line.startswith("(assert"):
            count +=1 
    return count        

def compare_queries(orgi_name, mini_name):
    items0, items1, keep = get_basic_keep(orgi_name, mini_name)
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)
    
    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)

    print("")

    print_compare_table(items0, ps0, items1, ps1)

    if os.path.exists(f"cache/{orgi_name}_{mini_name}_query_stats.pkl"):
        pts = cache_load(f"{orgi_name}_{mini_name}_query_stats.pkl")
    else:
        pts = np.zeros((len(keep), 2))
        for i, query in enumerate(tqdm(keep)):
            orgi_path = orgi.clean_dir + "/" + query
            if not os.path.exists(orgi_path):
                orgi_path = orgi_path.replace("dfy.", "dfyxxx")
            if not os.path.exists(orgi_path):
                orgi_path = orgi_path.replace(".smt2", ".1.smt2")
            mini_path = mini.clean_dir + "/" + query
            oc = get_query_stats(orgi_path)
            pts[i][0] = oc
            mc = get_query_stats(mini_path)
            pts[i][1] = mc
        cache_save(pts, f"{orgi_name}_{mini_name}_query_stats.pkl")
    return pts

PAIRS = {
    "d_komodo": "d_komodo_uc",
    "d_fvbkv": "d_fvbkv_uc",
    "d_lvbkv_closed": "d_lvbkv_uc",
    "fs_dice": "fs_dice_uc",
    "fs_vwasm": "fs_vwasm_uc",
}

fig, ax = plt.subplots()

for k in PAIRS.keys():
    pts = compare_queries(k, PAIRS[k])
    # print(sum(pts[:, 1] > 1), len(pts))
    # xs, ys = get_cdf_pts(pts[:, 1])
    xs, ys = get_cdf_pts(pts[:, 1] * 100 / pts[:, 0])
    # plt.hist(pts[:, 1] * 100 / pts[:, 0], bins=100, histtype='step', label="minimized")
    plt.plot(xs, ys, marker=",", label=k)

plt.legend()
plt.xscale("log")
plt.savefig("original.png")

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


# compare_queries("d_komodo", "d_komodo_uc")
# get_basic_keep("d_fvbkv", "d_fvbkv_uc")
# get_basic_keep("d_lvbkv_closed", "d_lvbkv_uc")
# print_asserts("d_komodo", "d_komodo_uc")
# print_asserts("d_lvbkv_closed", "d_lvbkv_uc")
# print_asserts("d_fvbkv", "d_fvbkv_uc")