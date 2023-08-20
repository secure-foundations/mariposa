from basic_utils import *
from db_utils import *
from vbkv_filemap import *

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
ANA = Analyzer(.05, 60, .05, .95, 0.8, "strict")

def load(proj, exp):
    rows = load_sum_table(proj, Z3_4_12_2, exp)
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

def analyze_unsat_cores0():
    c = Configer()
    UC = c.load_known_experiment("min_asserts")
    # orgi = c.load_known_project("fs_dice")
    # mini = c.load_known_project("fs_dice_uc")

    orgi = c.load_known_project("d_komodo")
    mini = c.load_known_project("d_komodo_uc")

    items0, ps0, tally0 = load(orgi, UC)
    items1, ps1, tally1 = load(mini, UC)

    assert len(tally1 - tally0) == 0

    print("original (unadjusted):")
    print_as_table(items0, ps0)
    print("minimized (unadjusted):")
    print_as_table(items1, ps1)

import re

ASSERT_LABELS = ["qfree", "others", "prelude", "type", "heap"]

def get_dfy_assert_label(line):
    qid_pat = re.compile(r"qid \|([^\|])*\|")

    if not line.startswith("(assert"):
        return None

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

def analyze_unsat_cores1():
    c = Configer()
    UC = c.load_known_experiment("min_asserts")
    orgi = c.load_known_project("d_komodo")
    mini = c.load_known_project("d_komodo_uc")

    # orgi = c.load_known_project("fs_dice")
    # mini = c.load_known_project("fs_dice_uc")

    items0, ps0, tally0 = load(orgi, UC)
    items1, ps1, tally1 = load(mini, UC)

    print("original (unadjusted):")
    print_as_table(items0, ps0)
    print("minimized (unadjusted):")
    print_as_table(items1, ps1)

    keep = set()
    assert len(tally1 - tally0) == 0

    for query in tally0:
        if query in items0[Stability.UNSOLVABLE]:
            continue
        if query not in tally1:
            continue
        if query in items1[Stability.UNSOLVABLE]:
            continue
        keep.add(query)
    
    for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        items0[cat] = items0[cat] & keep
        items1[cat] = items1[cat] & keep

    ps0, _ = get_category_percentages(items0)
    ps1, _ = get_category_percentages(items1)

    print("original (adjusted):")
    print_as_table(items0, ps0)
    print("minimized (adjusted):")
    print_as_table(items1, ps1)

    return  items0[Stability.UNSTABLE] & items1[Stability.STABLE]

def analyze_unsat_cores2():
    orgi = c.load_known_project("d_komodo")
    mini = c.load_known_project("d_komodo_uc")

    for label in ASSERT_LABELS:
        if os.path.exists(f"data/dfy_asserts/{label}"):
           continue
        os.mkdir(f"data/dfy_asserts/{label}") 
        for query in analyze_unsat_cores1():
            orgi_path = orgi.clean_dir + "/" + query
            mini_path = mini.clean_dir + "/" + query
            out_path = f"data/dfy_asserts/{label}/{query}"
            add_back_dfy_asserts(label, orgi_path, mini_path, out_path)

    # print(tabulate(table, headers=ASSERT_LABELS, tablefmt="github"))
    # table = np.array(table)
    # for i in range(len(ASSERT_LABELS)):
    #     # plt.hist(table[:, i], bins=20, label=ASSERT_LABELS[i], alpha=0.5)
    #     xs, ys = get_cdf_pts(table[:, i])
    #     plt.plot(xs, ys, label=ASSERT_LABELS[i], linewidth=2)
    # plt.legend()
    # plt.savefig("quanti.m.png")
 
def analyze_opaque():
    OP = c.load_known_experiment("opaque")
    d_lvbkv_opened = c.load_known_project("d_lvbkv_opened")
    d_lvbkv_closed = c.load_known_project("d_lvbkv_closed")
    items0, ps0, tally0 = load(d_lvbkv_opened, OP)
    items1, ps1, tally1 = load(d_lvbkv_closed, OP)

    print_as_table(items0, ps0)
    print_as_table(items1, ps1)

analyze_unsat_cores2()
