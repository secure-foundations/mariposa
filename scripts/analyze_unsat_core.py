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
        pp_table.append([cat, len(items[cat]), round(ps[cat], 2)])
        total += len(items[cat])
    pp_table.append(["total", total, "-"])
    print(tabulate(pp_table, headers="firstrow", tablefmt="github"))
    print("")

def analyze_unsat_cores():
    c = Configer()
    UC = c.load_known_experiment("min_asserts")
    D_KOMODO = c.load_known_project("fs_dice")
    D_KOMODO_UC = c.load_known_project("fs_dice_uc")

    # D_KOMODO = c.load_known_project("d_komodo")
    # D_KOMODO_UC = c.load_known_project("d_komodo_uc")

    items0, ps0, tally0 = load(D_KOMODO, UC)
    items1, ps1, tally1 = load(D_KOMODO_UC, UC)

    rows = load_sum_table(D_KOMODO_UC, Z3_4_12_2, UC)
    items2 = {Stability.STABLE: set(), Stability.UNSTABLE: set(), Stability.UNSOLVABLE: set()}
    
    uc_tally = set()
    for row in rows:
        query = row[0].split("/")[-1]
        cat, _ = ANA.categorize_query(row[2])
        if query in items0[Stability.UNSOLVABLE]:
            items2[Stability.UNSOLVABLE].add(query)
        elif cat == Stability.UNSOLVABLE:
            # print(query)
            if query in items0[Stability.STABLE]:
                items2[Stability.STABLE].add(query)
            elif query in items0[Stability.UNSTABLE]:
                items2[Stability.UNSTABLE].add(query)
            else:
                items2[Stability.UNSOLVABLE].add(query)
        else:
            items2[cat].add(query)
        uc_tally.add(query)
    for query in tally0 - uc_tally:
        if query in items0[Stability.STABLE]:
            items2[Stability.STABLE].add(query)
        elif query in items0[Stability.UNSTABLE]:
            items2[Stability.UNSTABLE].add(query)
        else:
            items2[Stability.UNSOLVABLE].add(query)
    ps2, _ = get_category_percentages(items2)

    print("original:")
    print_as_table(items0, ps0)
    print("unsat cores:")
    print_as_table(items1, ps1)
    print("unsat cores adjusted:")
    print_as_table(items2, ps2)

def analyze_opaque():
    OP = c.load_known_experiment("opaque")
    d_lvbkv_opened = c.load_known_project("d_lvbkv_opened")
    d_lvbkv_closed = c.load_known_project("d_lvbkv_closed")
    items0, ps0, tally0 = load(d_lvbkv_opened, OP)
    items1, ps1, tally1 = load(d_lvbkv_closed, OP)

    print_as_table(items0, ps0)
    print_as_table(items1, ps1)

analyze_unsat_cores()

# projs = ["d_fvbkv_z3/", "d_komodo_z3/", "d_lvbkv_z3/", "fs_dice_z3/", "fs_vwasm_z3/"]

# for proj in projs:
#     insts = list_files(f"data/unsat_cores/{proj}/inst/")
#     cores = list_files(f"data/unsat_cores/{proj}/core/")

#     insts = set([os.path.basename(x) for x in insts])
#     cores = set([os.path.basename(x) for x in cores])

#     count = 0
#     for inst in insts:
#         if inst.replace(".smt2", ".core") not in cores:
#             count += 1
#     print(f"{proj} {round(count/len(insts), 2)}")
#             # print(f"data/unsat_cores/{proj}/inst/{inst}")
