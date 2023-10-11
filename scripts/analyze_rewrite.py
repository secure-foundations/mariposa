from basic_utils import *
from db_utils import *

from configer import Configer

def stem_file_paths(items):
    new_items = {}
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
    return new_items

def load(proj, exp):
    c = Configer()
    Z3_4_12_2 = c.load_known_solver("z3_4_12_2")
    ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")
    
    rows = load_sum_table(proj, Z3_4_12_2, exp)
    if rows is None:
        return None, None, None
    items = ANA.categorize_queries(rows, tally=True)
    items = stem_file_paths(items)

    tally = items.pop(Stability.TALLY)
    ps, _ = get_category_percentages(items)
    return items, ps, tally

def print_compare_table(items0, ps0, items1, ps1):
    table = [["category", "original", "modified", "intersect"]]
    for cat in items0:
        r0 = round(ps0[cat], 2)
        r1 = round(ps1[cat], 2)
        overlap = len(items0[cat] & items1[cat])
        if r0 == 0 and r1 == 0:
            continue
        table.append([cat, f"{len(items0[cat])} ({r0})", f"{len(items1[cat])} ({r1})", overlap])
    print(tabulate(table, headers="firstrow", tablefmt="github"))

def get_basic_keep(org_name, mod_name):
    c = Configer()

    ORG = c.load_known_experiment("min_asserts")
    MOD = c.load_known_experiment("rewrite")

    org = c.load_known_project(org_name)
    mod = c.load_known_project(mod_name)

    items0, ps0, tally0 = load(org, ORG)
    items1, ps1, tally1 = load(mod, MOD)

    assert tally0 == tally1
    
    keeps = dict()
    for query in tally0:
        org_path = org.clean_dir + "/" + query
        mod_path = mod.clean_dir + "/" + query
        keeps[query] = (org_path, mod_path)

    for i in items0[Stability.STABLE] & items1[Stability.UNSTABLE]:
        print(i)
        # keeps.pop(i)

    print_compare_table(items0, ps0, items1, ps1)

    return items0, items1, keeps

def analyze_fun_assert():
    get_basic_keep("fs_vwasm", "fs_vwasm_fun_assert")

def emit_build_file(in_dir, out_dir):
    print("""
rule rewrite
    command = ./target/release/mariposa -i $in -m fun-assert -o $out

rule z3
    command = ./solvers/z3-4.12.2 $in -T:10 > $out
""")

    for query in list_files_ext(in_dir, ".smt2"):
        base = os.path.basename(query)
        shake = f"{out_dir}/{base}"
        print(f"build {shake}: rewrite {query}")
        # print(f"build {shake}.rst: z3 {shake}")

if __name__ == "__main__":
    emit_build_file(sys.argv[1], sys.argv[2])
    # os.system('grep -rnw "unknown" -l  gen/shake_satble/*.rst')
    # analyze_fun_assert()