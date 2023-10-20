from basic_utils import *
from db_utils import *

from diff_smt import get_asserts
from configer import Configer
from cache_utils import *
from plot_utils import *

UNSAT_CORE_PAIRS = {
    "d_komodo": ("d_komodo_uc", "d_komodo_shake"),
    "d_fvbkv": ("d_fvbkv_uc", "d_fvbkv_shake"),
    "d_lvbkv_closed": ("d_lvbkv_uc", "d_lvbkv_shake"),
    "fs_dice": ("fs_dice_uc", "fs_dice_shake"),
    "fs_vwasm": ("fs_vwasm_uc", "fs_vwasm_shake"),
}

BENCH_PAIRS = {   
    "stable_core": "stable_core_shake",
    "stable_ext": "stable_ext_shake",
    "unstable_ext": "unstable_ext_shake",
    "unstable_core": "unstable_core_shake",
}

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

    ORG = c.load_known_experiment("baseline")
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

def emit_build_file_common():
    print("""
rule tree_shake
    command = ./target/release/mariposa -i $in -m tree-shake -o $out > $out.log

rule fun_assert
    command = ./target/release/mariposa -i $in -m fun-assert -o $out

rule diff_core
    command = python3 scripts/diff_smt.py $core $in > $out

rule z3
    command = ./solvers/z3-4.12.2 $in -T:10 > $out
""")


def load_project(name):
    c = Configer()

    orig = c.load_known_project(name)
    core, shake = UNSAT_CORE_PAIRS[name]

    shake = c.load_known_project(shake)
    core = c.load_known_project(core)

    return orig, core, shake

# def analyze_rewrite(name):
#     orig, core, shake = load_project(name)
    
#     count = 0
#     for core_path in tqdm(list_smt2_files(core.clean_dir)):
#     # for core_path in tqdm(list_smt2_files(core.clean_dir)):
#         base = os.path.basename(core_path)
#         origin_path = f"{orig.clean_dir}/{base}"
#         shake_path = f"{shake.clean_dir}/{base}"

#     #     origin_asserts = get_asserts(origin_path)
#         shake_asserts = get_asserts(shake_path)
#         core_asserts = get_asserts(core_path)

#         common_count = len(core_asserts.keys() & shake_asserts.keys())
#         if common_count != len(core_asserts):
#             count += 1

#             cmd = r'rg -e "\(assert" ' +  origin_path + ' | wc -l'
#             orgi = int(subprocess_run(cmd)[0])
#             cmd = r'rg -e "\(assert" ' +  shake_path  + ' | wc -l'
#             mini = int(subprocess_run(cmd)[0])
#             print(round(mini / orgi, 2))

#             print(shake_path)
#             print(f"cp {origin_path} temp/woot.smt2")
#             print(f"cp {core_path} temp/core.smt2")
#             print(f"cp {shake_path} temp/out.smt2")
#             print(len(shake_asserts.keys()), common_count, len(core_asserts))

#     print(count)
#     # shake_rst = shake_path.replace(".smt2", ".rst")
#     # print(f"build {shake_rst}: diff_core {shake_path}")
#     # print(f"    core = {core_path}")

def parse_stamps(filename):
    cmds0 = dict()
    for line in open(filename):
        line = line.split("|||")
        stamp = int(line[0].strip())
        line = line[1].replace(" ", "").strip().strip()
        cmds0[line] = stamp
    return cmds0

def get_asserts(filename):
    cmds0 = dict()
    for line in open(filename):
        if line.startswith("(assert "):
            cmds0[line.replace(" ", "").strip()] = line.strip()
    return cmds0

def emit_build_file(name):
    c = Configer()

    orig = c.load_known_project(name)
    if name in BENCH_PAIRS:
        shake = c.load_known_project(BENCH_PAIRS[name])
    else:
        shake = c.load_known_project(UNSAT_CORE_PAIRS[name][1])

    emit_build_file_common()

    for query in list_files_ext(orig.clean_dir, ".smt2"):
        if "s_komodo" in query:
            continue
        base = os.path.basename(query)
        # shake_path = f"data/shake_stable/{base}"
        shake_path = f"{shake.clean_dir}/{base}"
        # shake_rst = shake_path.replace(".smt2", ".rst")
        print(f"build {shake_path}: tree_shake {query}")
        # print(f"build {shake_rst}: z3 {shake_path}")

def analyze_rewrite2():
    c = Configer()
    fig, ax = plt.subplots()
    
    for name in BENCH_PAIRS:
        orig = c.load_known_project(name)
        shake = c.load_known_project(BENCH_PAIRS[name])
        
        data = []
        for origin_path in tqdm(list_files_ext(orig.clean_dir, ".smt2")):
            if "s_komodo" in origin_path:
                continue
            base = os.path.basename(origin_path)
            shake_path = f"{shake.clean_dir}/{base}"

            if base.startswith("fs_vwasm-"):
                core_path = base.replace("fs_vwasm-", "data/unsat_cores/fs_vwasm_z3/min_asserts/")
            elif base.startswith("fs_dice-"):
                core_path = base.replace("fs_dice-", "data/unsat_cores/fs_dice_z3/min_asserts/")
            elif base.startswith("d_komodo-"):
                core_path = base.replace("d_komodo-", "data/unsat_cores/d_komodo_z3/min_asserts/")
            elif base.startswith("d_fvbkv-"):
                core_path = base.replace("d_fvbkv-", "data/unsat_cores/d_fvbkv_z3/min_asserts/")
            elif base.startswith("d_lvbkv-"):
                core_path = base.replace("d_lvbkv-", "data/unsat_cores/d_lvbkv_z3/min_asserts/")

            if not os.path.exists(core_path):
                continue

            # shake_asserts = get_asserts(shake_path)
            core_asserts = get_asserts(core_path)

            # common_count = len(core_asserts.keys() & shake_asserts.keys())
            # if common_count != len(core_asserts):
            #     count += 1

            cmd = r'rg -e "\(assert" ' +  origin_path + ' | wc -l'
            orgi = int(subprocess_run(cmd)[0])
            cmd = r'rg -e "\(assert" ' +  shake_path  + ' | wc -l'
            mini = int(subprocess_run(cmd)[0])

            stamps = parse_stamps(shake_path + ".log")
            core_asserts = get_asserts(core_path)
            depths = [stamps[i] for i in core_asserts if i in stamps]
            miss = len([i for i in core_asserts if i not in stamps])
            # if miss != 0:
            #     print(f"cp {origin_path} temp/woot.smt2")
            #     print(f"cp {core_path} temp/core.smt2")
            #     print(f"cp {shake_path} temp/out.smt2")
            #     print(miss, len(core_asserts))
            # print(round(np.mean(depths), 2), np.max(depths))
            data.append([np.mean(depths), np.max(depths), orgi, mini, miss, len(core_asserts)])
        data = np.array(data, dtype=np.float32)
        # xs, ys = get_cdf_pts(data[:,0])
        # plt.plot(xs, ys, marker=",", label=f"mean_depth_{name}", linewidth=2)
        # print(name)
        # print(data[:,1])
        # plt.hist(data[:,1], label=f"mean_depth_{name}", alpha=0.5)
        print(name)
        print(np.sum(data[:,4]!= 0) * 100 / len(data))
        # xs, ys = get_cdf_pts(data[:,4] * 100 / data[:,5])
        # plt.plot(xs, ys, marker=",", label=f"retention_{name}", linewidth=2)
    plt.xlim(0, 100)
    plt.ylim(0)
    # plt.xscale("log")
    # plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    plt.savefig(f"fig/depth.png", dpi=200)
    plt.close()

def test_macro_finder():
    for query in list_smt2_files("data/benchmarks/unstable_ext"):
        if "d_" not in query:
            continue
        base = os.path.basename(query)
        out_path = f"data/unstable_ext_macro/{base}"
        out_path = open(out_path, "w")
        out_path.write("(set-option :smt.macro_finder true)\n")
        query = open(query).read()
        out_path.write(query)

def check_shake_rsts():
    for rst in list_files_ext("gen/shake_d_lvbkv", ".rst"):
        num = open(rst).readline().strip().split(" ")
        num = [int(i) for i in num]
        if num[0] != num[2]:
            print(rst)
        # cmd = r'rg -e "\(assert" ' +  "data/d_lvbkv_z3_clean/" + rst[:-4].split("/")[-1] + ' | wc -l'
        # orgi = int(subprocess_run(cmd)[0])
        # print(round(num[1] / orgi, 2))

if __name__ == "__main__":
    # test_macro_finder()
    # emit_build_file("d_fvbkv")
    # analyze_rewrite("d_fvbkv")

    # emit_build_file("d_fvbkv")
    # emit_build_file("d_lvbkv_closed")
    # emit_build_file("fs_dice")
    # emit_build_file("fs_vwasm")
    
    # analyze_rewrite("d_fvbkv")

    # emit_build_file("stable_core")
    # emit_build_file("stable_ext")
    emit_build_file("unstable_ext")
    # emit_build_file("unstable_core")
    # analyze_rewrite2()

    # check_shake_rsts()
    # os.system('grep -rnw "unknown" -l  gen/shake_satble/*.rst')