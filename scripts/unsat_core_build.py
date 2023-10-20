from basic_utils import *
from diff_smt import *
from analyze_unsat_core import *

BUILD_RULES = """
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-label-assert

rule create-core
    command = ./solvers/z3-4.8.5 -T:60 $in > $out
    
rule create-min-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-reduce-assert --core-file-path $core
    
rule expand-min-query
    command = python3 scripts/unsat_core_search.py $in $hint $out > $out.log
"""

def emit_build(orgi_name):
    c = Configer()
    orgi = c.load_known_project(orgi_name)

    content = [BUILD_RULES]

    INST_ROOT = f"data/unsat_cores/{orgi_name}/inst/"
    MINI_ROOT = f"data/unsat_cores/{orgi_name}/min-asserts/"
    CORE_ROOT = f"data/unsat_cores/{orgi_name}/core/"

    original_queries = list_smt2_files(orgi.clean_dir)

    for original_query in original_queries:
        base = os.path.basename(original_query)
        inst_query = INST_ROOT + base
        core_path = CORE_ROOT + base.replace(".smt2", ".core")
        content.append[f"build {core_path}: create-core {inst_query}"]
        
    # for original_query in original_queries:
    #     base = os.path.basename(original_query)
    #     inst_query = INST_ROOT + base
    #     content.append[f"build {inst_query}: instrument-query {original_query}"]

    # for original_query in original_queries:
    #     base = os.path.basename(original_query)
    #     mini_path = MINI_ROOT+ base
    #     core_path = CORE_ROOT + base.replace(".smt2", ".core")
    #     core = open(core_path).read()
    #     if "unsat" not in core:
    #         continue
    #     print(f"build {mini_path}: create-min-query {inst_query} | {core_path}")
    #     print(f"    core = {core_path}")

def list_missing_unsat_cores():
    c = Configer()

    for orgi_name in PAIRS.keys():
        if orgi_name != "fs_dice":
            continue
        print(BUILD_RULES)
        mini_name = PAIRS[orgi_name]
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

        # print(len(tally1 - tally0))
        count = 0
        miss = 0
        for query in tally0:
            if query in items0[Stability.UNSOLVABLE]:
                continue
            if query not in tally1:
                miss += 1
                # print(orgi.clean_dir + "/" + query)
                # print(mini.clean_dir + "/" + query)
                continue
            if query in items1[Stability.UNSOLVABLE]:
                for cat in items0:
                    if query in items0[cat]:
                        break
                if cat == Stability.STABLE:
                    orig_path = orgi.clean_dir + "/" + query
                    hint_path = mini.clean_dir + "/" + query
                    out_path = f"data/unsat_cores/{orgi_name}/mini_ext/{query}"
                    print(f"build {out_path}: expand-min-query {orig_path} | {hint_path}")
                    print(f"    hint = {hint_path}")
                    pass
                else:
                    count += 1
        # print(round(100 * miss / len(tally0), 2), round(100 * count / len(tally0), 2))
    # print("give up bisection search at diff len: ", len(next_diff))

if __name__ == "__main__":
    # list_missing_unsat_cores()
    list_missing_unsat_cores()
