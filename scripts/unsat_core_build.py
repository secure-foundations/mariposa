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

class ExtendedProjectInfo:
    def __init__(self, orig_name):
        self.name = orig_name

        c = Configer()
        orig = c.load_known_project(orig_name)

        self.orig_dir = orig.clean_dir + "/"
        # the instrumented query
        self.inst_dir = f"data/unsat_cores/{orig_name}/inst/"
        # just the core output
        self.core_dir = f"data/unsat_cores/{orig_name}/core/"
        # the reduced query using the core
        self.mini_dir = f"data/unsat_cores/{orig_name}/min_asserts/"
        # the expanded query using the core
        self.mini_ext_dir = f"data/unsat_cores/{orig_name}/mini_ext/"

    def get_core_path(self, query):
        return self.core_dir + query.replace(".smt2", ".core")

def emit_build(orgi_name):
    proj = ExtendedProjectInfo(orgi_name)

    content = [BUILD_RULES]
    original_queries = list_smt2_files(proj.orig_dir)

    for original_query in original_queries:
        base = os.path.basename(original_query)
        inst_path = proj.inst_dir + base
        core_path = proj.get_core_path(base)
        content.append[f"build {core_path}: create-core {inst_path}"]

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

def list_missing_unsat_cores(orgi_name):
    c = Configer()

    print(BUILD_RULES)
    mini_name = PAIRS[orgi_name]
    UC = c.load_known_experiment("min_asserts")
    OP = c.load_known_experiment("opaque")
    orgi = c.load_known_project(orgi_name)
    mini = c.load_known_project(mini_name)
    proj = ExtendedProjectInfo(orgi_name)

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
                base = os.path.basename(query)
                orig_path = proj.orig_dir + base
                hint_path = proj.mini_dir + base
                ext_path = proj.mini_ext_dir + base
                # mini_ext_path = proj.mini_ext_dir + base
                print(f"build {ext_path}: expand-min-query {orig_path} | {hint_path}")
                print(f"    hint = {hint_path}")
            else:
                count += 1
        # print(round(100 * miss / len(tally0), 2), round(100 * count / len(tally0), 2))
    # print("give up bisection search at diff len: ", len(next_diff))


def inspect_expanded_core(orgi_name):
    proj = ExtendedProjectInfo(orgi_name)

    ext_queries = list_smt2_files(proj.mini_ext_dir)

    for ext_path in ext_queries:
        base = os.path.basename(ext_path)
        hint_path = proj.mini_dir + base
        ext_asserts = get_asserts(ext_path)
        orig_path = proj.orig_dir + base
        hint_asserts = get_asserts(hint_path)
        assert(key_set(hint_asserts).issubset(key_set(ext_asserts)))
        exted = len(key_set(ext_asserts) - key_set(hint_asserts))

        if exted > 50:
            print(exted)
            print(ext_path)
            # os.system("rm " + ext_path)
            # print(f"python3 scripts/unsat_core_search.py {orig_path} {hint_path} {ext_path} > {ext_path}.log")
        # out_path = f"data/unsat_cores/{orgi_name}/mini_ext/{query}"

if __name__ == "__main__":
    name = "fs_vwasm"
    # list_missing_unsat_cores(name)
    inspect_expanded_core(name)
