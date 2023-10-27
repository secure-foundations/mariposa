from basic_utils import *
from diff_smt import *
from configer import *

UNSAT_CORE_PROJECTS = {
    "d_komodo": "d_komodo_uc",
    "d_fvbkv": "d_fvbkv_uc",
    "d_lvbkv": "d_lvbkv_uc",
    "fs_dice": "fs_dice_uc",
    "fs_vwasm": "fs_vwasm_uc",
}

BUILD_RULES = """
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-label-assert

rule create-core
    command = ./solvers/z3-4.12.2 -T:120 $in > $out

rule create-min-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-reduce-assert --core-file-path $core

rule complete-min-query
    command = python3 scripts/unsat_core_search.py complete $in $hint $out > $out.log

rule reduce-query
    command = python3 scripts/unsat_core_search.py reduce $in $out > $out.log

rule iterate-reduce-query
    command = python3 scripts/unsat_core_search.py reduce $in $in > $out
"""

class ExtendedProjectInfo:
    def __init__(self, orig_name):
        self.name = orig_name

        c = Configer()
        orig = c.load_known_project(orig_name)
        core = c.load_known_project(UNSAT_CORE_PROJECTS[orig_name])

        self.orig_dir = orig.clean_dir + "/"
        # the instrumented query
        self.inst_dir = f"data/unsat_cores/{orig_name}/inst/"
        # just the core output
        self.core_dir = core.clean_dir + "/"
        # the reduced query using the core
        self.mini_dir = f"data/unsat_cores/{orig_name}/min_asserts/"
        # the expanded query using the core
        self.mini_ext_dir = f"data/unsat_cores/{orig_name}/mini_ext/"
        
        self.original_queries = list_smt2_files(self.orig_dir)

    def get_core_path(self, query):
        return self.core_dir + query.replace(".smt2", ".core")

    def emit_create_core(self, query):
        base = os.path.basename(query)
        inst_path = self.inst_dir + base
        core_path = self.get_core_path(base)

        return [f"build {inst_path}: instrument-query {query}", 
                f"build {core_path}: create-core {inst_path}"]

    def emit_all_create_core(self):
        content = [BUILD_RULES]

        for original_query in self.original_queries:
            content.extend(self.emit_create_core(original_query))

        print("\n".join(content))

    def emit_create_min_query(self, query):
        base = os.path.basename(query)
        inst_path = self.inst_dir + base
        mini_path = self.mini_dir + base
        core_path = self.get_core_path(base)

        core = open(core_path).read()

        if "unsat" not in core:
            return []

        return [f"build {mini_path}: create-min-query {inst_path} | {core_path}",
                f"    core = {core_path}"]
        
    def emit_all_create_min_query(self):
        content = [BUILD_RULES]

        for original_query in self.original_queries:
            content.extend(self.emit_create_min_query(original_query))

        print("\n".join(content))

    def emit_complete_min_query(self, query):
        base = os.path.basename(query)
        orig_path = self.orig_dir + base
        hint_path = self.inst_dir + base
        ext_path = self.mini_ext_dir + base

        assert os.path.exists(hint_path)

        return [f"build {ext_path}: complete-min-query {orig_path} | {hint_path}",
                f"    hint = {hint_path}"]

    def emit_iterate_reduce_ext_query(self, query):
        base = os.path.basename(query)
        ext_path = self.mini_ext_dir + base
        ext_log_path = ext_path + ".log"

        return [f"build {ext_log_path}: iterate-reduce-query {ext_path}"]

# def inspect_expanded_core(orgi_name):
#     proj = ExtendedProjectInfo(orgi_name)

#     ext_queries = list_smt2_files(proj.mini_ext_dir)

#     for ext_path in ext_queries:
#         base = os.path.basename(ext_path)
#         hint_path = proj.mini_dir + base
#         ext_asserts = get_asserts(ext_path)
#         orig_path = proj.orig_dir + base
#         hint_asserts = get_asserts(hint_path)
#         # not necessarily true, since we may have removed some asserts
#         # assert(key_set(hint_asserts).issubset(key_set(ext_asserts)))
#         exted = len(key_set(ext_asserts) - key_set(hint_asserts))

#         if exted > 50:
#             print(exted)
#             print(ext_path)
#             # os.system("rm " + ext_path)
#             # print(f"python3 scripts/unsat_core_search.py {orig_path} {hint_path} {ext_path} > {ext_path}.log")
#         # out_path = f"data/unsat_cores/{orgi_name}/mini_ext/{query}"

if __name__ == "__main__":
    pass
    # name = "d_komodo"
    # for name in PAIRS:
    # list_missing_unsat_cores(name)
    # inspect_expanded_core(name)
