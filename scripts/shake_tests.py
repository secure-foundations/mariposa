from basic_utils import *
from configer import *
import sys

STABLE_SAMPLES = "data/benchmarks/stable_core/"
UNSTABLE_SAMPLES = "data/test_set/"

def emit_build_file(in_dir, out_dir):
    print("""
rule shake
    command = ./target/release/mariposa -i $in -m tree-rewrite -o $out

rule z3
    command = ./solvers/z3-4.12.2 $in -T:10 > $out
""")

    for query in list_files_ext(in_dir, ".smt2"):
        base = os.path.basename(query)
        shake = f"{out_dir}/{base}"
        if "fs_" in query:
            continue
        print(f"build {shake}: shake {query}")
        print(f"build {shake}.rst: z3 {shake}")

emit_build_file(sys.argv[1], sys.argv[2])

# os.system('grep -rnw "unknown" -l  gen/shake_satble/*.rst')

# c = Configer()
# p = c.load_known_project("fs_dice")

# for query in p.list_queries():
#     base = os.path.basename(query)
#     shake = f"data/fs_dice_forall_fun/{base}"
#     print(f"build {shake}: shake {query}")
#     # print(f"build {shake}.rst: z3 {shake}")
