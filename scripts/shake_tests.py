from basic_utils import *

STABLE_SAMPLES = "data/benchmarks/stable_core/"
UNSTABLE_SAMPLES = "data/test_set/"

print("""
rule shake
    command = ./target/release/mariposa -i $in -m tree-shake -o $out

rule z3
    command = ./solvers/z3-4.12.2 $in -T:10 > $out
""")

for query in list_files_ext(STABLE_SAMPLES, ".smt2"):
    base = os.path.basename(query)
    shake = f"gen/shake/{base}"
    print(f"build {shake}: shake {query}")
    print(f"build {shake}.rst: z3 {shake}")
