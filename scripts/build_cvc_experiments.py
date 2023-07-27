import os
from basic_utils import *

def run_rules():
    return f"""
rule run-query
    command = (/usr/bin/time -o '$out' -a ./solvers/cvc5-1.0.3 --incremental $in --tlimit 60000) >> $out
"""

# create rules for data/verus_cvc/deleted_partial_order
def deleted_partial_order():
    print(run_rules())
    files = list_smt2_files("data/verus_cvc/deleted_partial_order")
    os.system("mkdir -p data/verus_cvc/deleted_partial_order_results")
    for f in files:
        f_out = f.replace(".smt2", ".out").replace("/deleted_partial_order/", "/deleted_partial_order_results/")
        print(f"build {f_out}: run-query {f}")

# create rules for data/verus_cvc/modified_partial_order
def modified_partial_order():
    print(run_rules())
    files = list_smt2_files("data/verus_cvc/modified_partial_order")
    os.system("mkdir -p data/verus_cvc/modified_partial_order_results")
    for f in files:
        f_out = f.replace(".smt2", ".out").replace("/modified_partial_order/", "/modified_partial_order_results/")
        print(f"build {f_out}: run-query {f}")

# create rules for data/verus_cvc/nr_deleted_partial_order
def nr_deleted_partial_order():
    print(run_rules())
    files = list_smt2_files("data/verus_cvc/nr_deleted_partial_order")
    os.system("mkdir -p data/verus_cvc/nr_deleted_partial_order_results")
    for f in files:
        f_out = f.replace(".smt2", ".out").replace("/nr_deleted_partial_order/", "/nr_deleted_partial_order_results/")
        print(f"build {f_out}: run-query {f}")

# deleted_partial_order()
# modified_partial_order()
nr_deleted_partial_order()
