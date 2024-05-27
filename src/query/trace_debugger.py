import os
import re

from tabulate import tabulate
from base.defs import MARIPOSA
from utils.query_utils import parse_trace
from utils.system_utils import log_check, subprocess_run
import itertools
from sexpdata import loads, dumps

def top_qids(qids, top):
    rank = 0
    res = set()
    for qid in qids:
        res.add(qid) 
        rank += 1
        if rank == top:
            break
    return res

def compare_traces(left, right):
    l = top_qids(left, 10)
    r = top_qids(right, 10)
    print(f"common: {len(l.intersection(r))}")
    
def load_quantifier_ids(query_path):
    qids = set()
    pattern = re.compile(":qid (mariposa_qid_([0-9]+))")
    for line in open(query_path).readlines():
        if ":qid mariposa_qid" in line:
            match = pattern.search(line)
            if match:
                qids.add(match.group(1))
    return qids

def print_expr(expr, depth=0):
    prefix = "  " * depth
    res = ""
    if isinstance(expr, list):
        res += "\n" + prefix + "("
        if not isinstance(expr[0], list):
            res += str(expr[0]) + " "
            expr = expr[1:]
        all_atoms = all([not isinstance(e, list) for e in expr])
        if all_atoms:
            res += " ".join([str(e) for e in expr])
            res += ")"
        else:
            for e in expr:
                res += print_expr(e, depth=depth+1)
            res += "\n" + prefix + ")"
    else:
        res = "\n" + prefix + str(expr)
    return res

def format_print_sexpr(st):
    # print(loads(st))
    return print_expr(loads(st))

class TraceDebugger:
    def __init__(self, orig_path, trace_dir, core_path, woco_path):
        print(f"orig path: `{orig_path}`\n")
        if not os.path.exists(core_path):
            print(f"**WARN** no core is available!\n")
            core_qids = set()
        else:
            core_qids = load_quantifier_ids(core_path)
            print(f"core path: `{core_path}`\n")
            print(f"core qid count: {len(core_qids)}\n")

        remove_qids = set()
        traces = os.listdir(trace_dir)
        log_check(len(traces) != 0, f"no traces found in `{trace_dir}`")

        for trace in traces:
            trace_path = trace_dir + "/" + trace
            print(f"trace path: `{trace}`\n")

            f_trace = parse_trace(orig_path, trace_path)
            table = []

            for qid, count in f_trace.items():
                if qid in core_qids:
                    in_core = "Y"                        
                else:
                    if len(remove_qids) != 3:
                        remove_qids.add(":qid " + qid + ")")

                    in_core = "N"
                table.append((qid, count, in_core))

            print(tabulate(table, headers=["QID", "Count", "In Core"], tablefmt="github"))
            break

        if len(core_qids) == 0:
            print("\nno core available, nothing to remove\n")
            return
        
        if len(remove_qids) == 0:
            print("\nno qids to remove\n")
            return

        print("\nremoved:")

        # with open(woco_path, "w+") as woco_file:
        for line in open(orig_path).readlines():
            if any([qid in line for qid in remove_qids]):
                print(f"```\n{format_print_sexpr(line)}\n```")
                print("")
                continue
                # woco_file.write(line)
