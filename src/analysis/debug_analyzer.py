from base.factory import FACT
from base.query_analyzer import Stability as STB
from tabulate import tabulate


def analyze_debug():
    ana = FACT.get_analyzer("10sec")
    solver = FACT.get_solver("z3_4_13_0")
    cfg = FACT.get_config("verus_quick")

    projects = []

    for g in ["anvil", "anvil.v1", "anvil.v2"]:
    # for g in ["v_systems", "dbg.v1", "dbg.v2"]:
        g = FACT.get_group(g)
        p = g.get_project("base.z3")
        v = FACT.load_analysis(p, cfg, solver, ana)
        projects.append(v)

    v0, v1, v2 = projects

    for stb in [STB.UNSOLVABLE, STB.UNSTABLE]:
        table = []
        for qid in v0.stability_categories[stb].items:
            row = [qid]
            for v in projects[1:]:
                if qid not in v:
                    row.append("N/A")
                    continue
                ss = v[qid].stability
                if ss == STB.UNSTABLE:
                    print("tail " + qid + ".smt2.txt")
                row.append(ss)
            table.append(row)
        print(tabulate(table, headers=["qid", "v0", "v1", "v2"]))
