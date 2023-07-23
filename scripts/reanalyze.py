from main import *
from configer import *

def dump_multi_status(project, solver, exp, ana):
    rows = load_sum_table(project, solver, cfg=exp)
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)

    print("project directory:", project.clean_dir)
    print("solver used:", solver.path)
    print("total queries:", len(rows))

    pp_table = [["category", "count", "percentage"]]
    for cat in {Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE}:
        pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])

    print(tabulate(pp_table, tablefmt="github"))
    print("")
    print("listing unstable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSTABLE]:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

    print("")
    print("listing unsolvable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSOLVABLE]:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

    print("")
    print("listing inconclusive queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.INCONCLUSIVE]:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

def main():
    c = Configer()
    exp = c.load_known_experiment("pagetable")
    solver = c.load_known_solver("z3_4_12_2")
    project = c.load_known_project("pagetable")
    anadefault = c.load_known_analyzer("default")
    ana5sec = c.load_known_analyzer("verus_5sec")
    ana2sec = c.load_known_analyzer("verus_2sec")
    print("=====================================")
    print("DEFAULT ANALYZER RESULTS:")
    print("=====================================")
    dump_multi_status(project,  solver, exp, anadefault)
    print("")
#   print("=====================================")
#   print("5 SECOND TIMEOUT ANALYZER RESULTS:")
#   print("=====================================")
#   dump_multi_status(project,  solver, exp, ana5sec)
#   print("")
#   print("=====================================")
#   print("2 SECOND TIMEOUT ANALYZER RESULTS:")
#   print("=====================================")
#   dump_multi_status(project,  solver, exp, ana2sec)

if __name__ == "__main__":
    main()
