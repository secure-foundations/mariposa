from main import *

# Performance of original queries
    # Size histograms
    # Time histograms
    # 3 pairs of time comparisons (think the 2d graph where x and y axis are the diff categories of queries)
# Stability
    # Pure percentages of queries that are stable, unsolvable, unstable (for original query vs original unsat vs alpha renamed unsat)
    # CDF of success rates (original query vs original unsat vs alpha renamed unsat)

def get_sampled_query_names():
    files = []
    for sampled_name in list_smt2_files("data/unsat_cores/d_komodo_z3/alpha_renamed_sampled"):
        files.append(sampled_name.replace(".alpha_renamed.1.smt2", "").split("/")[-1])
    return files

# original query location: /home/yizhou7/mariposa/data/d_komodo_z3_clean/{query_name}.smt2
# min asserts location: /home/gelatin/mariposa/data/unsat_cores/d_komodo_z3/min_asserts/{query_name}.smt2
# alpha renamed location: /home/gelatin/mariposa/data/unsat_cores/d_komodo_z3/alpha_renamed_clean/{query_name}.alpha_renamed.1.smt2

ORIGINAL = "/home/yizhou7/mariposa/data/d_komodo_z3_clean/{query_name}.smt2"
MIN_ASSERTS = "/home/gelatin/mariposa/data/unsat_cores/d_komodo_z3/min_asserts/{query_name}.smt2"
ALPHA_RENAMED = "/home/gelatin/mariposa/data/unsat_cores/d_komodo_z3/alpha_renamed_sampled/{query_name}.alpha_renamed.1.smt2"

# original = ORIGINAL.format(query_name=query_name)
# min_asserts = MIN_ASSERTS.format(query_name=query_name)
# alpha_renamed = ALPHA_RENAMED.format(query_name=query_name)

def get_original_query_path(query_name):
    return ORIGINAL.format(query_name=query_name)

def get_min_asserts_query_path(query_name):
    return MIN_ASSERTS.format(query_name=query_name)

def get_alpha_renamed_query_path(query_name):
    return ALPHA_RENAMED.format(query_name=query_name)

def get_original_query_path_db(query_name):
    return '/'.join(get_original_query_path(query_name).split('/')[4:])

def get_min_asserts_query_path_db(query_name):
    return '/'.join(get_min_asserts_query_path(query_name).split('/')[4:])

def get_alpha_renamed_query_path_db(query_name):
    return '/'.join(get_alpha_renamed_query_path(query_name).split('/')[4:])


def track_non_stable(sampled_queries, project, solver, exp, ana):
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

    print("checking for originally unstable queries...")
    for query in sampled_queries:
        if query not in items[Stability.STABLE]:
            print("unstable query:", query)

    print("")
    print("listing unstable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSTABLE]:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
#       ana.dump_query_status(mutations, blob)

    print("")
    print("listing inconclusive queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.INCONCLUSIVE] or query not in sampled_queries:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
#       ana.dump_query_status(mutations, blob)
    
    print("")
    print("listing unsolvable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSOLVABLE] or query not in sampled_queries:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
#       ana.dump_query_status(mutations, blob)


c = Configer()
ANA = c.load_known_analyzer('default')
SOLVER = c.load_known_solver('z3_4_12_2')
OG_PROJ = c.load_known_project('d_komodo')
OG_EXP = c.load_known_experiment('main')

#AR_PROJ = c.load_known_project('arsample')
AR_EXP = c.load_known_experiment('ar')
# Stability analysis
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

#   print(tabulate(pp_table, tablefmt="github"))
    print("")
#   print("listing unstable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSTABLE]:
            continue
#       print("query:", row[0])
#       print(row[0])
        mutations, blob = row[1], row[2]
#       ana.dump_query_status(mutations, blob)

    print("")
    print("listing unsolvable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSOLVABLE]:
            continue
#       print("query:", row[0])
#       print(row[0])
        mutations, blob = row[1], row[2]
#       ana.dump_query_status(mutations, blob)

    print("")
    print("listing inconclusive queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.INCONCLUSIVE]:
            continue
#       print("query:", row[0])
#       print(row[0])
#       mutations, blob = row[1], row[2]
#       print(blob)
#       ana.dump_query_status(mutations, blob)

    print("")
    print("listing 50 random stable queries...")
    
    stable_queries = items[Stability.STABLE]
    # sample 50 stable queries
    stable_queries = random.sample(stable_queries, 50)
    for query in stable_queries:
        print(query)


# Pure percentages of queries that are stable, unsolvable, unstable (for original query vs original unsat vs alpha renamed unsat)
def generate_percentages():
    query_names = get_sampled_query_names()
    # print percentages and queries from original queries
#   print("Original queries results")
#   og_query_db_names = [get_original_query_path_db(query_name) for query_name in query_names]
#   track_non_stable(og_query_db_names, OG_PROJ, SOLVER, OG_EXP, ANA)
    print("Sampled alpha renamed queries")
    dump_multi_status(AR_PROJ, SOLVER, AR_EXP, ANA)

# generate_percentages()

UC_PROJ = c.load_known_project('d_komodo_uc')
UC_EXP = c.load_known_experiment('unsat_core')

UC_SOLVER = c.load_known_solver('z3_4_12_1')
# dump_multi_status(UC_PROJ, UC_SOLVER, UC_EXP, ANA)

# copy files listed in file from src to dst
def copy_files_from_file(src, dst, file, ext):
    with open(file, 'r') as f:
        for line in f:
            line = line.strip()
            line += ext
            shutil.copy(os.path.join(src, line), dst)

# # copy files in unstable, unsolvable, and stable from data/unsat_cores/d_komodo_z3/min_asserts/ to data/ar_small_exp/uc/unstable or unsolvable or stable
# copy_files_from_file('data/unsat_cores/d_komodo_z3/min_asserts/', 'data/ar_small_exp/uc/unstable/', 'unstable', '.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/min_asserts/', 'data/ar_small_exp/uc/unstable_less/', 'unstable_less', '.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/min_asserts/', 'data/ar_small_exp/uc/unsolvable/', 'unsolvable', '.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/min_asserts/', 'data/ar_small_exp/uc/stable/', 'stable', '.smt2')
copy_files_from_file('data/unsat_cores/d_komodo_z3/min_asserts/', 'data/ar_small_exp/uc/unstable_remaining/', 'unstable_remaining', '.smt2')
# 
# # copy files in unstable, unsolvable, and stable from data/unsat_cores/d_komodo_z3/alpha_renamed_clean/ verified-ARMdef.s.dfyCheckWellformed___module.__default.AddrInL2PageTable.alpha_renamed.1.smt2 to data/ar_small_exp/ar/unstable or unsolvable or stable
# copy_files_from_file('data/unsat_cores/d_komodo_z3/alpha_renamed_clean/', 'data/ar_small_exp/ar/unstable/', 'unstable', '.alpha_renamed.1.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/alpha_renamed_clean/', 'data/ar_small_exp/ar/unstable_less/', 'unstable_less', '.alpha_renamed.1.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/alpha_renamed_clean/', 'data/ar_small_exp/ar/unsolvable/', 'unsolvable', '.alpha_renamed.1.smt2')
# copy_files_from_file('data/unsat_cores/d_komodo_z3/alpha_renamed_clean/', 'data/ar_small_exp/ar/stable/', 'stable', '.alpha_renamed.1.smt2')
copy_files_from_file('data/unsat_cores/d_komodo_z3/alpha_renamed_clean/', 'data/ar_small_exp/ar/unstable_remaining/', 'unstable_remaining', '.alpha_renamed.1.smt2')

UC_EXP = c.load_known_experiment('uc')
AR_EXP = c.load_known_experiment('ar')
UC_UNSTABLE_PROJ = c.load_known_project('uc_unstable')
AR_UNSTABLE_PROJ = c.load_known_project('ar_unstable')

# dump_multi_status(UC_UNSTABLE_PROJ, SOLVER, UC_EXP, ANA)
# dump_multi_status(AR_UNSTABLE_PROJ, SOLVER, AR_EXP, ANA)


def investigate_inconclusive(project, solver, exp, ana):
    rows = load_sum_table(project, solver, cfg=exp)
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)

    print("project directory:", project.clean_dir)
    print("solver used:", solver.path)
    print("total queries:", len(rows))

    pp_table = [["category", "count", "percentage"]]
    for cat in {Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE}:
        pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])

    for row in rows:
        query = row[0]
        if query in items[Stability.INCONCLUSIVE] or "verified-ptables.i.dfyImpl___module.__default.lemma__WritablePages" in query or "verified-finalise.gen.dfyImpl___module.__default.va__lemma__kom__smc__finalise__success" in query:
#       print("query:", row[0])
            print(row[0])
            mutations, blob = row[1], row[2]
            print(blob)
            ana.dump_query_status(mutations, blob)

# investigate_inconclusive(UC_UNSTABLE_PROJ, SOLVER, UC_EXP, ANA)
# investigate_inconclusive(AR_UNSTABLE_PROJ, SOLVER, AR_EXP, ANA)
