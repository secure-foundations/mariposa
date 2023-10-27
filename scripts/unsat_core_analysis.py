from basic_utils import *
from db_utils import *
from cache_utils import *

from plot_utils import *
from configer import Configer
from unsat_core_build import *

def stem_file_paths(items):
    new_items = {}
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
    return new_items

def load_project(proj_name):
    c = Configer()
    Z3_4_12_2 = c.load_known_solver("z3_4_12_2")
    ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")

    if proj_name in UNSAT_CORE_PROJECTS:
        proj = c.load_known_project(proj_name)
        exp = c.load_known_experiment("baseline")
    elif proj_name in UNSAT_CORE_PROJECTS.values():
        proj = c.load_known_project(proj_name)
        exp = c.load_known_experiment("min_asserts")

    rows = load_sum_table(proj, Z3_4_12_2, exp)
    items = ANA.categorize_queries(rows, tally=True)
    items = stem_file_paths(items)
    tally = items.pop(Stability.TALLY)
    ps, _ = get_category_percentages(items)
    return items, ps, tally

def print_compare_table(items0, ps0, items1, ps1):
    table = [["category", "original", "minimized"]]
    for cat in items0:
        r0 = round(ps0[cat], 2)
        r1 = round(ps1[cat], 2)
        if r0 == 0 and r1 == 0:
            continue
        table.append([cat, f"{len(items0[cat])} ({r0})", f"{len(items1[cat])} ({r1})"])
    print(tabulate(table, headers="firstrow", tablefmt="github"))

def find_category(query, items):
    for cat in items:
        if query in items[cat]:
            return cat
    return None

class CoreStats:
    def __init__(self, orgi_name):
        o_items, _, o_tally = load_project(orgi_name)
        m_items, _, m_tally = load_project(UNSAT_CORE_PROJECTS[orgi_name])
        assert m_tally.issubset(o_tally)
        
        self.proj = ExtendedProjectInfo(orgi_name)
        self.o_items = o_items
        self.o_tally = o_tally
        self.m_items = m_items
        self.m_tally = m_tally

    def get_query_status(self):
        # the original is unsolvable, we won't get a core anyways 
        # actually we could if we try hard ...
        orig_unsolvable = set()
        # the original is solvable, but we don't get a core
        core_missing = set()
        # the original is solvable, but the minimized is not
        core_incomplete = set()
        # we patched the incomplete core, it should be solvable 
        patched = set()

        for query in self.o_tally:
            if query in self.o_items[Stability.UNSOLVABLE]:
                orig_unsolvable.add(query)
                continue

            if query not in self.m_tally:
                # cat = find_category(query, o_items)
                core_missing.add(query)
            elif query in self.m_items[Stability.UNSOLVABLE]:
                core_incomplete.add(query)

            ext_path = self.proj.mini_ext_dir + query
            # hint_path = self.proj.mini_dir + query
            # orig_path = self.proj.orig_dir + query

            if os.path.exists(ext_path):
                patched.add(query)

        return orig_unsolvable, core_missing, core_incomplete, patched

    def fix_missing(self):
        orig_unsolvable, core_missing, core_incomplete, patched = self.get_query_status()

        # for query in self.o_tally - orig_unsolvable - patched:
        #     hint_path = self.proj.mini_dir + query
        #     ext_path = self.proj.mini_ext_dir + query
        #     orig_path = self.proj.orig_dir + query

        #     # hint_asserts = get_asserts(hint_path)
        #     # ext_asserts = get_asserts(ext_path)

        #     cat = find_category(query, self.o_items)
        #     if query in core_missing:
        #         if cat == Stability.STABLE:
        #             print(f"python3 scripts/unsat_core_search.py reduce {orig_path} {ext_path} > {ext_path}.log")
        content = [BUILD_RULES]

        for query in patched:
            ext_path = self.proj.mini_ext_dir + query
            content += self.proj.emit_iterate_reduce_ext_query(ext_path)
            break

        print("\n".join(content))
            
        # print(f"python3 scripts/unsat_core_search.py reduce {ext_path} {ext_path} > {ext_path}.log")

# def get_basic_keep(orgi_name, mini_name):
#     c = Configer()
#     BA = c.load_known_experiment("baseline")

#     orgi = c.load_known_project(orgi_name)
#     mini = c.load_known_project(mini_name)

#     items0, ps0, tally0 = load(orgi, BA)
#     items1, ps1, tally1 = load(mini, UC)

#     keep = set()
#     # print(len(tally1 - tally0))

#     for query in tally0:
#         if query in items0[Stability.UNSOLVABLE]:
#             continue
#         if query not in tally1:
#             continue
#         if query in items1[Stability.UNSOLVABLE]:
#             continue
#         keep.add(query)

#     for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
#         items0[cat] = items0[cat] & keep
#         items1[cat] = items1[cat] & keep

#     keeps = dict()
#     for query in keep:
#         orgi_path = orgi.clean_dir + "/" + query
#         mini_path = mini.clean_dir + "/" + query
#         keeps[query] = (orgi_path, mini_path)

#     return items0, items1, keeps

# def plot_instability_reduction():
#     fig, ax = plt.subplots()
#     x = 0

#     # pts = np.zeros((len(PAIRS), 4))
#     # for i, origi in enumerate(PAIRS):
#     #     mini = PAIRS[origi]
#     #     items0, items1, keep = get_basic_keep(origi, mini)
#     #     ps0, _ = get_category_percentages(items0)
#     #     ps1, _ = get_category_percentages(items1)
#     #     pts[i] = ps0[Stability.UNSTABLE], len(items0[Stability.UNSTABLE]), ps1[Stability.UNSTABLE], len(items1[Stability.UNSTABLE])
#     # print(pts.tolist())

#     pts = [[5.583756345177665, 110.0, 1.6751269035532994, 33.0], [3.187721369539551, 162.0, 1.338055883510429, 68.0], [3.920031360250882, 200.0, 1.1760094080752646, 60.0], [1.0980966325036603, 15.0, 0.36603221083455345, 5.0], [0.06134969325153374, 1.0, 0.18404907975460122, 3.0]]

#     ticks = []

#     for i, k in enumerate(PAIRS.keys()):    
#         plt.bar(x, height=pts[i][0], label="original")
#         plt.text(x, pts[i][0], f"{int(pts[i][1])}")
#         ticks.append(x + 0.5)
#         plt.bar(x+1, height=pts[i][2], label="reduced")
#         plt.text(x+1, pts[i][2], f"{int(pts[i][3])}")
#         x += 4

#     plt.title("Unsat Core Instability Difference")
#     plt.xticks(ticks, PAIRS.keys())
#     plt.ylabel("percentage of unstable queries")
#     plt.savefig("fig/context/instability_diff.png", dpi=200)
#     plt.close()

# def get_quanti_stats(query_path):
#     fcount = 0
#     ecount = 0
#     qf = 0
#     nqf = 0
#     others = 0

#     for line in open(query_path).readlines():
#         quanti = False
#         if not line.startswith("(assert"):
#             others += 1
#             continue
#         cfc = line.count("(forall")
#         if cfc > 0:
#             quanti = True
#             fcount += cfc
        
#         cec = line.count("(exists")
        
#         if cec > 0:        
#             quanti = True
#             ecount += cec

#         if not quanti:
#             qf += 1
#         else:
#             nqf += 1
#     return fcount, ecount, qf, nqf, others

# def load_quanti_keep_stats(orgi_name):
#     if os.path.exists(f"cache/{orgi_name}_keep_quanti.pkl"):
#         pts = cache_load(f"{orgi_name}_keep_quanti.pkl")
#     else:
#         mini_name = PAIRS[orgi_name]
#         items0, items1, keep = get_basic_keep(orgi_name, mini_name)
#         pts = np.zeros((len(keep), 10))
#         for i, q in enumerate(tqdm(keep)):
#             pts[i] = get_quanti_stats(keep[q][0]) \
#                 + get_quanti_stats(keep[q][1])
#         cache_save(pts, f"{orgi_name}_keep_quanti.pkl")
#     return pts

# def get_assert_size(query_path):
#     size = 0
#     for line in open(query_path).readlines():
#         if line.startswith("(assert"):
#             size += len(line)
#     return size

# def plot_context_reduction():
#     fig, ax = plt.subplots()

#     for orgi_name in PAIRS.keys():
#         pts = load_quanti_keep_stats(orgi_name)
#         # print((pts[:, 2] + pts[:, 3]) * 100 / (pts[:, 7] + pts[:, 8]))
#         xs, ys = get_cdf_pts((pts[:, 7] + pts[:, 8]) * 100 / (pts[:, 2] + pts[:, 3]) )
#         plt.plot(xs, ys, marker=",", label=orgi_name, linewidth=2)

#     plt.ylabel("cumulative percentage of queries")
#     plt.xlabel("percentage of assertions retained in unsat core (log scale)")
#     plt.title("Unsat Core Context Retention")
#     plt.legend()
#     plt.xscale("log")
#     plt.xlim(0.001, 100)
#     plt.ylim(0)
#     plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
#     plt.savefig("fig/context/context_retention.png", dpi=200)
#     plt.close()

#     fig, ax = plt.subplots()

#     for k in PAIRS.keys():
#         if os.path.exists(f"cache/{k}_assert_size.pkl"):
#             pts = cache_load(f"{k}_assert_size.pkl")
#         else:
#             items0, items1, keep = get_basic_keep(k, PAIRS[k])
#             pts = np.zeros((len(keep),), dtype=np.float64)
#             for i, q in enumerate(tqdm(keep)):
#                 orgi_path, mini_path = keep[q]
#                 fs0 = get_assert_size(orgi_path)
#                 fs1 = get_assert_size(mini_path)
#                 pts[i] = fs1 / fs0
#             cache_save(pts, f"{k}_assert_size.pkl")            
#         xs, ys = get_cdf_pts(pts * 100)
#         plt.plot(xs, ys, marker=",", label=k, linewidth=2)

#     plt.ylabel("cumulative percentage of queries")
#     plt.xlabel("percentage of assert bytes retained in unsat core (log scale)")
#     plt.legend()
#     plt.title("Unsat Core Size Retention")
#     plt.ylim(0)
#     plt.xscale("log")
#     plt.xlim(0.001, 100)
#     plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
#     # ax.xaxis.set_major_formatter(mtick.PercentFormatter(xmax=1.0, decimals=3))
#     plt.savefig("fig/context/size_retention.png", dpi=200)
#     plt.close()

if __name__ == "__main__":
    # plot_context_reduction()
    # plot_instability_reduction()
    for p in UNSAT_CORE_PROJECTS:
        CoreStats(p).fix_missing()
    # CoreStats("d_lvbkv").list_missing_unsat_cores()