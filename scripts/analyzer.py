from db_utils import *
import scipy.stats as stats
import numpy as np
import math
from tqdm import tqdm
import ast
from datetime import datetime

from configs.projects import *
from configs.experiments import *
from plot_utils import *
import matplotlib.pyplot as plt
from statsmodels.stats.proportion import proportions_ztest

COLORS = [
    "#FFB300", # Vivid Yellow
    "#803E75", # Strong Purple
    "#FF6800", # Vivid Orange
    "#A6BDD7", # Very Light Blue
    "#C10020", # Vivid Red
    "#CEA262", # Grayish Yellow
    "#817066", # Medium Gray
]

def get_color_map(keys):
    assert len(keys) <= len(COLORS)
    return {k: COLORS[i] for i, k in enumerate(keys)}

def percentage(a, b):
    return a * 100 / b

def append_summary_table(cfg, solver):
    con, cur = get_cursor(cfg.qcfg.db_path)
    solver_table = cfg.qcfg.get_solver_table_name(solver)
    summary_table = cfg.get_summary_table_name()

    res = cur.execute(f"""
        SELECT DISTINCT(query_path), result_code, elapsed_milli
        FROM {solver_table}
        WHERE query_path = vanilla_path""")

    vanilla_rows = res.fetchall()
    for (vanilla_path, v_rcode, v_time) in tqdm(vanilla_rows):
        res = cur.execute(f"""
            SELECT result_code, elapsed_milli, perturbation FROM {solver_table}
            WHERE vanilla_path = "{vanilla_path}" """)

        results = cfg.empty_muts_map([[], []])

        for row in res.fetchall():
            if row[2] is not None:
                results[row[2]][0].append(row[0])
                results[row[2]][1].append(row[1])

        summaries = []
        for perturb, (veri_res, veri_times) in results.items():
            summary = [str(perturb), veri_res, veri_times]
            summaries.append(summary)
        cur.execute(f"""INSERT INTO {summary_table}
            VALUES(?, ?, ?, ?, ?);""", 
            (str(solver), vanilla_path, v_rcode, v_time, str(summaries)))
    con.commit()
    con.close()

def build_summary_table(cfg):
    con, cur = get_cursor(cfg.qcfg.db_path)
    summary_table = cfg.get_summary_table_name()

    cur.execute(f"""DROP TABLE IF EXISTS {summary_table}""")

    cur.execute(f"""CREATE TABLE {summary_table} (
        solver varchar(10),
        vanilla_path TEXT,
        v_result_code varchar(10),
        v_elapsed_milli INTEGER,
        summaries TEXT)""")

    con.commit()
    con.close()

    for solver in cfg.samples:
        append_summary_table(cfg, solver)

def as_seconds(milliseconds):
    return milliseconds / 1000

def group_time_mean(times):
    assert len(times) != 0
    return as_seconds(np.mean(times))

def group_time_std(times):
    assert len(times) != 0
    return as_seconds(np.std(times))

def group_success_rate(vres):
    assert len(vres) != 0
    return percentage(vres.count("unsat"), len(vres))

def load_summary_table(cfg):
    con, cur = get_cursor(cfg.qcfg.db_path)
    summary_table_name = cfg.get_summary_table_name()
    summaries = dict()

    if not check_table_exists(cur, summary_table_name):
        con.close()
        return summaries

    for solver in cfg.samples:
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {summary_table_name}
            WHERE solver = ?""", (solver,))
        rows = res.fetchall()
        if len(rows) == 0:
            print(f"[INFO] skipping {summary_table_name} {solver}")
            continue
        nrows = []
        for row in rows:
            nrow = list(row)
            nrow[4] = ast.literal_eval(row[4])
            nrows.append(nrow)
        summaries[solver] = nrows
    con.close()
    return summaries

class Thresholds:
    def __init__(self):
        self.confidence = 0.05
        self.timeout = 1000

        self.unsolvable = 5
        assert 0 < self.unsolvable < 100

        self.res_stable = 95
        assert 0 < self.res_stable < 100

        self.time_stable = 1000

    def _categorize_group(self, vres, times):
        # success = 0
        # for i, x in enumerate(times):
        #     if as_seconds(x) <= self.timeout and vres[i] == "unsat":
        #         success += 1
        success = vres.count("unsat")
        size = len(vres)

        if success == 0:
            return "unsolvable"

        if success == size:
            return "stable"

        # value = self.unsolvable/100
        # _, p_value = proportions_ztest(count=success,
        #                                 nobs=len(vres),
        #                                 value=value, 
        #                                 alternative='smaller',
        #                                 prop_var=value)
        # if p_value <= self.confidence:
        #     return "unsolvable"

        # value = self.res_stable / 100
        # _, p_value = proportions_ztest(count=success, 
        #                                 nobs=len(vres),
        #                                 value=value,
        #                                 alternative='larger',
        #                                 prop_var=value)
        # if  p_value <= self.confidence:
        #     return "stable"

        return "unstable"
    
    def categorize_query(self, query_row):
        ress = set()
        pres, ptime = query_row[2], query_row[3]
        for (_, vres, times) in query_row[4]:
            ress.add(self._categorize_group(vres + [pres], times + [ptime]))
        if len(ress) == 1:
            return ress.pop()
        return "unstable"

def categorize_qeuries(rows, thresholds):
    unsolvables, stables, unstables = set(), set(), set()
    for query_row in rows:
        plain_path = query_row[1]
        res = thresholds.categorize_query(query_row)
        if res == "stable":
            stables.add(plain_path)
        elif res == "unsolvable":
            unsolvables.add(plain_path)
        else:
            unstables.add(plain_path)
    return (unsolvables, unstables, stables)

def remap_timeouts(rows, thresholds):
    for query_row in rows:
        if as_seconds(query_row[3]) >= thresholds.timeout:
            query_row[2] = "timeout"
        for (_, vres, times) in query_row[4]:
            for i, x in enumerate(times):
                if as_seconds(x) >= thresholds.timeout:
                    vres[i] = "timeout"

def get_category_precentages(items):
    items = [len(i) for i in items]
    total = sum(items)
    return [percentage(i, total) for i in items]

# def get_res_unstable_intervals(solver_summaries, res_stable_threshold, unsolvable_threshold):
#     categories = dict()
#     for solver, rows in solver_summaries.items():
#         categories[solver] = get_categories(rows, res_stable_threshold, unsolvable_threshold)
#     intervals = dict()
#     for solver, (unsolvables, stables, _, count) in categories.items():
#         max_ratio = percentage(count - len(stables), count)
#         min_ratio = percentage(len(unsolvables), count)
#         intervals[solver] = (min_ratio, max_ratio)
#         # print(solver, round(min_ratio, 2), "~" ,round(max_ratio, 2), 
#         #       round(max_ratio - min_ratio, 2))
#     return intervals

def do_stuff(cfg):
    s = load_summary_table(cfg)
    th = Thresholds()
    # colors = get_color_map(cfg.empty_muts_map())
    solver_count = len(s.keys())
    prev = None
    cut_figure, cut_aixs = setup_fig(solver_count, 1)
    for j, (solver, rows) in enumerate(s.items()):
        unsolvables = []
        unstables = []
        xs = [i for i in range(1, 63, 3)]
        xs.reverse()
        cc = []

        for i in xs:
            th.timeout = i
            remap_timeouts(rows, th)
            categories = categorize_qeuries(rows, th)
            cc.append(categories)
            ps = get_category_precentages(categories)
            unsolvables.append(ps[0])
            unstables.append(ps[1])

        # tt = 1
        # prev = None
        # for categories in reversed(cc):
        #     if prev is not None:
        #         print(tt)
        #         print("unsolvables -=", len(prev[0] - categories[0]))
        #         print("unstable -=", len(prev[1] - categories[1]))
        #         print("unstable +=", len(prev[0].intersection(categories[1])))
        #         print("unsolvables =", len(categories[0]))
        #         print("unstable =", len(categories[1]))
        #         print("")
        #     prev = categories
        #     tt += 3

        sp = cut_aixs
        if solver_count != 1:
            sp = cut_aixs[j]

        sp.plot(xs, unsolvables, marker=",", label="unsolvables")
        sp.plot(xs, unstables, marker=",", label="unstables")
        sp.legend()
        sp.set_title(f'{solver} timelimit cutoff vs category precentage')
        sp.set_ylabel("precentage of query")
        sp.set_xlabel("timelimit selection (seconds)")
        sp.set_xlim(left=1)
        sp.set_ylim(bottom=0)

    name = cfg.qcfg.name
    save_fig(cut_figure, f"{name}", f"fig/time_cutoff/{name}.png")
    # print(i, unsolvables, unstables)
    # print(s)

# def plot_basic(cfg, solver_summaries):
#     solver_count = len(cfg.samples)
#     time_figure, time_aixs = setup_fig(solver_count, 2)
#     colors = get_color_map(cfg.empty_muts_map())

#     for i, (solver, rows) in enumerate(solver_summaries.items()):
#         means = cfg.empty_muts_map()
#         stds = cfg.empty_muts_map()

#         for row in rows:
#             row_summaries = row[4]
#             for (perturb, vres, times) in row_summaries:
#                 if len(times) == 0:
#                     continue
#                 assert len(vres) == len(times)
#                 means[perturb].append(group_time_mean(times))
#                 stds[perturb].append(group_time_std(times))
#         if solver_count != 1:
#             plot_time_overall(time_aixs[i], means, stds, solver, colors)
#         else:
#             plot_time_overall(time_aixs, means, stds, solver, colors)
#     name = cfg.qcfg.name
#     save_fig(time_figure, f"{name}", f"fig/time_overall/{name}.png")

#     result_figure, result_aixs = setup_fig(solver_count, 2)
#     for i, (solver, rows) in enumerate(solver_summaries.items()):
#         srs = cfg.empty_muts_map()

#         for row in rows:
#             row_summaries = row[4]
#             for (perturb, vres, times) in row_summaries:
#                 if len(times) == 0:
#                     continue
#                 assert len(vres) == len(times)
#                 srs[perturb].append(group_success_rate(vres))
#         if solver_count != 1:
#             plot_result_overall(result_aixs[i], srs, solver, colors)
#         else:
#             plot_result_overall(result_aixs, srs, solver, colors)

#     save_fig(result_figure, f"{name}", f"fig/result_overall/{name}.png")

# def get_all_sr(plain_res, summaries):
#     # consider the plain one as well
#     all_vres = [plain_res]
#     for (_, vres, _) in summaries:
#         all_vres += vres
#     return group_success_rate(all_vres)

# import scipy

# def variance_test(times, time_std):
#     size = len(times)
#     std = np.std(times)
#     time_std = time_std * 1000
#     T = (size - 1) * ((std / time_std) ** 2)
#     c2 = scipy.stats.chi2.ppf(1-0.05, df=size-1)
#     return T > c2

# def get_time_unstable_ratios(solver_summaries, time_std_threshold):
#     ratios = dict()
#     for solver, rows in solver_summaries.items():
#         ratios[solver] = set()
#         count = len(rows)
#         for row in rows:
#             plain_path, summaries = row[1], row[4]
#             plain_res, plain_time = row[2], row[3]
#             all_sr = get_all_sr(plain_res, summaries)
#             if all_sr != 100:
#                 continue
#             for (_, _, times) in summaries:
#                 if variance_test(times, time_std_threshold):
#                     ratios[solver].add(plain_path)
#     ratios = {s: percentage(len(paths), count) for s, paths in ratios.items()}
#     return ratios

# def plot_time_stable(cfg, solver_summaries):
#     solver_count = len(cfg.samples)
#     time_figure, time_aixs = setup_fig(solver_count, 1)

#     for i, (solver, rows) in enumerate(solver_summaries.items()):
#         stds = cfg.empty_muts_map()
#         for row in rows:
#             summaries, plain_res = row[4], row[2]
#             all_sr = get_all_sr(plain_res, summaries)
#             if all_sr != 100:
#                 continue
#             for (perturb, _, times) in summaries:
#                 if len(times) == 0:
#                     continue
#                 stds[perturb].append(group_time_std(times))
#         sp = time_aixs[i]
#         for perturb, values in stds.items():
#             xs, ys = get_cdf_pts(values)
#             sp.set_ylabel("cumulative probability")
#             sp.plot(xs, ys, marker=",", label=perturb)
#             sp.set_title(f'{solver} stable query standard deviation cdf')
#         name = cfg.qcfg.name
#         save_fig(time_figure, f"{name}", f"fig/time_stable/{name}.png")

# def plot_time_mixed(cfg, solver_summaries):
#     solver_count = len(cfg.samples)
#     time_figure, time_aixs = setup_fig(solver_count, 1)

#     for i, (solver, rows) in enumerate(solver_summaries.items()):
#         means = cfg.empty_muts_map()
#         for row in rows:
#             summaries = row[4]
#             plain_path, plain_res = row[1], row[2]
#             all_sr = get_all_sr(plain_res, summaries)
#             if all_sr == 100 or all_sr == 0:
#                 continue
#             for (perturb, vres, times) in summaries:
#                 nts = [times[i] for i, x in enumerate(vres) if x != "timeout"]
#                 if len(nts) == 0:
#                     continue
#                 means[perturb].append(group_time_mean(nts))
#         sp = time_aixs[i]
#         for perturb, values in means.items():
#             xs, ys = get_cdf_pts(values)
#             sp.set_ylabel("cumulative probability")
#             sp.set_xlabel("mean response time (success only)")
#             sp.plot(xs, ys, marker=",", label=perturb)
#             sp.set_title(f'{solver} mixed queries cdf')
#         name = cfg.qcfg.name
#         save_fig(time_figure, f"{name}", f"fig/time_mixed/{name}.png")

# def as_md_row(row):
#     return "|" + "|".join(row) + "|"

# def as_md_table(table):
#     lines = [as_md_row(table[0])]
#     lines.append("|:---------:" * (len(table[0])) + "|")
#     for row in table[1:]:
#         lines.append(as_md_row(row))
#     lines.append("\n")
#     return "\n".join(lines)

# def plot_query_sizes(cfgs):
#     import os
#     figure, axis = setup_fig(1, 2)
#     colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

#     for cfg in cfgs:
#         clean_dir = cfg.qcfg.project.clean_dirs[Z3_4_11_2]
#         paths = list_smt2_files(clean_dir)
#         sizes = [] 
#         for path in paths:
#             sizes.append(os.path.getsize(path) / (8 * 1024 * 1024))
#         n = len(sizes)
#         label, color = cfg.qcfg.name, colors[label]
#         axis[0].plot(np.sort(sizes), np.arange(n), marker=",", label=label, color=color)
#         xs, ys = get_cdf_pts(sizes)
#         axis[1].plot(xs, ys, marker=",", label=label, color=color)

#     axis[0].legend()
#     axis[0].set_ylabel("cumulative probability")
#     axis[0].set_xlabel("query size (mb)")

#     axis[1].legend()
#     axis[1].set_xlabel("query size (mb)")

#     plt.tight_layout()
#     save_fig(figure, f"sizes", f"fig/sizes.pdf")

# def plot_time_cutoff(cfg):
#     summaries = load_summary(cfg)
#     thresholds = Thresholds(5, 95)
#     for i in reversed(range(3, 63, 3)):
#         for _, rows in summaries:
#             remap_query_summary_timeout(row, thresholds)
        # summaries = remap_summaries(summaries, i)
        # get_categories(rows, 95, 5)
        # vs = get_res_unstable_intervals(summaries, 90, 10)['z3_4_8_5']
        # print(i, vs[0], vs[1])
#     # get_categories(rows, res_stable_threshold, unsolvable_threshold):

# # def analyze_cond_fail(cfg):
# #     con, cur = get_cursor(cfg.qcfg.db_path)
# #     summary_table_name = cfg.get_summary_table_name()
# #     print(cfg.get_project_name())

# #     f = open("fig/cond_fail/" + summary_table_name + ".md", "w+")

# #     for i, solver in enumerate(cfg.samples):
# #         solver = str(solver)
# #         # print(solver, cfg.get_project_name())
# #         res = cur.execute(f"""SELECT * FROM {summary_table_name}
# #             WHERE solver = ?""", (solver, ))
# #         rows = res.fetchall()

# #         unsolvable = {p: set() for p in cfg.qcfg.enabled_muts}
# #         unsolvable["plain"] = set()

# #         for row in rows:
# #             if row[2] != "unsat":
# #                 unsolvable["plain"].add(row[1])

# #             summaries = ast.literal_eval(row[4])
# #             for (perturb, vres, _) in summaries:
# #                 if len(vres) != 0 and vres.count("unsat") ==0:
# #                     unsolvable[perturb].add(row[1])

# #         muts = ["plain", "shuffle", "rename", "sseed"]
# #         table = [[solver] + [m + "(" + str(len(unsolvable[m])) + ")" for m in muts]]

# #         for p1 in muts:
# #             row = [p1 + "(" + str(len(unsolvable[p1])) + ")"]
# #             for p2 in muts:
# #                 us1 = unsolvable[p1]
# #                 us2 = unsolvable[p2]
# #                 inter = len(us1.intersection(us2))
# #                 if p1 == p2:
# #                     row.append("-")
# #                 if len(us1) == 0:
# #                     row.append(f"nan")
# #                 else:
# #                     row.append(f"{inter}({str(round(inter * 100 / len(us1), 2))})")
# #             table.append(row)
# #         f.write(as_md_table(table))
# #     con.close()

# # def print_as_md_table(cfgs, summary_rows):
# #     solver_names = [str(s) for s in ALL_SOLVERS]
# #     project_names = [cfg.get_project_name() for  cfg in cfgs]

# #     row = [" "] + solver_names
# #     print("|" + "|".join(row) + "|")
# #     print("|:---------:" * (len(ALL_SOLVERS) + 1) + "|")
# #     for i, project in enumerate(project_names):
# #         row = [project]
# #         for (lp, hp, p) in summary_rows[i]:
# #             row.append(f"{str_percent(lp)}~{str_percent(hp)}, {str_percent(p)}")
# #         print("|" + "|".join(row) + "|")

# def analyze_d_komodo_sus(cfg):
#     assert cfg.qcfg.name == "D_KOMODO"
#     print("D_KOMODO total:")
#     os.system("""ls data/d_komodo_z3_clean/ | wc -l""")
#     print("D_KOMODO va__* total:")
#     os.system("""ls data/d_komodo_z3_clean/ | grep "va__" | wc -l""")
#     summaries = load_summary(cfg, 40)
#     categories = get_categories(summaries)

#     for other in [Z3_4_8_6, Z3_4_8_7, Z3_4_8_8, Z3_4_8_11, Z3_4_8_17, Z3_4_11_2]:
#         usol, ausol = 0, 0
#         for i in categories[other][0] - categories[Z3_4_8_5][0]:
#             if "va__" in i:
#                 usol += 1
#             ausol += 1

#         usta, austa = 0, 0
#         for i in categories[other][2] - categories[Z3_4_8_5][2]:
#             if "va__" in i:
#                 usta += 1
#             austa += 1

#         print(other)
#         print("va__* in additional unsolvable:", usol, "/", ausol)
#         print("va__* in additional unstable:", usta, "/", austa)

def dump_all(cfgs):
    projects = [cfg.qcfg.project for cfg in cfgs]
    project_names = [cfg.get_project_name() for cfg in cfgs]
    solver_names = [str(s) for s in ALL_SOLVERS]

    thres = Thresholds()

    data = []
    for cfg in cfgs:
        summaries = load_summary_table(cfg)
        row = []
        for solver in solver_names:
            if solver in summaries:
                rows = summaries[solver]
                remap_timeouts(rows, thres)
                items = categorize_qeuries(rows, thres)
                ps = get_category_precentages(items)
                row.append([ps[0], ps[0] + ps[1], -1])
            else:
                row.append([-1, -1, -1])
        data.append(row)
    # print(data)

    # data = [[[0.129366106080207, 1.5523932729624839, -1], [0.258732212160414, 1.2936610608020698, -1], [0.0, 1.2936610608020698, -1], [0.0, 1.1642949547218628, -1], [-1, -1, -1], [-1, -1, -1], [0.0, 1.6817593790426908, -1], [0.258732212160414, 1.4230271668822767, -1], [-1, -1, -1], [0.0, 1.2936610608020698, -1], [-1, -1, -1]], [[0.34079844206426485, 2.872444011684518, -1], [0.43816942551119764, 2.969814995131451, -1], [0.43816942551119764, 2.6777020447906525, -1], [0.2921129503407984, 2.0934761441090552, -1], [-1, -1, -1], [-1, -1, -1], [1.314508276533593, 9.785783836416748, -1], [-1, -1, -1], [-1, -1, -1], [2.0934761441090557, 11.538461538461538, -1], [-1, -1, -1]], [[-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [1.0178571428571428, 1.625, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1]], [[1.5954415954415955, 1.8233618233618234, -1], [1.5954415954415955, 1.7663817663817665, -1], [1.3105413105413106, 1.5384615384615385, -1], [1.2535612535612535, 1.3675213675213675, -1], [-1, -1, -1], [-1, -1, -1], [1.3675213675213675, 1.8803418803418803, -1], [1.2535612535612535, 1.8233618233618234, -1], [-1, -1, -1], [1.1396011396011396, 1.5954415954415955, -1], [-1, -1, -1]]]

    # colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

    # # # # print_as_md_table(data)
    # total = len(solver_names) * len(projects)
    bar_width = len(solver_names)/100
    # fig, aixs = plt.subplots(figsize=(total, 16))
    fig, ax = plt.subplots()

    br = np.arange(len(solver_names))
    br = [x - bar_width for x in br]

    for pi, project_row in enumerate(data):
        lps, hps, pds = [], [], []
        br = [x + bar_width for x in br]
        pcolor = COLORS[pi]
        for i, (lp, hp, p) in enumerate(project_row):
            if lp == hp and lp != 0:
                plt.scatter(br[i], lp, marker='_', color=pcolor, s=80)
            lps.append(lp)
            hps.append(hp)
            if projects[pi].orig_solver == ALL_SOLVERS[i]:
                plt.bar(br[i], hp-lp, bottom=lp, width = bar_width, color=pcolor, edgecolor='black')
            pds.append(p)

        hps_ = [hps[i] - lps[i] for i in range(len(hps))]
        plt.bar(br, height=lps, width=bar_width, color=pcolor, alpha=0.20)
        plt.bar(br, height=hps_, bottom=lps, width=bar_width, label=project_names[pi], color=pcolor)
        plt.bar(br, height=pds, bottom=hps, width=bar_width, color=pcolor, alpha=0.40)

    plt.ylim(bottom=0, top=15)
    plt.xlabel('solvers', fontsize = 12)
    plt.ylabel('unstable ratios', fontsize = 12)
    solver_lables = [f"{str(s).replace('_', '.')}\n{s.data[:-3]}" for s in ALL_SOLVERS]
    ax.tick_params(axis='both', which='major', labelsize=8)
    plt.xticks([r + bar_width for r in range(len(lps))], solver_lables, rotation=30, ha='right')
    plt.legend()
    plt.tight_layout()
    plt.savefig("fig/all.pdf")

# def dump_unsolvable(cfgs, timeout_threshold):
#     for cfg in cfgs:
#         summaries = load_summary(cfg, timeout_threshold)
#         categories = get_categories(summaries)
#         for solver, (unsolvables, _, _, _) in categories.items():
#             lname = f"data/sample_lists/{cfg.qcfg.name}_UNSOL_{solver}"
#             f = open(lname, "w+")
#             for item in unsolvables:
#                 f.write(item + "\n")
#             f.close()
