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
        res = cur.execute("DROP VIEW IF EXISTS query_view");
        res = cur.execute(f"""CREATE VIEW query_view AS 
            SELECT result_code, elapsed_milli, perturbation FROM {solver_table}
            WHERE query_path != vanilla_path
            AND vanilla_path = "{vanilla_path}" """)

        results = dict()

        for perturb in cfg.qcfg.enabled_muts:
            res = cur.execute(f"""SELECT * FROM query_view
                WHERE perturbation = ?""", (perturb,))
            rows = res.fetchall()
            sample_size = len(rows)
            veri_res = [r[0] for r in rows]
            veri_times = [r[1] for r in rows]

            if sample_size == 0:
                print(f"[WARN] 0 sample size encountered: {vanilla_path}")
                results[perturb] = (0, 0, [], [])
                continue

            p = veri_res.count("unsat") / sample_size

            # get the sample standard deviation
            time_stdev = np.std(veri_times, ddof=1)
            results[perturb] = (p, time_stdev, veri_res, veri_times)

        summaries = []
        for perturb, (_, _, veri_res, veri_times) in results.items():
            summary = (str(perturb), veri_res, veri_times)
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
    # ec = vres.count("error")
    # if ec != 0:
    #     print(ec)
    return percentage(vres.count("unsat"), len(vres))

def remap_timeouts(summaries, timeout_threshold=None):
    # new_summaries = []
    # for (p, vres, times) in summaries:
    #     new_summaries.append((p, vres[:30], times[:30]))
    # summaries = new_summaries 
    if timeout_threshold is None:
        return summaries
    for (_, vres, times) in summaries:
        to_indices = [i for i, x in enumerate(times) if as_seconds(x) >= timeout_threshold]
        for i in to_indices:
            vres[i] = "timeout"
    return summaries

def load_summary(cfg, timeout_threshold):
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
            continue
        nrows = []
        for row in rows:
            nrow = list(row)
            # remap the plain one as well
            if timeout_threshold is not None and as_seconds(nrow[3]) >= timeout_threshold:
                nrow[2] = "timeout"
            nrow[4] = remap_timeouts(ast.literal_eval(row[4]), timeout_threshold)
            nrows.append(nrow)
        summaries[solver] = nrows
    con.close()
    return summaries

def plot_basic(cfg, solver_summaries):
    solver_count = len(cfg.samples)
    time_figure, time_aixs = setup_fig(solver_count, 2)
    colors = get_color_map(cfg.empty_muts_map())

    for i, (solver, rows) in enumerate(solver_summaries.items()):
        means = cfg.empty_muts_map()
        stds = cfg.empty_muts_map()

        for row in rows:
            row_summaries = row[4]
            for (perturb, vres, times) in row_summaries:
                if len(times) == 0:
                    continue
                assert len(vres) == len(times)
                means[perturb].append(group_time_mean(times))
                stds[perturb].append(group_time_std(times))
        if solver_count != 1:
            plot_time_overall(time_aixs[i], means, stds, solver, colors)
        else:
            plot_time_overall(time_aixs, means, stds, solver, colors)
    name = cfg.qcfg.name
    save_fig(time_figure, f"{name}", f"fig/time_overall/{name}.png")

    result_figure, result_aixs = setup_fig(solver_count, 2)
    for i, (solver, rows) in enumerate(solver_summaries.items()):
        srs = cfg.empty_muts_map()

        for row in rows:
            row_summaries = row[4]
            for (perturb, vres, times) in row_summaries:
                if len(times) == 0:
                    continue
                assert len(vres) == len(times)
                srs[perturb].append(group_success_rate(vres))
        if solver_count != 1:
            plot_result_overall(result_aixs[i], srs, solver, colors)
        else:
            plot_result_overall(result_aixs, srs, solver, colors)

    save_fig(result_figure, f"{name}", f"fig/result_overall/{name}.png")

def get_all_sr(plain_res, summaries):
    # consider the plain one as well
    all_vres = [plain_res]
    for (_, vres, _) in summaries:
        all_vres += vres
    return group_success_rate(all_vres)

def is_group_unsolvable(vres, unsolvable_threshold):
    success = vres.count("unsat")
    size = len(vres)
    if size == 10:
        if success == 10:
            success = 30
        size = 30
    value = unsolvable_threshold/100
    stat, p_value = proportions_ztest(count=success, nobs=size, value=value, alternative='smaller', prop_var=value)
    if p_value > 0.05:
        return False
    else:
        return True

def is_group_stable(vres, res_stable_threshold):
    success = vres.count("unsat")
    size = len(vres)
    if size == 10:
        if success == 10:
            success = 30
        size = 30
    value = res_stable_threshold/100
    stat, p_value = proportions_ztest(count=success, nobs=size, value=value, alternative='larger', prop_var=value)
    if p_value > 0.05:
        return False
    else:
        return True

def check_group(vres, res_stable_threshold, unsolvable_threshold):
    unsolvable = is_group_unsolvable(vres, unsolvable_threshold)
    stable = is_group_stable(vres, res_stable_threshold)
    if unsolvable:
        return "unsolvable"
    if stable:
        return "stable"
    return "unstable"

def check_groups(summaries, res_stable_threshold, unsolvable_threshold):
    ress = set()
    for (_, vres, _) in summaries:
        ress.add(check_group(vres, res_stable_threshold, unsolvable_threshold))
    if len(ress) == 1:
        return ress.pop()
    return "unstable"

def get_categories(solver_summaries, res_stable_threshold, unsolvable_threshold):
    categories = dict()
    for solver, rows in tqdm(solver_summaries.items()):
        unsolvables, stables, unstables = set(), set(), set()
        count = 0
        for row in rows:
            summaries = row[4]
            plain_path, plain_res = row[1], row[2]
            res = check_groups(summaries, res_stable_threshold, unsolvable_threshold)
            if res == "stable":
                stables.add(plain_path)
            elif res == "unsolvable":
                unsolvables.add(plain_path)
            else:
                unstables.add(plain_path)
            count += 1
        categories[solver] = (unsolvables, stables, unstables, count)
    return categories

def get_res_unstable_intervals(solver_summaries, res_stable_threshold, unsolvable_threshold):
    categories = get_categories(solver_summaries, res_stable_threshold, unsolvable_threshold)
    intervals = dict()
    for solver, (unsolvables, stables, _, count) in categories.items():
        max_ratio = percentage(count - len(stables), count)
        min_ratio = percentage(len(unsolvables), count)
        intervals[solver] = (min_ratio, max_ratio)
        # print(solver, round(min_ratio, 2), "~" ,round(max_ratio, 2), 
        #       round(max_ratio - min_ratio, 2))
    return intervals

import scipy

def variance_test(times, time_std):
    size = len(times)
    std = np.std(times)
    time_std = time_std * 1000
    T = (size - 1) * ((std / time_std) ** 2)
    c2 = scipy.stats.chi2.ppf(1-0.05, df=size-1)
    return T > c2

def get_time_unstable_ratios(solver_summaries, time_std_threshold):
    ratios = dict()
    for solver, rows in solver_summaries.items():
        ratios[solver] = set()
        count = len(rows)
        for row in rows:
            plain_path, summaries = row[1], row[4]
            plain_res, plain_time = row[2], row[3]
            all_sr = get_all_sr(plain_res, summaries)
            if all_sr != 100:
                continue
            for (_, _, times) in summaries:
                if variance_test(times, time_std_threshold):
                    ratios[solver].add(plain_path)
    ratios = {s: percentage(len(paths), count) for s, paths in ratios.items()}
    return ratios

def plot_time_stable(cfg, solver_summaries):
    solver_count = len(cfg.samples)
    time_figure, time_aixs = setup_fig(solver_count, 1)

    for i, (solver, rows) in enumerate(solver_summaries.items()):
        stds = cfg.empty_muts_map()
        for row in rows:
            summaries, plain_res = row[4], row[2]
            all_sr = get_all_sr(plain_res, summaries)
            if all_sr != 100:
                continue
            for (perturb, _, times) in summaries:
                if len(times) == 0:
                    continue
                stds[perturb].append(group_time_std(times))
        sp = time_aixs[i]
        for perturb, values in stds.items():
            xs, ys = get_cdf_pts(values)
            sp.set_ylabel("cumulative probability")
            sp.plot(xs, ys, marker=",", label=perturb)
            sp.set_title(f'{solver} stable query standard deviation cdf')
        name = cfg.qcfg.name
        save_fig(time_figure, f"{name}", f"fig/time_stable/{name}.png")

def plot_time_mixed(cfg, solver_summaries):
    solver_count = len(cfg.samples)
    time_figure, time_aixs = setup_fig(solver_count, 1)

    for i, (solver, rows) in enumerate(solver_summaries.items()):
        means = cfg.empty_muts_map()
        for row in rows:
            summaries = row[4]
            plain_path, plain_res = row[1], row[2]
            all_sr = get_all_sr(plain_res, summaries)
            if all_sr == 100 or all_sr == 0:
                continue
            for (perturb, vres, times) in summaries:
                nts = [times[i] for i, x in enumerate(vres) if x != "timeout"]
                if len(nts) == 0:
                    continue
                means[perturb].append(group_time_mean(nts))
        sp = time_aixs[i]
        for perturb, values in means.items():
            xs, ys = get_cdf_pts(values)
            sp.set_ylabel("cumulative probability")
            sp.set_xlabel("mean response time (success only)")
            sp.plot(xs, ys, marker=",", label=perturb)
            sp.set_title(f'{solver} mixed queries cdf')
        name = cfg.qcfg.name
        save_fig(time_figure, f"{name}", f"fig/time_mixed/{name}.png")

# def str_percent(p):
#     if np.isnan(p):
#         return "-"
#     return str(round(p, 2)) + "%"

# def str_interval(interval):
#     return f"{str_percent(interval[0])}, {str_percent(interval[1])}"

# def print_summary_data(cfgs):
#     rows = []
#     for cfg in cfgs:
#         # print(cfg.get_project_name())
#         row = []
#         intervals = plot_result_overall(cfg)
#         bounds = plot_time_overall(cfg)
#         for solver in ALL_SOLVERS:
#             item = [np.nan, np.nan, np.nan]
#             if solver in intervals:
#                 item[0] = intervals[solver][0]
#                 item[1] = intervals[solver][1]
#             if solver in bounds:
#                 item[2] = bounds[solver]
#             row.append(item)
#         rows.append(row)
#     print(rows)

def as_md_row(row):
    return "|" + "|".join(row) + "|"

def as_md_table(table):
    lines = [as_md_row(table[0])]
    lines.append("|:---------:" * (len(table[0])) + "|")
    for row in table[1:]:
        lines.append(as_md_row(row))
    lines.append("\n")
    return "\n".join(lines)

def plot_query_sizes(cfgs):
    import os
    figure, axis = setup_fig(1, 2)
    colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

    for cfg in cfgs:
        clean_dir = cfg.qcfg.project.clean_dirs[Z3_4_11_2]
        paths = list_smt2_files(clean_dir)
        sizes = [] 
        for path in paths:
            sizes.append(os.path.getsize(path) / (8 * 1024 * 1024))
        n = len(sizes)
        label, color = cfg.qcfg.name, colors[label]
        axis[0].plot(np.sort(sizes), np.arange(n), marker=",", label=label, color=color)
        xs, ys = get_cdf_pts(sizes)
        axis[1].plot(xs, ys, marker=",", label=label, color=color)

    axis[0].legend()
    axis[0].set_ylabel("cumulative probability")
    axis[0].set_xlabel("query size (mb)")

    axis[1].legend()
    axis[1].set_xlabel("query size (mb)")

    plt.tight_layout()
    save_fig(figure, f"sizes", f"fig/sizes.pdf")

# def analyze_cond_fail(cfg):
#     con, cur = get_cursor(cfg.qcfg.db_path)
#     summary_table_name = cfg.get_summary_table_name()
#     print(cfg.get_project_name())

#     f = open("fig/cond_fail/" + summary_table_name + ".md", "w+")

#     for i, solver in enumerate(cfg.samples):
#         solver = str(solver)
#         # print(solver, cfg.get_project_name())
#         res = cur.execute(f"""SELECT * FROM {summary_table_name}
#             WHERE solver = ?""", (solver, ))
#         rows = res.fetchall()

#         unsolvable = {p: set() for p in cfg.qcfg.enabled_muts}
#         unsolvable["plain"] = set()

#         for row in rows:
#             if row[2] != "unsat":
#                 unsolvable["plain"].add(row[1])

#             summaries = ast.literal_eval(row[4])
#             for (perturb, vres, _) in summaries:
#                 if len(vres) != 0 and vres.count("unsat") ==0:
#                     unsolvable[perturb].add(row[1])

#         muts = ["plain", "shuffle", "rename", "sseed"]
#         table = [[solver] + [m + "(" + str(len(unsolvable[m])) + ")" for m in muts]]

#         for p1 in muts:
#             row = [p1 + "(" + str(len(unsolvable[p1])) + ")"]
#             for p2 in muts:
#                 us1 = unsolvable[p1]
#                 us2 = unsolvable[p2]
#                 inter = len(us1.intersection(us2))
#                 if p1 == p2:
#                     row.append("-")
#                 if len(us1) == 0:
#                     row.append(f"nan")
#                 else:
#                     row.append(f"{inter}({str(round(inter * 100 / len(us1), 2))})")
#             table.append(row)
#         f.write(as_md_table(table))
#     con.close()

# def print_as_md_table(cfgs, summary_rows):
#     solver_names = [str(s) for s in ALL_SOLVERS]
#     project_names = [cfg.get_project_name() for  cfg in cfgs]

#     row = [" "] + solver_names
#     print("|" + "|".join(row) + "|")
#     print("|:---------:" * (len(ALL_SOLVERS) + 1) + "|")
#     for i, project in enumerate(project_names):
#         row = [project]
#         for (lp, hp, p) in summary_rows[i]:
#             row.append(f"{str_percent(lp)}~{str_percent(hp)}, {str_percent(p)}")
#         print("|" + "|".join(row) + "|")

def analyze_d_komodo_sus(cfg):
    assert cfg.qcfg.name == "D_KOMODO"
    print("D_KOMODO total:")
    os.system("""ls data/d_komodo_z3_clean/ | wc -l""")
    print("D_KOMODO va__* total:")
    os.system("""ls data/d_komodo_z3_clean/ | grep "va__" | wc -l""")
    summaries = load_summary(cfg, 40)
    categories = get_categories(summaries)

    for other in [Z3_4_8_6, Z3_4_8_7, Z3_4_8_8, Z3_4_8_11, Z3_4_8_17, Z3_4_11_2]:
        usol, ausol = 0, 0
        for i in categories[other][0] - categories[Z3_4_8_5][0]:
            if "va__" in i:
                usol += 1
            ausol += 1

        usta, austa = 0, 0
        for i in categories[other][2] - categories[Z3_4_8_5][2]:
            if "va__" in i:
                usta += 1
            austa += 1

        print(other)
        print("va__* in additional unsolvable:", usol, "/", ausol)
        print("va__* in additional unstable:", usta, "/", austa)

def dump_all(cfgs, timeout_threshold, time_std_threshold, res_stable_threshold, unsolvable_threshold):
    projects = [cfg.qcfg.project for cfg in cfgs]
    project_names = [cfg.get_project_name() for cfg in cfgs]
    solver_names = [str(s) for s in ALL_SOLVERS]

    data = []
    for cfg in cfgs:
        summaries = load_summary(cfg, timeout_threshold)
        intervals = get_res_unstable_intervals(summaries, res_stable_threshold, unsolvable_threshold)
        ratios = get_time_unstable_ratios(summaries, time_std_threshold)
        row = []
        for solver_name in solver_names:
            if solver_name in intervals:
                lb, ub = intervals[solver_name]
                row.append([lb, ub, ratios[solver_name]])
            else:
                row.append([-1, -1, -1])
        data.append(row)
    # data = [[[0.38809831824062097, 1.5523932729624839, 1.9404915912031049], [0.258732212160414, 1.8111254851228977, 1.8111254851228977], [0.258732212160414, 1.6817593790426908, 0.9055627425614489], [0.0, 1.423027166882277, 0.7761966364812419], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [0.129366106080207, 1.2936610608020698, 3.3635187580853816], [0.0, 1.2936610608020698, 1.8111254851228977], [1.034928848641656, 1.2936610608020698, 0.0]], [[1.3631937682570594, 3.359298928919182, 1.2171372930866602], [1.4118792599805259, 3.2619279454722494, 1.1684518013631937], [1.2658227848101267, 2.8237585199610518, 0.7302823758519961], [1.1197663096397275, 2.6777020447906525, 0.9250243427458618], [2.3369036027263874, 7.254138266796494, 3.0185004868549172], [2.4342745861733204, 7.546251217137293, 3.1645569620253164], [2.4342745861733204, 7.643622200584226, 2.8237585199610518], [3.8461538461538463, 10.662122687439144, 2.775073028237585], [3.6514118792599803, 9.980525803310613, 3.7974683544303796], [3.6514118792599803, 10.17526777020448, 3.9922103213242455], [-1, -1, -1]], [[1.3214285714285714, 2.142857142857143, 0.35714285714285715], [1.3214285714285714, 2.1785714285714284, 0.375], [1.2142857142857142, 2.357142857142857, 0.5535714285714286], [1.0714285714285714, 1.8571428571428572, 0.30357142857142855], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [1.4821428571428572, 5.589285714285714, 1.0], [1.4464285714285714, 5.589285714285714, 1.0714285714285714], [-1, -1, -1]], [[0.8262910798122066, 2.0093896713615025, 0.5070422535211268], [0.8075117370892019, 1.9530516431924883, 0.39436619718309857], [0.4131455399061033, 1.4460093896713615, 0.4131455399061033], [0.4507042253521127, 1.5211267605633803, 0.39436619718309857], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [0.8450704225352113, 4.769953051643192, 0.6572769953051644], [0.7887323943661971, 4.525821596244131, 0.7136150234741784], [-1, -1, -1]], [[1.5954415954415955, 1.7663817663817665, 0.0], [1.5954415954415955, 1.8233618233618234, 0.0], [1.3105413105413106, 1.4814814814814814, 0.05698005698005698], [1.2535612535612535, 1.3105413105413106, 0.05698005698005698], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [1.1965811965811965, 1.6524216524216524, 0.05698005698005698], [1.2535612535612535, 1.5384615384615385, 0.17094017094017094], [11.396011396011396, 12.706552706552706, 0.0]], [[2.9947916666666665, 4.1015625, 0.5859375], [3.3854166666666665, 4.036458333333333, 0.5208333333333334], [3.125, 4.036458333333333, 0.390625], [2.4088541666666665, 3.3203125, 0.390625], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [-1, -1, -1], [2.7994791666666665, 3.90625, 0.9114583333333334], [2.734375, 4.036458333333333, 1.0416666666666667], [-1, -1, -1]]]

    colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

    # # # print_as_md_table(data)
    total = len(solver_names) * len(projects)
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

def dump_unsolvable(cfgs, timeout_threshold):
    for cfg in cfgs:
        summaries = load_summary(cfg, timeout_threshold)
        categories = get_categories(summaries)
        for solver, (unsolvables, _, _, _) in categories.items():
            lname = f"data/sample_lists/{cfg.qcfg.name}_UNSOL_{solver}"
            f = open(lname, "w+")
            for item in unsolvables:
                f.write(item + "\n")
            f.close()
