from db_utils import *
import numpy as np
from tqdm import tqdm
import ast
import scipy.stats
from enum import Enum

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

class RCode(Enum):
    SAT = 1
    UNSAT = 2
    TIMEOUT = 3
    UNKNOWN = 4
    ERROR = 5

    def from_str(s):
        if s == "sat":
            return RCode.SAT
        elif s == "unsat":
            return RCode.UNSAT
        elif s == "timeout":
            return RCode.TIMEOUT
        elif s == "unknown":
            return RCode.UNKNOWN
        elif s == "error":
            return RCode.ERROR
        else:
            assert False

    def __str__(self):
        if self == RCode.SAT:
            return "sat"
        elif self == RCode.UNSAT:
            return "unsat"
        elif self == RCode.TIMEOUT:
            return "timeout"
        elif self == RCode.UNKNOWN:
            return "unknown"
        elif self == RCode.ERROR:
            return "error"
        else:
            assert False

def append_summary_table(cfg, solver):
    con, cur = get_cursor(cfg.qcfg.db_path)
    solver_table = cfg.qcfg.get_solver_table_name(solver)
    summary_table = cfg.get_summary_table_name()

    if not check_table_exists(cur, solver_table):
        con.close()
        return

    res = cur.execute(f"""
        SELECT DISTINCT(query_path), result_code, elapsed_milli
        FROM {solver_table}
        WHERE query_path = vanilla_path""")

    vanilla_rows = res.fetchall()
    for (vanilla_path, v_rcode, v_time) in tqdm(vanilla_rows):
        res = cur.execute(f"""
            SELECT result_code, elapsed_milli, perturbation FROM {solver_table}
            WHERE vanilla_path = "{vanilla_path}"
            AND perturbation IS NOT NULL""")
        
        perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
        v_rcode = RCode.from_str(v_rcode).value
        results = {p: [[v_rcode], [v_time]] for p in perturbs}

        for row in res.fetchall():
            results[row[2]][0].append(RCode.from_str(row[0]).value)
            results[row[2]][1].append(row[1])

        mut_size = cfg.qcfg.max_mutants
        blob = np.zeros((len(perturbs), 2, mut_size + 1), dtype=int)
        for pi, perturb in enumerate(perturbs):
            (veri_res, veri_times) = results[perturb]
            blob[pi][0] = veri_res
            blob[pi][1] = veri_times

        cur.execute(f"""INSERT INTO {summary_table}
            VALUES(?, ?, ?, ?);""", 
            (str(solver), vanilla_path, str(perturbs), blob))
    con.commit()
    con.close()

def build_summary_table(cfg):
    con, cur = get_cursor(cfg.qcfg.db_path)
    summary_table = cfg.get_summary_table_name()

    cur.execute(f"""DROP TABLE IF EXISTS {summary_table}""")

    cur.execute(f"""CREATE TABLE {summary_table} (
        solver varchar(10),
        vanilla_path TEXT,
        pretubrations TEXT,
        summaries BLOB)""")

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
        mut_size = cfg.qcfg.max_mutants
        for row in rows:
            perturbs = ast.literal_eval(row[2])
            blob = np.frombuffer(row[3], dtype=int)
            blob = blob.reshape((len(perturbs), 2, mut_size + 1))
            nrow = [row[0], row[1], perturbs, blob]
            nrows.append(nrow)
        summaries[solver] = nrows
        # print(f"[INFO] loaded {summary_table_name} {solver}")
    con.close()
    return summaries

class Stablity(str, Enum):
    UNSOLVABLE = "unsolvable"
    RES_UNSTABLE = "res_unstable"
    TIME_UNSTABLE = "time_unstable"
    STABLE = "stable"

    def __str__(self) -> str:
        return super().__str__()

    def empty_map():
        em = {c: set() for c in Stablity}
        return em

# miliseconds
def successes_within_timeout(blob, timeout=1e6):
    success = blob[0] == RCode.UNSAT.value
    none_timeout = blob[1] < timeout 
    success = np.sum(np.logical_and(success, none_timeout))
    return success

class Thresholds:
    def __init__(self, method):
        self.confidence = 0.05
        self.timeout = 1e6

        self.unsolvable = 5
        assert 0 < self.unsolvable < 100

        self.res_stable = 95
        assert 0 < self.res_stable < 100

        self.time_std = 1e6

        if method == "regression":
            self.categorize_group = self._categorize_group_regression
        elif method == "strict":
            self.categorize_group = self._categorize_group_divergence_strict
        # elif method == "threshold":
        #     self.categorize_group = self._categorize_group_threshold
        else:
            assert False

    def _categorize_group_regression(self, group_blob):
        pres = group_blob[0][0]
        ptime = group_blob[1][0]
        if pres != RCode.UNSAT.value or ptime > self.timeout:
            return Stablity.UNSOLVABLE

        timeout = max(ptime * 1.5, ptime + 50000)
        success = successes_within_timeout(group_blob, timeout)
        # if success < len(group_blob[0]) * 0.8:
        #     return Stablity.RES_UNSTABLE

        size = len(group_blob[0])
        if success != size:
            return Stablity.RES_UNSTABLE
        return Stablity.STABLE

    def _categorize_group_divergence_strict(self, group_blob):
        size = len(group_blob[0])
        success = successes_within_timeout(group_blob, self.timeout)

        if success == 0:
            return Stablity.UNSOLVABLE

        if success == size:
            return Stablity.STABLE
        
        return Stablity.RES_UNSTABLE

    # def _categorize_group_threshold(self, group_blob):
    #     success = vress.count("unsat")
    #     size = len(vress)
    #     # for i, x in enumerate(times):
    #     #     if as_seconds(x) <= self.timeout and vress[i] == "unsat":
    #     #         success += 1

    #     value = self.unsolvable/100
    #     _, p_value = proportions_ztest(count=success,
    #                                     nobs=size,
    #                                     value=value, 
    #                                     alternative='smaller',
    #                                     prop_var=value)
    #     if p_value <= self.confidence:
    #         return Stablity.UNSOLVABLE

    #     value = self.res_stable / 100
    #     _, p_value = proportions_ztest(count=success, 
    #                                     nobs=size,
    #                                     value=value,
    #                                     alternative='larger',
    #                                     prop_var=value)

    #     if p_value <= self.confidence:
    #         std = np.std(times)
    #         time_std = self.time_std * 1000
    #         T = (size - 1) * ((std / time_std) ** 2)
    #         if T > scipy.stats.chi2.ppf(1-self.confidence, df=size-1):
    #             return Stablity.TIME_UNSTABLE
    #         else:
    #             return Stablity.STABLE

    #     return Stablity.RES_UNSTABLE
    
    def categorize_query(self, group_blobs, perturbs=None):
        ress = set()
        if perturbs is None:
            perturbs = [i for i in range(group_blobs.shape[0])]
        for i in perturbs:
            ress.add(self.categorize_group(group_blobs[i]))
        if len(ress) == 1:
            return ress.pop()
        if ress == {Stablity.TIME_UNSTABLE, Stablity.STABLE}:
            return Stablity.TIME_UNSTABLE
        return Stablity.RES_UNSTABLE

def categorize_qeuries(rows, thresholds, perturbs=None):
    categories = Stablity.empty_map()
    for query_row in rows:
        plain_path = query_row[1]
        res = thresholds.categorize_query(query_row[3], perturbs)
        categories[res].add(plain_path)
    return categories

def get_category_precentages(categories):
    percentages = dict()
    total = sum([len(i) for i in categories.values()])
    for c, i in categories.items():
        percentages[c] = percentage(len(i), total)
    return percentages, total

# def subplot_cutoff(sp, xs, ys0, ys1, ys2, solver):
#     sp.plot(xs, ys0, marker=",", label="unsolvables")
#     sp.plot(xs, ys1, marker=",", label="res_unstables")
#     sp.plot(xs, ys2, marker=",", label=" res_unstables")
#     sp.set_title(f'{solver} timelimit cutoff vs category precentage')
#     sp.set_xlabel("timelimit selection (seconds)")
#     sp.set_ylabel("precentage of query")
#     sp.set_xlim(left=5, right=60)
#     sp.set_ylim(bottom=0, top=15)
#     sp.legend()

def plot_cutoff(cfg):
    s = load_summary_table(cfg)
    solver_count = len(s.keys())
    cut_figure, cut_aixs = setup_fig(solver_count, 2)
    xs = [i for i in range(5, 61, 1)]
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]

    for j, (solver, rows) in enumerate(s.items()):
        sps = cut_aixs
        if solver_count != 1:
            sps = cut_aixs[j]

        strict_th = Thresholds("strict")
        palin_th = Thresholds("regression")

        stricts = {"unsolvable": [], "union": [], "shuffle": [], 
                    "rename": [], "rseed": [], "intersect": []}
        plains = {"unsolvable": [], "res_unstable": []}

        for i in xs:
            strict_th.timeout = i * 1000
            palin_th.timeout = i * 1000

            categories = {"unsolvable": set(), "shuffle": set(), "rename":set(), "rseed": set(), "union": set()}
            categories2 = {"unsolvable": 0, "res_unstable": 0, "stable": 0}
            for query_row in rows:
                plain_path = query_row[1]
                group_blobs = query_row[3]
                ress = set()
                for k, p in enumerate(perturbs):
                    res = strict_th.categorize_group(group_blobs[k])
                    if res == Stablity.RES_UNSTABLE:
                        categories[p].add(plain_path)
                    ress.add(res)
                if ress == {Stablity.UNSOLVABLE}:
                    categories["unsolvable"].add(plain_path)
                elif ress != {Stablity.STABLE}:
                    categories["union"].add(plain_path)

                res = palin_th.categorize_query(group_blobs)
                categories2[res] += 1

            total = len(rows)
            intersect = set.intersection(*[categories["shuffle"], categories["rename"], categories["rseed"]])
            categories["intersect"] = intersect
            for k, v in categories.items():
                stricts[k].append(percentage(len(v) , total))
            for k in {"unsolvable", "res_unstable"}:
                plains[k].append(percentage(categories2[k], total))

        for k in stricts:
            sps[0].plot(xs, stricts[k], marker=".", label=k)
        sps[0].legend()
        for k in plains:
            sps[1].plot(xs, plains[k], marker=".", label=k)
        sps[1].legend()

    name = cfg.qcfg.name
    save_fig(cut_figure, f"{name}", f"fig/time_cutoff/{name}.png")

def categorty_prediction(cfg):
    summaries = load_summary_table(cfg)
    sample_size = 30
    for solver in summaries:
        true_unsol, est_unsol = 0, 0
        true_stable, est_stable = 0, 0
        for query_row in summaries[solver]:
            group_blobs = query_row[3]
            for i in range(group_blobs.shape[0]):
                sample = group_blobs[i][:,:sample_size]
                sample_success = successes_within_timeout(sample)
                true_success = successes_within_timeout(group_blobs[i])
                if sample_success == 0:
                    est_unsol += 1
                    if true_success == 0:
                        true_unsol += 1
                if sample_success == sample_size:
                    est_stable += 1
                    if true_success == group_blobs.shape[2]:
                        true_stable += 1
        print(solver, 
              round(percentage(true_unsol, est_unsol), 2),
              round(percentage(true_stable, est_stable), 2))

def compare_perturbations(cfg, solver=None):
    summaries = load_summary_table(cfg)
    th = Thresholds("strict")

    # votes = {c: 0 for c in Stablity}
    if solver is not None:
        summaries = {solver: summaries[solver]}

    solver_count = len(summaries.keys())
    figure, aixs = setup_fig(solver_count, 2)

    for j, solver in enumerate(summaries):
        decisions = dict()
        perturbations = summaries[solver][0][2]
        categories = [c for c in Stablity]
        for p in perturbations:
           decisions[p] = {c: set() for c in Stablity}
        for query_row in summaries[solver]:
            group_blobs = query_row[3]
            for i in range(group_blobs.shape[0]):
                p = perturbations[i]
                c = th.categorize_group(group_blobs[i])
                decisions[p][c].add(query_row[1])
        sps = aixs
        if solver_count != 1:
            sps = aixs[j]
        data = []
        for (_, decision) in decisions.items():
            pts = []
            for c in categories:
                pts.append(len(decision[c]))
            data.append(pts)
        data = np.array(data)

        new_row = np.zeros(data.shape[1])
        for i, c in enumerate(categories):
            things = [decisions[p][c] for p in perturbations]
            common = set.intersection(*things)
            new_row[i] = len(common)
        data = np.vstack((data, new_row))
        perturbations += ["common"]

        norm_data = np.zeros(data.T.shape)
        for i, col in enumerate(data.T):
            new_col = np.zeros(col.shape)
            if np.max(col) != 0:
                new_col = np.array(col) / np.max(col)
            norm_data[i] = new_col
        norm_data = norm_data.T

        bar_width = len(categories)/50
        br = np.arange(len(categories))
        br = [x - bar_width for x in br]

        for i in range(data.shape[0]):
            if i == len(data) - 1:
                continue
            br = [x + bar_width for x in br]
            sps[0].bar(br, height=data[i]-data[-1], bottom=data[-1], width=bar_width, color=COLORS[i], label=str(perturbations[i]))
            sps[0].bar(br, height=data[-1], width=bar_width, color=COLORS[i], alpha=0.5)
            sps[1].bar(br, height=norm_data[i]-norm_data[-1], bottom=norm_data[-1], width=bar_width, color=COLORS[i], label=str(perturbations[i]))
            sps[1].bar(br, height=norm_data[-1], width=bar_width, color=COLORS[i], alpha=0.5)

        sps[0].set_xticks([r + bar_width for r in range(len(categories))])
        sps[0].set_xticklabels([str(c) for c in categories])
        sps[0].set_xlabel('categorties', fontsize = 12)
        sps[0].legend()

        sps[1].set_xticks([r + bar_width for r in range(len(categories))])
        sps[1].set_xticklabels([str(c) for c in categories])
        sps[1].set_xlabel('categorties', fontsize = 12)
        sps[1].legend()

    name = cfg.qcfg.name
    plt.savefig(f"fig/pert_diff/{name}.png")

# def do_stuff():
#     pass

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

# # def plot_query_sizes(cfgs):
# #     import os
# #     figure, axis = setup_fig(1, 2)
# #     colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

# #     for cfg in cfgs:
# #         clean_dir = cfg.qcfg.project.clean_dirs[Z3_4_11_2]
# #         paths = list_smt2_files(clean_dir)
# #         sizes = [] 
# #         for path in paths:
# #             sizes.append(os.path.getsize(path) / (8 * 1024 * 1024))
# #         n = len(sizes)
# #         label, color = cfg.qcfg.name, colors[label]
# #         axis[0].plot(np.sort(sizes), np.arange(n), marker=",", label=label, color=color)
# #         xs, ys = get_cdf_pts(sizes)
# #         axis[1].plot(xs, ys, marker=",", label=label, color=color)

# #     axis[0].legend()
# #     axis[0].set_ylabel("cumulative probability")
# #     axis[0].set_xlabel("query size (mb)")

# #     axis[1].legend()
# #     axis[1].set_xlabel("query size (mb)")

# #     plt.tight_layout()
# #     save_fig(figure, f"sizes", f"fig/sizes.pdf")

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
#         unsolvable["regression"] = set()

#         for row in rows:
#             if row[2] != "unsat":
#                 unsolvable["regression"].add(row[1])

#             summaries = ast.literal_eval(row[4])
#             for (perturb, vres, _) in summaries:
#                 if len(vres) != 0 and vres.count("unsat") ==0:
#                     unsolvable[perturb].add(row[1])

#         muts = ["regression", "shuffle", "rename", "sseed"]
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

# # # def print_as_md_table(cfgs, summary_rows):
# # #     solver_names = [str(s) for s in ALL_SOLVERS]
# # #     project_names = [cfg.get_project_name() for  cfg in cfgs]

# # #     row = [" "] + solver_names
# # #     print("|" + "|".join(row) + "|")
# # #     print("|:---------:" * (len(ALL_SOLVERS) + 1) + "|")
# # #     for i, project in enumerate(project_names):
# # #         row = [project]
# # #         for (lp, hp, p) in summary_rows[i]:
# # #             row.append(f"{str_percent(lp)}~{str_percent(hp)}, {str_percent(p)}")
# # #         print("|" + "|".join(row) + "|")

# # def analyze_d_komodo_sus(cfg):
# #     assert cfg.qcfg.name == "D_KOMODO"
# #     print("D_KOMODO total:")
# #     os.system("""ls data/d_komodo_z3_clean/ | wc -l""")
# #     print("D_KOMODO va__* total:")
# #     os.system("""ls data/d_komodo_z3_clean/ | grep "va__" | wc -l""")
# #     summaries = load_summary_table(cfg)

# #     thres = Thresholds("regression")
# #     # thres.timeout = 60
# #     unsolvables0 = categorize_qeuries(summaries['z3_4_8_5'], thres)[0]
# #     unsolvables8 = categorize_qeuries(summaries['z3_4_8_8'], thres)[0]

# #     for i in unsolvables8 - unsolvables0:
# #         print(i)

def dump_all(cfgs):
    projects = [cfg.qcfg.project for cfg in cfgs]
    project_names = [cfg.get_project_name() for cfg in cfgs]
    solver_names = [str(s) for s in Z3_SOLVERS_ALL]

    thres = Thresholds("strict")
    thres.timeout = 3e4 # 30s

    data = []
    for cfg in cfgs:
        summaries = load_summary_table(cfg)
        row = []
        for solver in tqdm(solver_names):
            if solver in summaries:
                rows = summaries[solver]
                items = categorize_qeuries(rows, thres)
                ps = get_category_precentages(items)
                row.append([ps[Stablity.UNSOLVABLE], ps[Stablity.RES_UNSTABLE], ps[Stablity.TIME_UNSTABLE]])
            else:
                row.append([0, 0, 0])
        data.append(row)
    print(data)

    bar_width = len(solver_names)/100
    fig, ax = plt.subplots()

    br = np.arange(len(solver_names))
    br = [x - bar_width for x in br]

    for pi, project_row in enumerate(data):
        lps, hps, pds = [], [], []
        br = [x + bar_width for x in br]
        pcolor = COLORS[pi]
        for i, (lp, hp, p) in enumerate(project_row):
            if lp == hp and lp != 0:
                plt.scatter(br[i], lp, marker='_', color=pcolor, s=bar_width)
            lps.append(lp)
            hps.append(hp)
            if projects[pi].orig_solver == solver_names[i]:
                plt.bar(br[i], hp, bottom=lp, width = bar_width, color=pcolor, edgecolor='black')
            pds.append(p)

        plt.bar(br, height=lps, width=bar_width, color=pcolor, alpha=0.20)
        plt.bar(br, height=hps, bottom=lps, width=bar_width, label=project_names[pi], color=pcolor)
        hps = [hps[i] + lps[i] for i in range(len(hps))]
        plt.bar(br, height=pds, bottom=hps, width=bar_width, color=pcolor, alpha=0.40)

    plt.ylim(bottom=0, top=15)
    plt.xlabel('solvers', fontsize = 12)
    plt.ylabel('unstable ratios', fontsize = 12)
    solver_lables = [f"{str(s).replace('_', '.')}\n{s.data[:-3]}" for s in Z3_SOLVERS_ALL]
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
