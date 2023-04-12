from db_utils import *
import numpy as np
from tqdm import tqdm
import ast
import scipy.stats
from enum import Enum
from vbkv_filemap import *

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
    "#F6768E", # Strong Purplish Pink
]

class ColorMapper:
    def __init__(self):
        self.i = 0
    
    def peek(self):
        return COLORS[self.i]
    
    def pop(self):
        self.i += 1
        return COLORS[self.i-1]

def get_color_map(keys):
    assert len(keys) <= len(COLORS)
    return {k: COLORS[i] for i, k in enumerate(keys)}

PROJECT_COLORS = get_color_map([c.get_project_name() for c in ALL_CFGS])
PERTURBATION_COLORS = get_color_map(["unsolvable", "union", "intersect"] + [c for c in Mutation])
PERTURBATION_COLORS["res_unstable"] = PERTURBATION_COLORS["union"]

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

def build_solver_summary_table(cfg, solver):
    con, cur = get_cursor(cfg.qcfg.db_path)
    solver_table = cfg.qcfg.get_solver_table_name(solver)
    summary_table = cfg.get_solver_summary_table_name(solver)

    if not check_table_exists(cur, solver_table):
        print(f"[WARN] table {solver_table} does not exist")
        con.close()
        return

    cur.execute(f"""DROP TABLE IF EXISTS {summary_table}""")

    cur.execute(f"""CREATE TABLE {summary_table} (
        vanilla_path TEXT,
        pretubrations TEXT,
        summaries BLOB)""")

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
            VALUES(?, ?, ?);""", 
            (vanilla_path, str(perturbs), blob))

    con.commit()
    con.close()

def extend_solver_summary_table(cfg, ext_cfg, solver):
    con, cur = get_cursor(cfg.qcfg.db_path)
    solver_table = cfg.qcfg.get_solver_table_name(solver)
    solver_ext_table = ext_cfg.qcfg.get_solver_table_name(solver)
    # summary_table = cfg.get_solver_summary_table_name(solver)

    if not check_table_exists(cur, solver_table):
        con.close()
        return
    
    solver_table = cfg.qcfg.get_solver_table_name(solver)

    res = cur.execute(f"""
        SELECT query_path, result_code, elapsed_milli, command FROM {solver_ext_table} """)

    ext_results = dict()
    rows = res.fetchall()

    for (query_path, rcode, time, command) in tqdm(rows):
        stem = query_path.split("/")[-1]
        ext_results[stem] = (rcode, time, command)
        # print(stem, time, rcode)

    res = cur.execute(f"""
        SELECT query_path, rowid FROM {solver_table}
        WHERE result_code = "timeout" """)

    rows = res.fetchall()

    for (query_path, row_id) in tqdm(rows):
        stem = query_path.split("/")[-1]
        (rcode, time, command) = ext_results[stem]
        cur.execute(f"""UPDATE {solver_table}
            SET result_code = "{rcode}",
            elapsed_milli = {time},
            command = "{command}"
            WHERE rowid = {row_id}""")

    con.commit()
    con.close()

    build_solver_summary_table(cfg, solver)

def as_seconds(milliseconds):
    return milliseconds / 1000

def group_time_mean(times):
    assert len(times) != 0
    return as_seconds(np.mean(times))

def group_time_std(times):
    assert len(times) != 0
    return as_seconds(np.std(times))

def load_solver_summary(cfg, solver, skip=set()):
    con, cur = get_cursor(cfg.qcfg.db_path)
    new_table_name = cfg.qcfg.get_solver_table_name(solver) + "_summary"
    if not check_table_exists(cur, new_table_name):
        print(f"[INFO] skipping {new_table_name}")
        return None
    solver = str(solver)

    res = cur.execute(f"""SELECT * FROM {new_table_name}""")
    rows = res.fetchall()

    nrows = []
    mut_size = cfg.qcfg.max_mutants
    for row in rows:
        if row[0] in skip:
            continue
        perturbs = ast.literal_eval(row[1])
        blob = np.frombuffer(row[2], dtype=int)
        blob = blob.reshape((len(perturbs), 2, mut_size + 1))
        nrow = [row[0], perturbs, blob]
        nrows.append(nrow)
    con.close()
    return nrows

def get_unknowns(cfg):
    th = Classifier("strict")
    th.timeout = 61e4

    summary = load_solver_summary(cfg, cfg.qcfg.project.orig_solver)
    if summary is None:
        return set()
    categories = categorize_queries(summary, th)
    return categories[Stablity.UNKNOWN]

def load_solver_summaries(cfg, skip_unknowns=True):
    summaries = dict()

    if skip_unknowns:
        unkowns = get_unknowns(cfg)
    else:
        unkowns = set()

    for solver in cfg.samples:
        nrows = load_solver_summary(cfg, solver, unkowns)
        if nrows is None:
            continue
        summaries[solver] = nrows
    return summaries

class Stablity(str, Enum):
    UNKNOWN = "unknown"
    UNSOLVABLE = "unsolvable"
    UNSTABLE = "unstable"
    # TIME_UNSTABLE = "time_unstable"
    STABLE = "stable"

    def __str__(self) -> str:
        return super().__str__()

    def empty_map():
        em = {c: set() for c in Stablity}
        return em

# # miliseconds
# def indices_within_timeout(blob, timeout):
#     none_timeout = blob[1] < timeout 
#     return np.where(none_timeout)[0]

def count_within_timeout(blob, rcode, timeout=1e6):
    success = blob[0] == rcode.value
    none_timeout = blob[1] < timeout
    success = np.sum(np.logical_and(success, none_timeout))
    return success

    # if self.time_std is not None:
    #     std = np.std(times)
    #     T = (size - 1) * ((std / self.time_std) ** 2)
    #     if T > scipy.stats.chi2.ppf(1-self.confidence, df=size-1):
    #         return Stablity.TIME_UNSTABLE

class Classifier:
    def __init__(self, method):
        self.confidence = 0.05
        self.timeout = 1e6

        self.unsolvable = 5
        self.res_stable = 95
        self.discount = 0.8

        if method == "regression":
            assert False
            # self.categorize_group = self._categorize_group_regression
        elif method == "strict":
            self.categorize_group = self._categorize_strict
        elif method == "t_test":
            self.categorize_group = self._categorize_t_test
        else:
            assert False

    # def _categorize_group_regression(self, group_blob):
    #     pres = group_blob[0][0]
    #     ptime = group_blob[1][0]
    #     if pres != RCode.UNSAT.value or ptime > self.timeout:
    #         return Stablity.UNSOLVABLE

    #     timeout = max(ptime * 1.5, ptime + 50000)
    #     success = count_within_timeout(group_blob, RCode.UNSAT, timeout)

    #     if success < len(group_blob[0]) * 0.8:
    #         return Stablity.RES_UNSTABLE

    #     size = len(group_blob[0])
    #     if success != size:
    #         return Stablity.RES_UNSTABLE
    #     return Stablity.STABLE

    def _categorize_strict(self, group_blob):
        size = len(group_blob[0])
        success = count_within_timeout(group_blob, RCode.UNSAT, self.timeout)

        if success == 0:
            if count_within_timeout(group_blob, RCode.UNKNOWN, self.timeout) == size:
                return Stablity.UNKNOWN
            return Stablity.UNSOLVABLE

        if success == size:
            return Stablity.STABLE

        # if m > self.timeout * self.discount:
        #     return Stablity.STABLE
        return Stablity.UNSTABLE

    def _categorize_t_test(self, group_blob):
        size =  group_blob.shape[1]

        unsat_indices = group_blob[0] == RCode.UNSAT.value
        nto_indices = group_blob[1] < self.timeout
        valid_indices = np.logical_and(unsat_indices, nto_indices)
        success = np.sum(valid_indices)

        # success = count_within_timeout(group_blob, RCode.UNSAT, self.timeout)
        # if success == 0:
        #     if count_within_timeout(group_blob, RCode.UNKNOWN, self.timeout) == size:
        #         return Stablity.UNKNOWN

        value = self.unsolvable/100
        _, p_value = proportions_ztest(count=success,
                                        nobs=size,
                                        value=value, 
                                        alternative='smaller',
                                        prop_var=value)
        if p_value <= self.confidence:
            return Stablity.UNSOLVABLE

        value = self.res_stable/100
        _, p_value = proportions_ztest(count=success, 
                                        nobs=size,
                                        value=value,
                                        alternative='smaller',
                                        prop_var=value)

        if p_value <= self.confidence and \
            np.mean(group_blob[1][valid_indices]) < self.timeout * self.discount:
            return Stablity.UNSTABLE

        return Stablity.STABLE
    
    def categorize_query(self, group_blobs, perturbs=None):
        ress = set()
        if perturbs is None:
            perturbs = [i for i in range(group_blobs.shape[0])]
        for i in perturbs:
            ress.add(self.categorize_group(group_blobs[i]))
        if len(ress) == 1:
            return ress.pop()
        if Stablity.UNSTABLE not in ress:
            print(ress)
        return Stablity.UNSTABLE

def categorize_queries(rows, classifier, perturbs=None):
    categories = Stablity.empty_map()
    for query_row in rows:
        plain_path = query_row[0]
        res = classifier.categorize_query(query_row[2], perturbs)
        categories[res].add(plain_path)
    return categories

def get_category_percentages(categories):
    percentages = dict()
    total = sum([len(i) for i in categories.values()])
    for c, i in categories.items():
        percentages[c] = percentage(len(i), total)
    return percentages, total

def get_cutoff_categories(categories, i, classifier, rows, perturbs):
    classifier.timeout = i * 1e3
    cur = {p: set() for p in perturbs + ["unsolvable", "union", "intersect"]}
    for query_row in rows:
        plain_path = query_row[0]
        group_blobs = query_row[2]
        ress = set()
        for k, p in enumerate(perturbs):
            res = classifier.categorize_group(group_blobs[k])
            if res == Stablity.UNSTABLE:
                cur[p].add(plain_path)
                cur["union"].add(plain_path)
            ress.add(res)
        if ress == {Stablity.UNSOLVABLE}:
            cur["unsolvable"].add(plain_path)
        elif ress == {Stablity.UNSTABLE}:
            # if all of the perturbations is unstable
            cur["intersect"].add(plain_path)
        elif ress != {Stablity.STABLE}:
            # if any of the perturbations is unstable
            # or the results are mixed
            cur["union"].add(plain_path)

    categories[i] = cur

def get_all_cutoff_categories(classifier, rows, cutoffs, perturbs):
    import multiprocessing as mp
    manager = mp.Manager()
    categories = manager.dict()

    processes = []
    for i in cutoffs:
        p = mp.Process(target=get_cutoff_categories, args=(categories, i, classifier, rows, perturbs))
        p.start()
        processes.append(p)

    for p in processes:
        p.join()

    return categories

def plot_ext_cutoff(cfg):
    classifier = Classifier("t_test")
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    name = cfg.qcfg.name

    skip = get_unknowns(cfg)
    # figure, axis = plt.subplots(2, 1)

    rows = load_solver_summary(cfg, Z3_4_12_1, skip)
    cutoffs = [i for i in range(10, 151, 1)]

    categories = get_all_cutoff_categories(classifier, rows, cutoffs, perturbs)
    total = len(rows)

    sp = plt
    cm = ColorMapper()

    sp.plot(cutoffs, [percentage(len(categories[i]["union"]), total) for i in cutoffs], label="unstable", color=cm.pop())
    sp.plot(cutoffs, [percentage(len(categories[i]["unsolvable"]), total) for i in cutoffs], label="unsolvable", color=cm.pop())

    for step in [5, 30, 60]:
        changes = []
        for i in cutoffs:
            if i + step > cutoffs[-1]:
                continue
            curr = categories[i]
            next = categories[i+step]
            changes.append(percentage(len(curr["union"].intersection(next["union"])), total))
        print(changes[-1])
        sp.vlines(cutoffs[-1]-step, ymin=0, ymax=changes[-1], color=cm.peek(), linestyle='--')
        sp.plot(cutoffs[:len(changes)], changes, label=f"{step}s forward", color=cm.pop())
    # sp.legend(loc='upper center', ncol=3, fancybox=True, shadow=True,bbox_to_anchor=(0.5, 1.15))
    sp.legend()
    sp.xlim(left=min(cutoffs), right=max(cutoffs))
    sp.xlabel("timelimit choice (seconds)")
    sp.xticks([10, 30, 60, 90, 120, 150])
    
    sp.ylim(bottom=0)
    sp.ylabel("percentages of queries")

    plt.tight_layout()
    plt.savefig(f"fig/time_cutoff/{name}_ext.png")

# def cutoff_edge(cfg):
#     summaries = load_solver_summaries(cfg)
#     for solver in summaries:
#         for query_row in summaries[solver]:
#             group_blobs = query_row[2]
#             scs = []
#             for i in range(group_blobs.shape[0]):
#                 group_blob = group_blobs[i]
#                 sc = count_within_timeout(group_blob, RCode.UNSAT, timeout=61e3)
#                 if sc != 61:
#                     scs.append(sc)
#                     scs.append(round(np.mean([t for i, t in enumerate(group_blob[1]) if t < 61e3 and group_blob[0][i] == RCode.UNSAT.value])/1000, 3))
#             if scs != []:
#                 print(scs)
#         break

def plot_pert_diff(cfg):
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    name = cfg.qcfg.name

    skip = get_unknowns(cfg)
    figure, axis = plt.subplots(1, 2)
  
    cutoffs = [i for i in range(10, 61, 1)]

    classifier = Classifier("t_test")

    for si, solver in enumerate([cfg.qcfg.project.orig_solver, Z3_4_12_1]):
        rows = load_solver_summary(cfg, solver, skip)
        total = len(rows)
        sp = axis[si]

        categories = get_all_cutoff_categories(classifier, rows, cutoffs, perturbs)
        keys = ["union"] + perturbs + ["unsolvable","intersect"]
        points = {p:[] for p in keys}

        for j in cutoffs:
            for k, v in categories[j].items():
                points[k].append(percentage(len(v), total))

        for k in points:
            if k == "unsolvable":
                continue
            sp.plot(cutoffs, points[k], label=k, color=PERTURBATION_COLORS[k])
        sp.set_ylim(bottom=0, top=6)
        sp.set_xlabel("timelimit choice (seconds)")
        sp.set_xlim(left=min(cutoffs), right=60)
        # sp.set_xticks([15, 30, 45, 60])
        sp.set_title(str(solver))

    # axis[i].set_xticks([min(cutoffs)] + np.arange(30, 6, 30).tolist() + [max(cutoffs)])
    axis[0].set_ylabel("percetable of queries")
    axis[0].legend()

    plt.savefig(f"fig/pert_diff/{name}.png")

def plot_sr_cdf(cfg):
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    name = cfg.qcfg.name

    skip = get_unknowns(cfg)
    pa = 1

    for solver in Z3_SOLVERS_ALL:
        rows = load_solver_summary(cfg, solver, skip)
        dps = np.zeros((len(rows), 3))
        for query_row in rows:
            # plain_path = query_row[0]
            group_blobs = query_row[2]
            # ress = set()
            msr1, msr2 = 61, 61
            plain_res = group_blobs[0][0][0]
            plain_time = group_blobs[0][1][0]

            for k, p in enumerate(perturbs):
                sr1 = count_within_timeout(group_blobs[k], RCode.UNSAT, timeout=61e3)
                msr1 = min(msr1, sr1)
                sr2 = 0
                if plain_res == RCode.UNSAT.value:
                    sr2 = count_within_timeout(group_blobs[k], RCode.UNSAT, timeout=61e3)

            msr2 = min(msr2, sr2)
            dps[rows.index(query_row), 0] = percentage(msr1, 61)
            dps[rows.index(query_row), 1] = percentage(msr2, 61)
        xs, ys = get_cdf_pts(dps[:,0])
        plt.scatter(xs, ys, label=str(solver), marker=".")
        # xs, ys = get_cdf_pts(dps[:,1])
        # plt.scatter(xs, ys, label=str(solver) + "_reg", marker=".")  
        # for i in range(dps.shape[1]):
        #     xs, ys = get_cdf_pts(dps[:,i])
        #     plt.scatter(xs, ys, label=str(perturbs[i]), color=PERTURBATION_COLORS[str(perturbs[i])], marker=".")
    plt.ylim(bottom=0, top=12)
    plt.xlim(left=0, right=100)
    plt.xlabel("min success rate among perturbation groups")
    plt.ylabel("cumulative percentage of queries")
    plt.legend()
    plt.savefig(f"fig/sr_cdf/{name}.png")

def plot_time_std(cfg):
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    name = cfg.qcfg.name

    skip = get_unknowns(cfg)
    figure, axis = plt.subplots(1, 2)
  
    i = 0

    for solver in [Z3_4_12_1]:
        rows = load_solver_summary(cfg, solver, skip)
        dps = [[], [], []]
        for query_row in rows:
            group_blobs = query_row[2]

            # for k, p in enumerate(perturbs):
            sr0 = count_within_timeout(group_blobs[0], RCode.UNSAT, timeout=61e3)
            sr1 = count_within_timeout(group_blobs[1], RCode.UNSAT, timeout=61e3)
            sr2 = count_within_timeout(group_blobs[2], RCode.UNSAT, timeout=61e3)

            if sr0 == 61:
                dps[0].append(np.std(group_blobs[0][1])/1000)
            if sr1 == 61:
                dps[1].append(np.std(group_blobs[1][1])/1000)
            if sr2 == 61:
                dps[2].append(np.std(group_blobs[2][1])/1000)

        for i in range(len(dps)):
            xs, ys = get_cdf_pts(dps[i])
            axis[0].plot(xs, ys, label=str(perturbs[i]), color=PERTURBATION_COLORS[str(perturbs[i])])

    # axis[0].set_ylim(bottom=80)
    axis[0].set_xlim(left=0.1)
    # axis[0].set_xscale("log")
    axis[0].legend()

    plt.savefig(f"fig/time_stable/{name}.png")

# def categorty_prediction(cfg):
#     summaries = load_solver_summaries(cfg)
#     sample_size = 30
#     for solver in summaries:
#         true_unsol, est_unsol = 0, 0
#         true_stable, est_stable = 0, 0
#         for query_row in summaries[solver]:
#             group_blobs = query_row[2]
#             for i in range(group_blobs.shape[0]):
#                 sample = group_blobs[i][:,:sample_size]
#                 sample_success = successes_within_timeout(sample)
#                 true_success = successes_within_timeout(group_blobs[i])
#                 if sample_success == 0:
#                     est_unsol += 1
#                     if true_success == 0:
#                         true_unsol += 1
#                 if sample_success == sample_size:
#                     est_stable += 1
#                     if true_success == group_blobs.shape[2]:
#                         true_stable += 1
#         print(solver, 
#               round(percentage(true_unsol, est_unsol), 2),
#               round(percentage(true_stable, est_stable), 2))

def export_timeouts(cfg, solver):
    con, cur = get_cursor(cfg.qcfg.db_path)
    solver_table = cfg.qcfg.get_solver_table_name(solver)

    if not check_table_exists(cur, solver_table):
        print(f"[WARN] export timeout: {solver_table} does not exist!")
        con.close()
        return
    clean_dir = cfg.qcfg.project.clean_dirs[solver]
    assert clean_dir.endswith("/")
    target_dir = clean_dir[:-1] + "_"+ str(solver) + "_ext/"

    res = cur.execute(f"""
        SELECT vanilla_path, perturbation, command FROM {solver_table}
        WHERE result_code = "timeout" """)

    rows = res.fetchall()
    # print(len(rows))

    for row in rows:
        vanilla_path = row[0]
        perturb = row[1]
        assert vanilla_path.endswith(".smt2")
        assert vanilla_path.startswith(clean_dir)
        stemed = vanilla_path[len(clean_dir):-5]
        command = row[2]
        [solver_path, mut_path, limit] = command.split(" ")
        index = mut_path.index(stemed) + len(stemed)
        info = mut_path[index:].split(".")
        # print(vanilla_path)
        if perturb is None:
            command = f"cp {vanilla_path} {target_dir}"
        else:
            seed = int(info[1])
            assert perturb == info[2]
            file_name = f"{str(seed)}.{perturb}.smt2"
            mutant_path = target_dir + stemed + "." + file_name
            command = f"./target/release/mariposa -i {vanilla_path} -p {perturb} -o {mutant_path} -s {seed}"
        print(command)

    con.close()

def plot_query_sizes(cfgs):
    import os
    # figure, axis = setup_fig(1, 2)
    colors = get_color_map([cfg.qcfg.name for cfg in cfgs])

    for cfg in cfgs:
        clean_dir = cfg.qcfg.project.clean_dirs[Z3_4_11_2]
        paths = list_smt2_files(clean_dir)
        sizes = [] 
        for path in paths:
            sizes.append(os.path.getsize(path) / 1024)
        n = len(sizes)
        label = cfg.qcfg.name
        color = colors[label]
        plt.plot(np.sort(sizes), np.arange(n), marker=".", label=label, color=color)

    plt.legend()
    plt.xscale("log")
    plt.ylabel("cumulative count")
    plt.xlabel("query size KB (log scale)")

    plt.tight_layout()
    plt.savefig("fig/sizes.pdf")

def dump_all(cfgs=ALL_CFGS):
    project_names = [cfg.get_project_name() for cfg in cfgs]
    solver_names = [str(s) for s in Z3_SOLVERS_ALL]

    category_count = len(Stablity)
    thres = Classifier("t_test")
    thres.timeout = 61e3 # 1 min
    # thres.res_stable = 80
    # thres.time_std = 6e3 # 6 sec

    data = np.zeros((len(cfgs), len(solver_names), category_count))
    for cfg in cfgs:
        summaries = load_solver_summaries(cfg)
        for solver in tqdm(solver_names):
            if solver in summaries:
                items = categorize_queries(summaries[solver], thres)
                ps, _ = get_category_percentages(items)
                ps = [ps[c] for c in Stablity]
                data[cfgs.index(cfg), solver_names.index(solver)] = ps
    print(data.tolist())

    data = np.array(data)

    bar_width = len(solver_names)/100
    fig, ax = plt.subplots()
    fig.set_size_inches(8, 4)

    br = np.arange(len(solver_names))
    br = [x - bar_width for x in br]

    # data[project_index][solver_index][category_index]

    for pi, project_row in enumerate(data):
        pcs = np.zeros((category_count, len(solver_names)))

        br = [x + bar_width for x in br]
        for i, ps in enumerate(project_row):
            pcs[:, i] = ps
        pcolor = PROJECT_COLORS[project_names[pi]]
        pcs = np.cumsum(pcs,axis=0)

        plt.bar(br, height=pcs[1], width=bar_width, color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.2)
        plt.bar(br, height=pcs[2]-pcs[1], bottom=pcs[1], width=bar_width, color=pcolor,label=project_names[pi], edgecolor='black', linewidth=0.2)

        for i in range(len(solver_names)):
            if solver_names[i] == str(cfgs[pi].qcfg.project.orig_solver):
                plt.bar(br[i], height=pcs[1][i], width=bar_width, color=pcolor, alpha=0.40, edgecolor='black', linewidth=0.2, hatch='xxxx')
                plt.bar(br[i], height=pcs[2][i]-pcs[1][i], bottom=pcs[1][i], width=bar_width, color=pcolor, edgecolor='black', linewidth=0.2, hatch='xxxx')

    # plt.ylim(bottom=0, top=8)
    plt.xlabel('solvers', fontsize = 12)
    plt.ylabel('categorty ratios', fontsize = 12)
    solver_lables = [f"{str(s).replace('_', '.')}\n{s.data[:-3]}" for s in Z3_SOLVERS_ALL]
    ax.tick_params(axis='both', which='major', labelsize=8)
    plt.xticks([r + bar_width for r in range(len(solver_names))], solver_lables, rotation=30, ha='right')
    plt.legend()
    plt.tight_layout()
    plt.savefig("fig/all.pdf")

def compare_vbkvs(linear, dynamic):
    dfiles, lfiles = set(), set()
    for k, v in FILE_MAP.items():
        dfiles |= set(v[0])
        lfiles |= set(v[1])
    # print(len(lfiles))
    # print(len(dfiles))

    th = Classifier("t_test")
    th.timeout = 61e4
    # th.unsolvable = 20
    # th.res_stable = 80
    th.time_std = 5e3

    linear_filtered = set()
    for query in linear.samples[Z3_4_11_2]:
        for f in lfiles:
            if "-" + f in query:
                linear_filtered.add(query)
    dynamic_filtered = set()
    for query in dynamic.samples[Z3_4_11_2]:
        for f in dfiles:
            if "-" + f in query:
                dynamic_filtered.add(query)
                break

    data = np.zeros((4, len(Stablity)))

    linear_summary = load_solver_summary(linear, linear.qcfg.project.orig_solver, get_unknowns(linear))
    linear_categories = categorize_queries(linear_summary, th)

    linear_filtered_categories = {c: set() for c in Stablity}
    for c, qs in linear_categories.items():
        linear_filtered_categories[c] = qs.intersection(linear_filtered)

    lcs, ltot = get_category_percentages(linear_categories)
    lcs = [lcs[c] for c in Stablity]

    lfcs, lftot = get_category_percentages(linear_filtered_categories)
    lfcs = [lfcs[c] for c in Stablity]

    dynamic_summary = load_solver_summary(dynamic, dynamic.qcfg.project.orig_solver, get_unknowns(dynamic))
    d_categories = categorize_queries(dynamic_summary, th)

    dynamic_filtered_categories = {c: set() for c in Stablity}

    for c, qs in d_categories.items():
        dynamic_filtered_categories[c] = qs.intersection(dynamic_filtered)
    
    dcs, dtot = get_category_percentages(d_categories)
    dcs = [dcs[c] for c in Stablity]

    dfcs, dftot = get_category_percentages(dynamic_filtered_categories)
    dfcs = [dfcs[c] for c in Stablity]

    data[0] = lcs
    data[1] = lfcs
    data[2] = dcs
    data[3] = dfcs

    print(data.tolist())

    data = np.cumsum(data, axis=1)

    solver_names = [str(s) for s in Z3_SOLVERS_ALL]
    bar_width = len(solver_names)/100
    fig, ax = plt.subplots()
    # print(data[:, 0])

    br = np.arange(4)
    # br = [x - bar_width for x in br]

    # plt.bar(br, height=data[:, 0], width=bar_width, alpha=0.40, edgecolor='black', linewidth=0.2)
    # br = [x + bar_width for x in br]
    plt.bar(br, height=data[:, 1]-data[:, 0], width=bar_width, alpha=0.40, edgecolor='black', linewidth=0.2)
    br = [x + bar_width for x in br]
    plt.bar(br, height=data[:, 2]-data[:, 1], width=bar_width, alpha=0.40, edgecolor='black', linewidth=0.2)
    br = [x + bar_width for x in br]
    plt.bar(br, height=data[:, 3]-data[:, 2], width=bar_width, alpha=0.40, edgecolor='black', linewidth=0.2)

    plt.legend()
    plt.tight_layout()
    plt.savefig("fig/compare.pdf")

# def analyze_regression(cfg, solver):
#     unkowns = get_unknowns(cfg)
#     nrows = load_solver_summary(cfg, solver, unkowns)
#     regres = []
#     tregres = []
#     imporoves = []
#     for query_row in nrows:
#         # query = query_row[0]
#         group_blobs = query_row[2]
#         plain_res = group_blobs[0][0][0]
#         plain_time = group_blobs[0][1][0]

#         # print(group_blobs.shape)
#         for group_blob in group_blobs:
#             ress = group_blob[0][1:]
#             times = group_blob[1][1:]
#             # print(len(ress), len(times))
#             if plain_res == RCode.UNSAT.value:
#                 if np.all(ress == RCode.UNSAT.value):
#                     ratio = np.median(times) / plain_time
#                     if ratio > 1.5:
#                         print(ratio)
#                 else:
#                     print(np.sum(ress == RCode.UNSAT.value))
                    
            # and plain_res == RCode.UNSAT.value:
    #             if time > plain_time:
    #                 print("regression", query)
    #         if res == RCode.UNSAT.value and plain_res != RCode.UNSAT.value:
    #             print("improve", query)
    #     # print(plain_res, np.sum(group_blobs[0][0][1:] == RCode.UNSAT.value) / 60)
    #     times = group_blobs[0][1][1:]
    #     successes = np.sum(group_blobs[0][0][1:] == RCode.UNSAT.value)
    #     if plain_res == RCode.UNSAT.value:
    #         regres.append(successes * 100 / 60)
    #         tregres.append(np.median(times) / plain_time)
    #     else:
    #         imporoves.append(successes * 100 / 60)
    # print(np.sum(np.array(regres) < 80))
    # print(np.sum(np.array(tregres) > 1.5))
    # print(imporoves)

        # tt = (group_blobs[0][1][0], np.median(times), np.min(times), np.max(times))
        # print(tt)

def do_stuff(cfg):
    summaries = load_solver_summaries(cfg)
    # perturbs = [str(p) for p in cfg.qcfg.enabled_muts]

    solver_count = len(cfg.samples.keys())
    cut_figure, cut_aixs = setup_fig(solver_count, 1)
    xs = [i for i in range(5, 62, 1)]
    perturbs = [str(p) for p in cfg.qcfg.enabled_muts]
    skip = get_unknowns(cfg)

    for j, solver in enumerate(cfg.samples.keys()):
        sps = cut_aixs
        if solver_count != 1:
            sps = cut_aixs[j]

        rows = summaries[solver]
        pts = [[], [], []]
        for query_row in rows:
            group_blobs = query_row[2]
            t = min(group_blobs[0][1][0], 60000)
            for j in range(3):
                times = group_blobs[:,1][j]
                times = np.clip(times, 0, 60000)
                pts[j].append((t, np.median(times), np.min(times), np.max(times)))

        for pt in pts:
            pt.sort(key=lambda x: x[0])

        xs = np.arange(start=0, stop=len(pts[0])*3, step=3)

        sps.scatter([p[0] for p in pts[0]], [p[1] for p in pts[0]], label="shuffle", marker='.')
        sps.scatter([p[0] for p in pts[1]], [p[1] for p in pts[1]], label="rename", marker='.')
        sps.scatter([p[0] for p in pts[2]], [p[2] for p in pts[1]], label="rseed", marker='.')
        x = np.linspace(0, 60000, 100)
        y = 2*x
        sps.plot(x, y)
        y = x/2
        sps.plot(x, y)
        
        sps.set_ylim(0, 60000)
        sps.set_xlim(0, 60000)

        sps.set_aspect('equal', adjustable='box')
        sps.legend()
        plt.tight_layout()
        name = cfg.qcfg.name
        plt.savefig(f"fig/time_scatter/{name}.png")

def do_what(cfg):
    for cfg in [D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG]:
        summaries = load_solver_summaries(cfg, skip_unknowns=False)
        for query_row in summaries[Z3_4_8_8]:
            sc = 1000
            if query_row[0] in issues:
                group_blobs = query_row[2]
                for i in range(group_blobs.shape[0]):
                    group_blob = group_blobs[i]
                    sc = min(count_within_timeout(group_blob, RCode.UNSAT, timeout=61e3), sc)
                print(sc)
        # th = Classifier("strict")
        # th.timeout = 6e4
        # categories1 = categorize_queries(summaries[Z3_4_8_5], th)
        # categories2 = categorize_queries(summaries[Z3_4_8_8], th)
        # diff = categories2[Stablity.RES_UNSTABLE.value] - categories1[Stablity.STABLE.value]
        # # assert "data/d_komodo_z3_clean/verified-smcapi.i.dfyImpl___module.__default.lemma__sha256__suffix.smt2" in categories2[Stablity.RES_UNSTABLE.value]

        # # for query_row in summaries[Z3_4_8_8]:
        # #     if "data/d_komodo_z3_clean/verified-pagedb.i.dfyCheckWellformed___module.__default.pageDbL2PTableCorresponds.smt2" in query_row[0]:
        # #         print(query_row)
        # print(len(diff))
    
    # summaries = load_solver_summaries(cfg)
    # summary = summaries[Z3_4_8_8]

    
    # print(summary)

