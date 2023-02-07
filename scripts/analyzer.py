import sqlite3
from db_utils import *
import scipy.stats as stats
import numpy as np
import math
from tqdm import tqdm
import ast
from datetime import datetime

from runner import ALL_MUTS
from configs.projects import *
from configs.experiments import *
from plot_utils import *
import matplotlib.pyplot as plt

def as_seconds(milliseconds):
    return milliseconds / 1000

def as_percentage(p):
    return round(p * 100, 2)

def build_unstable_table(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    unstable_table_name = "unstable_" + cfg.table_name

    cur.execute(f"""DROP TABLE IF EXISTS {unstable_table_name}""")

    cur.execute(f"""CREATE TABLE {unstable_table_name} (
        solver varchar(10),
        vanilla_path varchar(255),
        v_result_code varchar(10),
        v_elapsed_milli INTEGER,
        shuffle_summary TEXT,
        rename_summary TEXT,
        sseed_summary TEXT
        )""")

    for solver in cfg.samples:
        solver = str(solver)
        res = cur.execute("DROP VIEW IF EXISTS solver_view");
        res = cur.execute(f"""
            CREATE VIEW solver_view AS 
            SELECT query_path, vanilla_path, perturbation, result_code, elapsed_milli
            FROM {cfg.table_name}
            WHERE command LIKE "%{solver}%"
            """)

        res = cur.execute(f"""
            SELECT query_path, result_code, elapsed_milli
            FROM solver_view
            WHERE query_path = vanilla_path
            """)

        vanilla_rows = res.fetchall()
        for (vanilla_path, v_rcode, v_time) in tqdm(vanilla_rows):
            res = cur.execute("DROP VIEW IF EXISTS query_view");
            res = cur.execute(f"""CREATE VIEW query_view AS 
                SELECT result_code, elapsed_milli, perturbation FROM solver_view
                WHERE query_path != vanilla_path
                AND vanilla_path = "{vanilla_path}" """)

            results = dict()

            for perturb in ALL_MUTS:
                res = cur.execute(f"""
                    SELECT * FROM query_view
                    WHERE perturbation = ?
                    """, (perturb,))
                rows = res.fetchall()
                sample_size = len(rows)
                veri_res = [r[0] for r in rows]
                veri_times = [r[1] for r in rows]

                if sample_size == 0:
                    print("[WARN] 0 sample size encountered")
                    print(vanilla_path)
                    results[perturb] = (0, 0, [], [])
                    continue

                p = veri_res.count("unsat") / sample_size

                # get the sample standard deviation
                time_stdev = np.std(veri_times, ddof=1)
                results[perturb] = (p, time_stdev, veri_res, veri_times)

            summaries = []
            for perturb, (_, _, veri_res, veri_times) in results.items():
                summary = (perturb, veri_res, veri_times)
                summaries.append(str(summary))

            cur.execute(f"""INSERT INTO {unstable_table_name}
                VALUES(?, ?, ?, ?, ?, ?, ?);""", 
                (solver, vanilla_path, v_rcode, v_time, summaries[0], summaries[1], summaries[2]))
    con.commit()

def process_mut_group(summary, v_res, v_time):
    (perturb, veri_res, veri_times) = summary
    assert len(veri_res) != 0
    assert len(veri_res) == len(veri_times)
    p1 = as_percentage(veri_res.count("unsat") / len(veri_res))
    sd1 = as_seconds(np.std(veri_times, ddof=1))
    nt_veri_times = []
    # for i, t in enumerate(veri_times):
    #     if veri_res[i] != 'timeout':
    #         nt_veri_times.append(t)
    # if len(nt_veri_times) != 0:
    #     # diff = as_seconds(np.average(nt_veri_times) - v_time)
    #     sd2 = as_seconds(np.std(nt_veri_times, ddof=1))
    # else:
    #     sd2 = np.nan
    return sd1
    # if 0 < p1 < 100:
    #     print(p1, round(sd1 - sd2, 2))

class QueryRes:
    def __init__(self):
        self.skip = False
        self.solvable = False
        self.res_unstable = False
        self.time_unstable = False

def process_query_experiment(summaries, v_res, v_time):
    qr = QueryRes()
    for s in summaries:
        if len(s[1]) == 0:
            qr.skip = True
            return qr
    all_res = set()
    sds = []
    for s in summaries:
        sd = process_mut_group(s, v_res, v_time)
        sds.append(sd)
        all_res |= set(s[1])
    all_res.add(v_res)
    if 'unsat' in all_res:
       qr.solvable = True
    if "sat" in all_res:
        print("[WARN] SAT in result code!")

    if all_res - {'unsat'} != set():
        qr.res_unstable = True

    for sd in sds:
        if sd > 5:
            qr.time_unstable = True
    return qr

def plot_time_cdf_comparison(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    unstable_table_name = "unstable_" + cfg.table_name

    aixs = setup_project_time_cdfs(cfg.project.name)
    for i, solver in enumerate(cfg.samples):
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {unstable_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()

        dists = {"plain": [], "shuffle": [],  "rename": [], "sseed": []}
        for row in rows:
            dists["plain"].append(row[3])
            summaries = [ast.literal_eval(row[i]) for i in range(4, 7)]

            if len(summaries[0][2]) != 0:
                dists["shuffle"].append(np.average(summaries[0][2]))
            if len(summaries[1][2]) != 0:
                dists["rename"].append(np.average(summaries[1][2]))
            if len(summaries[2][2]) != 0:
                dists["sseed"].append(np.average(summaries[2][2]))
        plot_time_cdfs(aixs[i], dists, solver)

    name = f"fig/time_cdf_{cfg.project.name}.png"
    plt.savefig(name)
    con.close()

def plot_time_variance_cdf(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    unstable_table_name = "unstable_" + cfg.table_name

    aixs = setup_fig(cfg.project.name, 3, 1)
    for i, solver in enumerate(cfg.samples):
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {unstable_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()

        dists = {"shuffle": [],  "rename": [], "sseed": []}
        for row in rows:
            # dists["plain"].append(row[3])
            summaries = [ast.literal_eval(row[i]) for i in range(4, 7)]

            if len(summaries[0][2]) != 0:
                dists["shuffle"].append(as_seconds((np.std(summaries[0][2]))))
            if len(summaries[1][2]) != 0:
                dists["rename"].append(as_seconds(np.std(summaries[1][2])))
            if len(summaries[2][2]) != 0:
                dists["sseed"].append(as_seconds(np.std(summaries[2][2])))
        plot_time_variance_cdfs(aixs[i], dists, solver)
    con.close()
    name = f"fig/time_variance_cdf_{cfg.project.name}.png"
    plt.savefig(name)

def plot_success_rate_cdf(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    unstable_table_name = "unstable_" + cfg.table_name

    aixs = setup_fig(cfg.project.name, 3, 2)
    for i, solver in enumerate(cfg.samples):
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {unstable_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()

        dists = {"shuffle": [],  "rename": [], "sseed": []}
        for row in rows:
            # dists["plain"].append(row[3])
            summaries = [ast.literal_eval(row[i]) for i in range(4, 7)]

            p1, p2, p3 = 0, 0, 0

            if len(summaries[0][2]) != 0:
                p1 = summaries[0][1].count("unsat") * 100 / len(summaries[0][2])
            if len(summaries[1][2]) != 0:
                p2 = summaries[1][1].count("unsat") * 100 / len(summaries[1][2])
            if len(summaries[2][2]) != 0:
                p3 = summaries[2][1].count("unsat") * 100 / len(summaries[2][2])

            dists["shuffle"].append(p1)
            dists["rename"].append(p2)
            dists["sseed"].append(p3)
        plot_success_rate_cdfs(aixs[i], dists, solver)
    con.close()

    name = f"fig/success_rate_cdf_{cfg.project.name}.png"
    plt.savefig(name)

def analyze_unstable_table(cfg):
    plot_success_rate_cdf(cfg)
    plot_time_variance_cdf(cfg)
    # plot_time_cdf_comparison(cfg)

    # for i, solver in enumerate(cfg.samples):
    #     solver = str(solver)

    #     res = cur.execute(f"""
    #         SELECT SUM(elapsed_milli)
    #         FROM {cfg.table_name} WHERE
    #         command LIKE "%{solver}%" 
    #         """)

    #     (cpu_hours, ) = res.fetchone()
    #     cpu_hours = round(cpu_hours / 1000 / 60 / 60, 2)

    #     res = cur.execute(f"""SELECT 
    #             COUNT(DISTINCT(vanilla_path))
    #             FROM {cfg.table_name}
    #             WHERE query_path == vanilla_path
    #             AND command LIKE "%{solver}%" """)
    #     v_count = res.fetchall()[0][0]

    #     res = cur.execute(f"""SELECT 
    #             COUNT(DISTINCT(vanilla_path))
    #             FROM {cfg.table_name}
    #             WHERE query_path == vanilla_path
    #             AND result_code == "unsat"
    #             AND command LIKE "%{solver}%" """)
    #     vs_count = res.fetchall()[0][0]

        # print("solver " + solver)
        # print(f"cpu hours: {cpu_hours}")
        # print(f"vanilla count: {v_count}")
        # print(f"vanilla success count: {vs_count} ({round(vs_count * 100 / v_count, 2)})%")
        # print(f"unsolvable: {unsolvable}")
        # print(f"solvable but result instable: {unstable}")
        # print(f"solvable but time instable: {time_unstable}")
        # print(f"skipped: {skipped}")
        # print("")


# cfg = ExpConfig("test3", D_FVBKV, [Z3_4_11_2], 20)
# build_unstable_table(cfg)

# 
cfgs = [D_KOMODO_BASIC_CFG, S_KOMODO_BASIC_CFG, D_FVBKV_Z3_CFG]
# cfgs = [D_KOMODO_BASIC_CFG]

# build_unstable_table(cfg)
for cfg in cfgs:
    analyze_unstable_table(cfg)