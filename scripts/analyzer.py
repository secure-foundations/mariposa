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
    return p * 100

def append_summary_table(cfg, solver):
    con, cur = get_cursor()
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

        for perturb in ALL_MUTS:
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
            summary = (perturb, veri_res, veri_times)
            summaries.append(str(summary))
        cur.execute(f"""INSERT INTO {summary_table}
            VALUES(?, ?, ?, ?, ?, ?, ?);""", 
            (str(solver), vanilla_path, v_rcode, v_time, summaries[0], summaries[1], summaries[2]))
    con.commit()
    con.close()

def build_summary_table(cfg):
    con, cur = get_cursor()
    summary_table = cfg.get_summary_table_name()

    cur.execute(f"""DROP TABLE IF EXISTS {summary_table}""")

    cur.execute(f"""CREATE TABLE {summary_table} (
        solver varchar(10),
        vanilla_path TEXT,
        v_result_code varchar(10),
        v_elapsed_milli INTEGER,
        shuffle_summary TEXT,
        rename_summary TEXT,
        sseed_summary TEXT)""")

    con.commit()
    con.close()

    for solver in cfg.samples:
        append_summary_table(cfg, solver)


def plot_time_variance_cdf(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    summary_table_name = cfg.get_summary_table_name()

    figure, aixs = setup_fig(len(cfg.samples), 2)
    for i, solver in enumerate(cfg.samples):
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {summary_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()

        dists = {"shuffle": [],  "rename": [], "sseed": []}
        dists2 = {"shuffle": [],  "rename": [], "sseed": []}
        for row in rows:
            # dists["plain"].append(row[3])
            summaries = [ast.literal_eval(row[i]) for i in range(4, 7)]

            if len(summaries[0][2]) != 0:
                dists["shuffle"].append(as_seconds((np.std(summaries[0][2]))))
                dists2["shuffle"].append(np.average(summaries[0][2]))
            if len(summaries[1][2]) != 0:
                dists["rename"].append(as_seconds(np.std(summaries[1][2])))
                dists2["rename"].append(np.average(summaries[1][2]))
            if len(summaries[2][2]) != 0:
                dists["sseed"].append(as_seconds(np.std(summaries[2][2])))
                dists2["sseed"].append(np.average(summaries[2][2]))

        plot_time_variance_cdfs(aixs[i], dists, dists2, solver)
    con.close()
    count = len(dists["shuffle"])
    name = cfg.get_project_name()
    save_fig(figure, f"{name}({count})", f"fig/time_{name}.png")

def plot_success_rate_cdf(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    summary_table_name = cfg.get_summary_table_name()

    figure, aixs = setup_fig(len(cfg.samples), 2)
    for i, solver in enumerate(cfg.samples):
        solver = str(solver)
        res = cur.execute(f"""SELECT * FROM {summary_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()

        dists = {"shuffle": [],  "rename": [], "sseed": []}

        for row in rows:
            summaries = [ast.literal_eval(row[i]) for i in range(4, 7)]

            # p1, p2, p3 = 0, 0, 0
            if len(summaries[0][2]) != 0:
                p1 = summaries[0][1].count("unsat") * 100 / len(summaries[0][2])
                dists["shuffle"].append(p1)
            if len(summaries[1][2]) != 0:
                p2 = summaries[1][1].count("unsat") * 100 / len(summaries[1][2])
                dists["rename"].append(p2)
            if len(summaries[2][2]) != 0:
                p3 = summaries[2][1].count("unsat") * 100 / len(summaries[2][2])
                dists["sseed"].append(p3)
        plot_success_rate_cdfs(aixs[i], dists, solver)
    con.close()

    count = len(dists["shuffle"])
    name = cfg.get_project_name()
    save_fig(figure, f"{name}({count})", f"fig/response_{name}.png")

def analyze_unstable_table(cfg):
    plot_success_rate_cdf(cfg)
    plot_time_variance_cdf(cfg)
    # plot_time_cdf_comparison(cfg)

# cfg = ExpConfig("test3", D_FVBKV, [Z3_4_11_2], 20)
# build_unstable_table(cfg)

cfgs = [D_FVBKV_Z3_CFG]

# append_summary_table(D_FVBKV_Z3_CFG, Z3_4_5_0)
for cfg in cfgs:
    analyze_unstable_table(cfg)