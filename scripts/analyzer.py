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

def as_seconds(milliseconds):
    return round(milliseconds / 1000, 2)

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
        shuffle_summary varchar(100),
        rename_summary varchar(100),
        sseed_summary varchar(100)
        )""")

    for solver in cfg.samples:
        solver = str(solver)
        res = cur.execute(f"""
            SELECT query_path, result_code, elapsed_milli
            FROM {cfg.table_name}
            WHERE query_path = vanilla_path
            AND command LIKE ?
            """, (f"%{solver}%", ))

        vanilla_rows = res.fetchall()
        for (vanilla_path, v_rcode, v_time) in tqdm(vanilla_rows):
            # if v_rcode != 'unsat':
            #     print("???")
            #     print(vanilla_path)
            #     print(vanilla_path, v_rcode, v_time)
            
            res = cur.execute("DROP VIEW IF EXISTS query_view");
            res = cur.execute(f"""
                CREATE VIEW query_view AS
                SELECT result_code, elapsed_milli, perturbation FROM {cfg.table_name}
                WHERE query_path != vanilla_path
                AND command LIKE "%{solver}%" 
                AND vanilla_path = "{vanilla_path}" """)

            results = dict()

            for perturb in ALL_MUTS:
                res = cur.execute(f"""
                    SELECT * FROM query_view
                    WHERE perturbation = ?
                    """, (perturb,))
                rows = res.fetchall()
                sample_size = len(rows)
                veri_times = [r[1] for r in rows]
                veri_res = [1 if r[0] == 'unsat' else 0 for r in rows]
                if sample_size == 0:
                    print("[WARN] 0 sample size encountered")
                    print(vanilla_path)
                    results[perturb] = (0, 0, 0)
                    continue
                p = sum(veri_res) / sample_size

                # t_critical = stats.t.ppf(q=cfg.confidence_level, df=sample_size-1)  
                # get the sample standard deviation
                time_stdev = np.std(veri_times, ddof=1)
                results[perturb] = (as_percentage(p), as_seconds(time_stdev), sample_size)

            maybe = False
            for perturb, (p, _, _) in results.items():
                if p <= 0.99:
                    maybe = True
            if maybe:
                summaries = []
                for perturb, (p, std, sz) in results.items():
                    summary = [perturb, p, std, sz]
                    summaries.append(str(summary))

                cur.execute(f"""INSERT INTO {unstable_table_name}
                    VALUES(?, ?, ?, ?, ?, ?, ?);""", (solver, vanilla_path, v_rcode, v_time, summaries[0], summaries[1], summaries[2]))
    con.commit()

def analyze_unstable_table(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    unstable_table_name = "unstable_" + cfg.table_name
    for solver in cfg.samples:
        solver = str(solver)

        res = cur.execute(f"""
            SELECT SUM(elapsed_milli)
            FROM {cfg.table_name} WHERE
            command LIKE "%{solver}%" 
            """)

        (cpu_hours, ) = res.fetchone()
        cpu_hours = round(cpu_hours / 1000 / 60 / 60, 2)

        res = cur.execute(f"""SELECT 
                COUNT(DISTINCT(vanilla_path))
                FROM {cfg.table_name}
                WHERE query_path == vanilla_path
                AND command LIKE "%{solver}%" """)
        v_count = res.fetchall()[0][0]

        res = cur.execute(f"""SELECT 
                COUNT(DISTINCT(vanilla_path))
                FROM {cfg.table_name}
                WHERE query_path == vanilla_path
                AND result_code == "unsat"
                AND command LIKE "%{solver}%" """)
        vs_count = res.fetchall()[0][0]

        res = cur.execute(f"""SELECT * FROM {unstable_table_name}
            WHERE solver = ?""", (solver, ))
        rows = res.fetchall()
        solvable = 0

        for row in rows:
            shuffle_summary = ast.literal_eval(row[4])
            rename_summary = ast.literal_eval(row[5])
            sseed_summary = ast.literal_eval(row[6])
            if shuffle_summary[1] >= 0.01 or \
                rename_summary[1] >= 0.01 or \
                    sseed_summary[1] >= 0.01:
                solvable += 1

        print("solver " + solver)
        print(f"cpu hours: {cpu_hours}")
        print(f"vanilla count: {v_count}")
        print(f"vanilla success count: {vs_count} ({round(vs_count * 100 / v_count, 2)})%")
        print(f"[0, 1) success rate in ALL mut groups: {len(rows) - solvable}")
        print(f"[1, 99] success rate in ANY mut group: {solvable}")
        print("")

    con.close()

# cfg = ExpConfig("test3", D_FVBKV, [Z3_4_11_2], 20)
# build_unstable_table(cfg)

# cfg = S_KOMODO_BASIC_CFG
cfg = D_KOMODO_BASIC_CFG
analyze_unstable_table(cfg)