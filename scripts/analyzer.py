import sqlite3
from db_utils import *
import scipy.stats as stats
import numpy as np
import math

def as_seconds(milliseconds):
    return round(milliseconds / 1000, 2)

def as_percentage(p):
    return round(p * 100, 2)

cfg = ExpConfig("test2", ["z3-4.4.2"], [])
con = sqlite3.connect(DB_PATH)
cur = con.cursor()

res = cur.execute(f"""
    SELECT query_path, result_code, elapsed_milli
            FROM {cfg.table_name}
            WHERE query_path = vanilla_path
    """)

vanilla_rows = res.fetchall()

for (vanilla_path, v_rcode, v_time) in vanilla_rows:
    for perturb in ALL_MUTS:
        res = cur.execute(f"""SELECT * FROM {cfg.table_name}
            WHERE query_path != vanilla_path
            AND perturbation = ? 
            AND vanilla_path = ?""", (perturb, vanilla_path))
        # if v_rcode != 'unsat':
        #     print("???")
        #     print(vanilla_path)
        #     print(vanilla_path, v_rcode, v_time)

        rows = res.fetchall()
        sample_size = len(rows)
        if sample_size == 0:
            continue

        veri_times = [r[7] for r in rows]
        veri_res = [1 if r[6] == 'unsat' else 0 for r in rows]
        p = sum(veri_res) / sample_size
        t_critical = stats.t.ppf(q=cfg.confidence_level, df=sample_size-1)  
        # # get the sample standard deviation
        time_stdev = np.std(veri_times, ddof=1)
        # standard deviation estimate
        # sigma = time_stdev/math.sqrt(sample_size) 
        # time_moe = t_critical * sigma
        # statistics.stdev

        # if p <= 0.9:
            # print(vanilla_path)
        print(as_percentage(p), as_seconds(time_stdev))

# print(len(rows))
# print(len(set(rows)))

con.close()