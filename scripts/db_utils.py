import sqlite3
import sys, os
from tqdm import tqdm

# from enum import auto

DB_PATH = "data/mariposa.db"

def create_experiment_table(cur, table_name):
    cur.execute(f"""CREATE TABLE {table_name}(
        query_path TEXT NOT NULL,
        vanilla_path TEXT,
        perturbation varchar(10),
        command TEXT NOT NULL,
        std_out TEXT,
        std_error TEXT,
        result_code varchar(10),
        elapsed_milli INTEGER, 
        timestamp DEFAULT CURRENT_TIMESTAMP
        )""")
    print(f"[INFO] created new table {table_name}")

def check_table_exists(cur, table_name):
    cur.execute(f"""SELECT name from sqlite_master
        WHERE type='table'
        AND name=?""", (table_name,))
    res = cur.fetchone() != None
    return res

# def drop_table(table_name, ignore_exist):
#     if ignore_exist:
#         cur.execute(f"""DROP TABLE IF EXISTS {table_name}""")
#     else:
#         cur.execute(f"""DROP TABLE {table_name}""")
#     con.commit()
#     con.close()

def confirm_drop_table(cur, table_name):
    if check_table_exists(cur, table_name):
        print(f"confirm to drop existing experiment table {table_name} [Y]")
        if input() != "Y":
            print(f"[WARN] abort dropping table {table_name}")
            return False
        cur.execute(f"""DROP TABLE {table_name}""")
        print(f"[INFO] dropped existing table {table_name}")
        return True
    print(f"[INFO] ignored non-existing table {table_name}")
    return True

def rename_table(cur, old_name, new_name):
    q = f"""ALTER TABLE {old_name} RENAME TO {new_name}"""
    print(q)
    cur.execute(q)

def get_tables(db_path):
    con = sqlite3.connect(db_path)
    cur = con.cursor()
    res = cur.execute("""SELECT name FROM sqlite_master
        WHERE type='table'
        ORDER BY name ASC""")
    tables = dict()
    tns = res.fetchall()
    for r in tns:
        res = cur.execute(f"""SELECT COUNT(*) FROM {r[0]}""")
        tables[r[0]] = res.fetchone()[0]
    con.close()
    return tables

def show_tables():
    tables = get_tables(DB_PATH)
    for table, count in tables.items():
        print(table, count)

def get_connection():
    return sqlite3.connect(DB_PATH)

def get_cursor():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    return con, cur

def zip_db():
    os.system(f"cd data && lrzip -z mariposa.db")

def import_tables(other_db_path):
    ts0 = get_tables(DB_PATH)
    ts1 = get_tables(other_db_path)
    tn0 = set(ts0.keys())
    tn1 = set(ts1.keys())
    for t in tn0.intersection(tn1):
        if ts0[t] != ts1[t]:
            print(f"[WARN] table row count mismatch {t} {ts0[t]} vs {ts1[t]}")

    con, cur = get_cursor()
    cur.execute(f'ATTACH "{other_db_path}" as OTHER_DB;')

    for table_name in tn1 - tn0:
        print(f"confirm importing table {table_name} [Y]")
        if input() != "Y":
            print(f"[INFO] skip importing table {table_name}")
        else:
            create_experiment_table(cur, table_name)
            cur.execute(f"INSERT INTO {table_name} SELECT * FROM OTHER_DB.{table_name}")
            print(f"[INFO] done importing table {table_name}")
    con.commit()
    con.close()

if __name__ == "__main__":
    # import_tables()
    if len(sys.argv) <= 1:
        show_tables()
    else:
        cmd = sys.argv[1]
        if cmd == "zip_db":
            zip_db()
