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

def show_tables():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    res = cur.execute("""SELECT name FROM sqlite_master
        WHERE type='table'
        ORDER BY name ASC""")
    for r in res.fetchall():
        res = cur.execute(f"""SELECT COUNT(*) FROM {r[0]}""")
        print(r[0], res.fetchone()[0])
    con.close()

def get_connection():
    return sqlite3.connect(DB_PATH)

def get_cursor():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    return con, cur

def zip_db():
    os.system(f"cd data && tar cvzf mariposa.db.tar.gz mariposa.db")

def import_tables():
    con, cur = get_cursor()
    cur.execute('ATTACH "data/mariposa3.db" as OTHER_DB;')
    tables = [
        "D_LVBKV_z3_4_11_2",
        "D_LVBKV_z3_4_4_2"]
    # cur.execute(f"""DROP TABLE IF EXISTS D_LVBKV_summary""")
    # cur.execute(f"""CREATE TABLE D_LVBKV_summary (
    #     solver varchar(10),
    #     vanilla_path TEXT,
    #     v_result_code varchar(10),
    #     v_elapsed_milli INTEGER,
    #     summaries TEXT)""")

    for table_name in tables:
        create_experiment_table(cur, table_name)
        cur.execute(f"INSERT INTO {table_name} SELECT * FROM OTHER_DB.{table_name}")
    con.commit()
    con.close()
    pass

if __name__ == "__main__":
    # import_tables()
    if len(sys.argv) <= 1:
        show_tables()
    else:
        cmd = sys.argv[1]
        if cmd == "zip_db":
            zip_db()
