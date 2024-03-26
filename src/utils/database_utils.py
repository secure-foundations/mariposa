import sqlite3, os
from utils.system_utils import log_debug, log_info, log_check, log_check

def split_zip_db(db_path):
    import glob

    DB_ROOT = "data/dbs/"

    log_check(db_path.startswith(DB_ROOT), 
              f"{db_path} not under {DB_ROOT}, skipping")

    log_check(os.path.exists(db_path), 
        f"{db_path} does not exist, skipping")

    base_name = os.path.basename(db_path)

    split_pattern = f"{DB_ROOT}/{base_name}.tar.gz.*"
    splits = glob.glob(split_pattern)

    if len(splits) > 0:
        log_check(f"{base_name} split already exists, remove?")
        os.system(f"rm {split_pattern}")

    os.system(f"cd {DB_ROOT} && tar cvzf - {base_name} | split --bytes=50MB - {base_name}.tar.gz.")

    splits = glob.glob(split_pattern)
    log_check(len(splits) > 0, f"{base_name} split failed!")

    log_info(f"{base_name} split into {len(splits)} chunks " + "\t" + " ".join(splits))

# def merge_unzipped_db():
    # os.system("cd data && mv mariposa.db mariposa.temp.db")
    # os.system("cd data && cat chunk.tar.gz.* | tar xzvf -")

def get_cursor(db_path):
    con = sqlite3.connect(db_path, timeout=10)
    cur = con.cursor()
    return con, cur

def conclude(con):
    con.commit()
    con.close()

def table_exists(cur, table_name):
    cur.execute(f"""SELECT name from sqlite_master
        WHERE type='table'
        AND name=?""", (table_name,))
    res = cur.fetchone() != None
    return res

def rename_table(cur, old_name, new_name):
    q = f"""ALTER TABLE {old_name} RENAME TO {new_name}"""
    # print(q)
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

def show_tables(db_path):
    tables = get_tables(db_path)
    for table, count in tables.items():
        print(table, count)

def create_exp_table(cur, table_name):
    cur.execute(f"""CREATE TABLE {table_name}(
        query_path TEXT NOT NULL,
        vanilla_path TEXT,
        perturbation varchar(10),
        command TEXT NOT NULL,
        std_out TEXT,
        std_error TEXT,
        result_code INTEGER,
        elapsed_milli INTEGER, 
        check_sat_id INTEGER,
        timestamp DEFAULT CURRENT_TIMESTAMP)""")
    log_debug(f"created table {table_name}")

def create_sum_table(cur, table_name):
    cur.execute(f"""CREATE TABLE {table_name} (
        vanilla_path TEXT,
        summaries BLOB,
        PRIMARY KEY (vanilla_path))""")
    # log_info(f"created table {table_name}")

def get_vanilla_paths(cur, exp_table_name):
    res = cur.execute(f"""
        SELECT vanilla_path, result_code, elapsed_milli
        FROM {exp_table_name}
        WHERE perturbation IS NULL""")
    vanilla_rows = res.fetchall()
    return vanilla_rows

def get_mutant_rows(cur, exp_table_name, v_path, mutation):
    res = cur.execute(f"""
        SELECT result_code, elapsed_milli, perturbation FROM {exp_table_name}
        WHERE vanilla_path = ?
        AND perturbation = ?""", (v_path, mutation))
    return res.fetchall()
