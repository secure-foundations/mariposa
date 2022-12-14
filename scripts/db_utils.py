import sqlite3
from path_utils import *
from configer import *
from tqdm import tqdm

# from enum import auto
# from strenum import StrEnum

# class RCode(StrEnum):

# res = cur.execute("""DROP TABLE vanilla_queries""")
# res = cur.execute("""DROP TABLE vanilla_results""")

PNAME_SERVAL_KOMODO = "serval_komodo"
PNAME_DAFNY_TESTS = "dafny_tests"
PNAME_SMTLIB = "smtlib"

def reload_vanilla_queries_table():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    # cur.execute("""DROP TABLE vanilla_queries""")
    cur.execute("""CREATE TABLE vanilla_queries(
        query_path varchar(255) NOT NULL,
        project varchar(255) NOT NULL,
        status varchar(10),
        PRIMARY KEY (query_path))""")

    print("loading " + PNAME_SERVAL_KOMODO)
    for path in tqdm(list_smt2_files(SKOMODO_CLEAN_DIR)):
        cur.execute(f"""INSERT INTO vanilla_queries (query_path, project, status)
            VALUES(?, ?, 'unsat');""", (path, PNAME_SERVAL_KOMODO))
    
    print("loading " + PNAME_DAFNY_TESTS)

    for path in tqdm(list_smt2_files(DFY_CLEAN_DIR)):
        cur.execute(f"""INSERT INTO vanilla_queries (query_path, project, status)
            VALUES(?, ?, 'unsat');""", (path, PNAME_DAFNY_TESTS))

    print("loading " + PNAME_SMTLIB)

    for path in tqdm(list_smt2_files(SMT_ALL_DIR)):
        with open(path) as f:
            query = f.read()
            status = "unknown"
            if "(set-info :status unsat)" in query:
                status = "unsat"
            elif "(set-info :status sat)" in query:
                status = "sat"
            else:
                assert("(set-info :status unknown)" in query)
            cur.execute(f"""INSERT INTO vanilla_queries (query_path, project, status)
                VALUES(?, ?, ?);""", (path, PNAME_SMTLIB, status))

    con.commit()
    con.close()

def sample_vanilla_queries(project, query_count, status="unsat"):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    if query_count is None:
        # get all queries
        res = cur.execute("""SELECT query_path from vanilla_queries
            WHERE project = ?
            AND status = ?;
            """, (project, status))
    else:
        res = cur.execute("""SELECT query_path from vanilla_queries
            WHERE project = ?
            AND status = ?
            ORDER BY RANDOM() LIMIT ?;
            """, (project, status, query_count))
    paths = [i[0] for i in res.fetchall()]
    con.close()
    return paths

def setup_experiment_table(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    cur.execute(f"""CREATE TABLE {cfg.table_name}(
        query_path varchar(255) NOT NULL,
        vanilla_path varchar(255),
        command varchar(455) NOT NULL,
        std_out TEXT,
        std_error TEXT,
        result_code varchar(10),
        elapsed_milli INTEGER, 
        timestamp DEFAULT CURRENT_TIMESTAMP
        )""")
    con.commit()
    con.close()

def drop_experiment_table(cfg, ignore_exist):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    if ignore_exist:
        cur.execute(f"""DROP TABLE IF EXISTS {cfg.table_name}""")
    else:
        cur.execute(f"""DROP TABLE {cfg.table_name}""")
    con.commit()
    con.close()

def show_tables():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    res = cur.execute("""SELECT name FROM sqlite_master
        WHERE type='table'""")
    print(res.fetchall())
    con.close()

if __name__ == "__main__":
    show_tables()
    # reload_vanilla_queries_table()
# cur.execute("""CREATE TABLE mutant_queries(
#     mutant_path varchar(255) NOT NULL,
#     vanilla_path varchar(255) NOT NULL,
#     full_command varchar(455) NOT NULL,
#     timestamp DEFAULT CURRENT_TIMESTAMP,
#     FOREIGN KEY (vanilla_path) REFERENCES vanilla_queries(query_path)
#     )""")
