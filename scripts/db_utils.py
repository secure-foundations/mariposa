import sqlite3
from path_utils import *
from configer import *

# from enum import auto
# from strenum import StrEnum

# class RCode(StrEnum):

# res = cur.execute("""DROP TABLE vanilla_queries""")
# res = cur.execute("""DROP TABLE vanilla_results""")

PNAME_SERVAL_KOMODO = "serval_komodo"

def reload_vanilla_queries_table():
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    cur.execute("""DROP TABLE vanilla_queries""")
    cur.execute("""CREATE TABLE vanilla_queries(
        query_path varchar(255) NOT NULL,
        project varchar(255) NOT NULL,
        status varchar(10),
        PRIMARY KEY (query_path))""")

    print("loading " + PNAME_SERVAL_KOMODO)
    for path in list_smt2_files(SKOMODO_CLEAN_DIR):
        cur.execute(f"""INSERT INTO vanilla_queries (query_path, project, status)
            VALUES(?, ?, 'unsat');""", (path, PNAME_SERVAL_KOMODO))
    con.commit()
    con.close()

def sample_vanilla_queries(project, query_count):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()

    res = cur.execute(f"""SELECT query_path from vanilla_queries
        WHERE project = ?
        ORDER BY RANDOM() LIMIT ?;
        """, (project, query_count))
    paths = [i[0] for i in res.fetchall()]
    con.close()
    return paths

def setup_experiment_table(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
    cur.execute(f"""CREATE TABLE {cfg.table_name}(
        query_path varchar(255) NOT NULL,
        is_mut BOOL,
        command varchar(455) NOT NULL,
        std_out TEXT,
        std_error TEXT,
        elapsed_milli INTEGER, 
        timestamp DEFAULT CURRENT_TIMESTAMP
        )""")
    con.commit()
    con.close()

def drop_experiment_table(cfg):
    con = sqlite3.connect(DB_PATH)
    cur = con.cursor()
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

# show_tables()
# # reload_vanilla_queries_table()
# path = select_vanilla_queries(PNAME_SERVAL_KOMODO, 10)
# print(path)

# cur.execute("""CREATE TABLE mutant_queries(
#     mutant_path varchar(255) NOT NULL,
#     vanilla_path varchar(255) NOT NULL,
#     full_command varchar(455) NOT NULL,
#     timestamp DEFAULT CURRENT_TIMESTAMP,
#     FOREIGN KEY (vanilla_path) REFERENCES vanilla_queries(query_path)
#     )""")
