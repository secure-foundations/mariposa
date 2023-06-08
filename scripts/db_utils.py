import sqlite3
import sys, os
from tqdm import tqdm
from experiments import *
import numpy as np
from rcode import RCode
from analyzer import *
from basic_utils import *
import ast

def zip_db():
    os.system("cd data && rm chunk.tar.gz.*")
    os.system("cd data && tar cvzf - mariposa.db | split --bytes=50MB - chunk.tar.gz.")

def unzip_db():
    os.system("cd data && mv mariposa.db mariposa.temp.db")
    os.system("cd data && cat chunk.tar.gz.* | tar xzvf -")

def check_table_exists(cur, table_name):
    cur.execute(f"""SELECT name from sqlite_master
        WHERE type='table'
        AND name=?""", (table_name,))
    res = cur.fetchone() != None
    return res

def get_connection(db_path=DB_PATH):
    return sqlite3.connect(db_path)

def get_cursor(db_path=DB_PATH):
    con = sqlite3.connect(db_path)
    cur = con.cursor()
    return con, cur

def check_existing_tables(cfg, project, solver):
    exp_table = cfg.get_exp_name(project, solver)
    sum_name = cfg.get_sum_name(project, solver)
    con, cur = get_cursor(cfg.db_path)

    if check_table_exists(cur, sum_name):
        print(f"[INFO] {sum_name} already exists, remove it? [Y]")
        exit_with_on_fail(input() == "Y", f"[INFO] aborting")
        cur.execute(f"""DROP TABLE {sum_name}""")
    
    if check_table_exists(cur, exp_table):
        print(f"[INFO] {exp_table} already exists, remove it? [Y]")
        exit_with_on_fail(input() == "Y", f"[INFO] aborting")
        cur.execute(f"""DROP TABLE {exp_table}""")

    con.commit()
    con.close()

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

def show_tables(db_path=DB_PATH):
    tables = get_tables(db_path)
    for table, count in tables.items():
        print(table, count)

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
    print(f"[INFO] created table {table_name}")

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
        print(f"[INPUT] confirm importing table {table_name} [Y]")
        if input() != "Y":
            print(f"[INFO] skip importing table {table_name}")
        else:
            create_experiment_table(cur, table_name)
            cur.execute(f"INSERT INTO {table_name} SELECT * FROM OTHER_DB.{table_name}")
            print(f"[INFO] done importing table {table_name}")
    con.commit()
    con.close()

def create_sum_table(cfg, exp_table_name, sum_table_name):
    con, cur = get_cursor(cfg.db_path)

    if not check_table_exists(cur, exp_table_name):
        print(f"[WARN] table {exp_table_name} does not exist")
        con.close()
        return

    cur.execute(f"""DROP TABLE IF EXISTS {sum_table_name}""")

    cur.execute(f"""CREATE TABLE {sum_table_name} (
        vanilla_path TEXT,
        mutations TEXT,
        summaries BLOB,
        PRIMARY KEY (vanilla_path, mutations)
        )""")

    res = cur.execute(f"""
        SELECT query_path, result_code, elapsed_milli
        FROM {exp_table_name}
        WHERE query_path = vanilla_path""")

    vanilla_rows = res.fetchall()
    dup_warn = True

    processed = set()
    print(f"[INFO] post processing exp data")

    for (vanilla_path, v_rcode, v_time) in vanilla_rows:
        if vanilla_path in processed:
            continue
        processed.add(vanilla_path)

        res = cur.execute(f"""
            SELECT result_code, elapsed_milli, perturbation FROM {exp_table_name}
            WHERE vanilla_path = "{vanilla_path}"
            AND perturbation IS NOT NULL""")
        mutations = [str(p) for p in cfg.enabled_muts]
        v_rcode = RCode.from_str(v_rcode).value
        results = {p: [[v_rcode], [v_time]] for p in mutations}

        for row in reversed(res.fetchall()):
            results[row[2]][0].append(RCode.from_str(row[0]).value)
            results[row[2]][1].append(row[1])

        mut_size = cfg.num_mutant
        expected_size = mut_size + 1
        
        blob = np.zeros((len(mutations), 2, expected_size), dtype=int)
        for pi, perturb in enumerate(mutations):
            (veri_res, veri_times) = results[perturb]

            if len(veri_res) > expected_size:
                if dup_warn:
                    print(f"[WARN] {vanilla_path} has more than {mut_size} mutants with {perturb}, truncating")
                    print(f"[WARN] this may be caused by multiple runs of the same experiment. remove duplicate rows from table {exp_table_name} in {cfg.db_path} if necessary")
                dup_warn = False
                veri_res = veri_res[:expected_size]
                veri_times = veri_times[:expected_size]
            elif len(veri_res) < expected_size:
                print(f"[ERROR] {vanilla_path} has less than {mut_size} mutants, aborting")
                con.close()
                sys.exit(1)

            blob[pi][0] = veri_res
            blob[pi][1] = veri_times

        if cfg.db_mode == DBMode.UPDATE:
            cur.execute(f"""REPLACE INTO {sum_table_name}
                VALUES(?, ?, ?);""", 
                (vanilla_path, str(mutations), blob))
        else:
            cur.execute(f"""INSERT INTO {sum_table_name}
                VALUES(?, ?, ?);""", 
                (vanilla_path, str(mutations), blob))

    con.commit()
    con.close()

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

# def extend_solver_summary_table(cfg, ext_cfg, solver):
#     con, cur = get_cursor(cfg.qcfg.db_path)
#     solver_table = cfg.qcfg.get_solver_table_name(solver)
#     solver_ext_table = ext_cfg.qcfg.get_solver_table_name(solver)
#     # summary_table = cfg.get_solver_summary_table_name(solver)

#     if not check_table_exists(cur, solver_table):
#         con.close()
#         return
    
#     solver_table = cfg.qcfg.get_solver_table_name(solver)

#     res = cur.execute(f"""
#         SELECT query_path, result_code, elapsed_milli, command FROM {solver_ext_table} """)

#     ext_results = dict()
#     rows = res.fetchall()

#     for (query_path, rcode, time, command) in tqdm(rows):
#         stem = query_path.split("/")[-1]
#         ext_results[stem] = (rcode, time, command)
#         # print(stem, time, rcode)

#     res = cur.execute(f"""
#         SELECT query_path, rowid FROM {solver_table}
#         WHERE result_code = "timeout" """)

#     rows = res.fetchall()

#     for (query_path, row_id) in tqdm(rows):
#         stem = query_path.split("/")[-1]
#         (rcode, time, command) = ext_results[stem]
#         cur.execute(f"""UPDATE {solver_table}
#             SET result_code = "{rcode}",
#             elapsed_milli = {time},
#             command = "{command}"
#             WHERE rowid = {row_id}""")

#     con.commit()
#     con.close()
#     create_summary_table(cfg, solver)

def load_sum_table(project, solver, cfg=MAIN_EXP, skip=set()):
    con, cur = get_cursor(cfg.db_path)
    sum_name = cfg.get_sum_name(project, solver)

    if not check_table_exists(cur, sum_name):
        print(f"[INFO] skipping {sum_name}")
        return None

    solver = str(solver)

    res = cur.execute(f"""SELECT * FROM {sum_name}""")
    rows = res.fetchall()

    nrows = []
    mut_size = cfg.num_mutant
    for row in rows:
        if row[0] in skip:
            continue
        mutations = ast.literal_eval(row[1])
        blob = np.frombuffer(row[2], dtype=int)
        blob = blob.reshape((len(mutations), 2, mut_size + 1))
        nrow = [row[0], mutations, blob]
        nrows.append(nrow)

    con.close()
    return nrows

if __name__ == "__main__":
    # import_tables()
    # tables = get_tables("./data/mariposa.db")
    # con, cur = get_cursor("./data/mariposa.db")
    
    # for table in tables:
    #     old_table = table
    #     table = table.lower()
    #     if table.endswith("_summary"):
    #         # main_d_komodo_z3_4_5_0_sum
    #         table = "main_" + table.replace("_summary", "_sum")
    #         rename_table(cur, old_table, table)
    #     else:
    #         table = "main_" + table + "_exp"
    #         rename_table(cur, old_table, table)
    # con.commit()
    # con.close()

    if len(sys.argv) <= 1:
        show_tables()
    # else:
    #     cmd = sys.argv[1]
    #     if cmd == "zip_db":
    #         zip_db()
    #     elif cmd == "unzip_db":
    #         unzip_db()
