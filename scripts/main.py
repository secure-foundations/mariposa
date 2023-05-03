from configs.projects import *
from configs.experiments import *
from runner import Runner, subprocess_run
from db_utils import *
from analyzer import *

def import_database(other_server):
    other_db_path = "data/mariposa2.db"
    os.system(f"rm {other_db_path}")
    os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {other_db_path}")
    import_tables(other_db_path)

def clean_queries(cfg):
    from clean_utils import clean_dfy_project
    from clean_utils import clean_fs_project
    clean_dfy_project(cfg, cfg.clean_dirs[Z3_4_11_2])

def send_project_queries(project, other_server):
    pass

def sample_projects(projects):
    for proj in projects:
        print(proj)

def gen_bisec_tasks():
    for cfg in ALL_CFGS:
        summaries = load_solver_summaries(cfg, skip_unknowns=False)
        classifier = Classifier("z_test")
        classifier.timeout = 6e4
        categories1 = categorize_queries(summaries[Z3_4_8_5], classifier)
        categories2 = categorize_queries(summaries[Z3_4_8_8], classifier)
        diff = categories1[Stablity.STABLE.value].intersection(categories2[Stablity.UNSTABLE.value])
        # print(len(diff))
        for l in diff:
            solver_table = cfg.qcfg.get_solver_table_name(Z3_4_8_8)
            con, cur = get_cursor(cfg.qcfg.db_path)
            res = cur.execute(f"""SELECT query_path FROM {solver_table}
                WHERE vanilla_path = '{l}'
                AND perturbation != ''
                """)
            assert(l.startswith("data/"))
            assert(l.endswith(".smt2"))
            p = l[5:-5]
            tsk = open("data/bisect_tasks/" + p.replace("/", "--") + ".txt", "w+")
            tsk.write(f"{l}\n")
            for row in res.fetchall():
                mpath = row[0]
                assert mpath.find(p) != -1
                args = mpath.split(".")[-3:]
                assert args[-1] == "smt2"
                command = f"./target/release/mariposa -i {l} -p {args[1]} -o {row[0]} -s {args[0]}\n"
                tsk.write(command)

from datetime import datetime

def get_runtime():
    con, cur = get_cursor()
    total = 0
    for cfg in ALL_CFGS:
        for solver in cfg.samples:
            solver_table = cfg.qcfg.get_solver_table_name(solver)
            res = cur.execute(f"""
                SELECT SUM(elapsed_milli)
                FROM {solver_table}""")
            time = res.fetchone()[0] / 1000 / 3600
            # start, end = res.fetchone()
            # date from string 
            # start = datetime.strptime(start, '%Y-%m-%d %H:%M:%S')
            # end = datetime.strptime(end, '%Y-%m-%d %H:%M:%S')
            # diff = end - start
            # convert into hours
            total += time
            print(cfg.qcfg.name, solver, time)
    print(total)
            # diff = diff.total_seconds() / 3600
            # print(cfg.qcfg.name, solver, round(diff, 2))
        # print(solver_df["time"].mean())
    # solver_table = cfg.qcfg.get_solver_table_name(solver)

import re

def parse_bisect():
    commit_re = re.compile("\[([a-z0-9]+)\]")
    blames = dict()
    logs = os.listdir("data/bisect_tasks")
    for log in logs:
        if log.endswith(".txt"):
            continue
        f = open(f"data/bisect_tasks/{log}")
        lines = f.readlines()
        blames[log] = set()
        for l in lines:
            if "# first bad commit:" in l:
                blames[log].add(commit_re.search(l).group(1))
                break
            if "# possible first bad commit:" in l:
                blames[log].add(commit_re.search(l).group(1))
    for log in blames:
        count = len(blames[log])
        if count > 2:
            pass
            # print(log, count)
            # print("../mariposa/scripts/bisect-metascript.sh", log)
        else:
            print(blames[log])

if __name__ == '__main__':
    print("building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    # assert stdout == "master"
    os.system("cargo build --release")

    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"
    
    # get_runtime()
    # entropy_test()
    # create_benchmark()

    # v_test()
    # dump_all()

    # cfg = D_KOMODO_CFG
    # dump_all()
    cfg = D_KOMODO_CFG
    plot_ext_cutoff(cfg)
    plot_vbkv_ext_cutoff()
    plot_pert_diff(cfg)
    plot_time_std(cfg)
    plot_sr_cdf(cfg)
    do_stuff(cfg)

    # # get_diff_mutants()
    # for cfg in tqdm(ALL_CFGS):
    #     do_stuff(cfg)

    # plot_ext_cutoff(D_LVBKV_CFG)
    # import_database("s1905")

    # extend_solver_summary_table(D_LVBKV_CFG, D_LVBKV_TO_CFG, Z3_4_12_1)
    # build_solver_summary_table(S_CERTIKOS_CFG, Z3_4_12_1)
