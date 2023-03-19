from configs.projects import *
from configs.experiments import *
from runner import Runner, subprocess_run
from db_utils import *

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
S_KOMODO.assign_z3_dirs("data/s_komodo_clean/")
S_KOMODO.assign_cvc5_dirs("data/s_komodo_clean/")

S_CERTIKOS = ProjectConfig("s_certikos", FrameworkName.SERVAL, Z3_4_4_2)
S_CERTIKOS.assign_z3_dirs("data/s_certikos_clean/")
S_CERTIKOS.assign_cvc5_dirs("data/s_certikos_clean/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
# D_KOMODO.assign_cvc5_dirs("data/d_komodo_cvc5_clean/")

D_FVBKV = ProjectConfig("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectConfig("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)

FS_VWASM = ProjectConfig("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_VWASM.assign_cvc5_dirs("data/fs_vwasm_cvc5_clean/")

FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

# Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8, Z3_4_8_11, Z3_4_8_17, Z3_4_11_2]

S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, Z3_SOLVERS_ALL, DB_PATH)
D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, Z3_SOLVERS_ALL, DB_PATH)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS_ALL, DB_PATH)
D_FVBKV_CFG = ExpConfig("D_FVBKV", D_FVBKV, Z3_SOLVERS_ALL, DB_PATH)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS_ALL, DB_PATH)
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, Z3_SOLVERS_ALL, DB_PATH)
S_CERTIKOS_CFG = ExpConfig("S_CERTIKOS", S_CERTIKOS, Z3_SOLVERS_ALL, DB_PATH)

ALL_CFGS = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG, FS_VWASM_CFG]

UNSOL_Z3 = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_11_2]
S_KOMODO_UNSOL_CFG = ExpConfig("S_KOMODO_UNSOL", S_KOMODO, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
D_KOMODO_UNSOL_CFG = ExpConfig("D_KOMODO_UNSOL", D_KOMODO, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
D_LVBKV_UNSOL_CFG = ExpConfig("D_LVBKV_UNSOL", D_LVBKV, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
D_FVBKV_UNSOL_CFG = ExpConfig("D_FVBKV_UNSOL", D_FVBKV, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
FS_DICE_UNSOL_CFG = ExpConfig("FS_DICE_UNSOL", FS_DICE, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
FS_VWASM_UNSOL_CFG = ExpConfig("FS_VWASM_UNSOL", FS_VWASM, UNSOL_Z3, "data/mariposa.saved.db", load_list=True)
ALL_UNSOL_CFGs = [S_KOMODO_UNSOL_CFG, D_KOMODO_UNSOL_CFG, D_LVBKV_UNSOL_CFG, D_FVBKV_UNSOL_CFG, FS_DICE_UNSOL_CFG, FS_VWASM_UNSOL_CFG]

for cfg in ALL_UNSOL_CFGs:
    cfg.qcfg.max_mutants = 5
    cfg.qcfg.timeout = 120

def analyze_results():
    from analyzer import load_summary_table, plot_cutoff, dump_all, build_summary_table, compare_perturbations
    # analyze_d_komodo_sus(D_KOMODO_CFG)

    # cfgs = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, FS_VWASM_CFG]
    # D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, [Z3_4_11_2], DB_PATH)
    # plot_cutoff(D_KOMODO_CFG)
    compare_perturbations(D_LVBKV_CFG)
    # do_stuff(D_LVBKV_CFG)
    # dump_all(cfgs)
    # total = 0
    # for cfg in ALL_UNSOL_CFGs:
    #     print(cfg.qcfg.name)
    #     for solver, summaries in load_summary(cfg, None).items():
    #         counts = {"stable":0, "time_unstable":0, "res_unstable":0, "to_unsolvable": 0, "uk_unsolvable": 0}
    #         for row in summaries:
    #             pres = row[2]
    #             sr = get_all_sr(pres, row[4])
    #             all_vres = [pres]
    #             all_times = [row[3]]
    #             for (_, vres, times) in row[4]:
    #                 all_vres += vres
    #                 all_times += times
    #             if set(all_vres) == {"unknown"}:
    #                 counts["uk_unsolvable"] += 1
    #             elif sr == 100:
    #                 std = round(np.std(all_times) / 1000, 2)
    #                 if std < 3:
    #                     counts["stable"] += 1
    #                 else:
    #                     counts["time_unstable"] += 1
    #             elif sr == 0:
    #                 counts["to_unsolvable"] += 1
    #             else:
    #                 counts["res_unstable"] += 1
    #             # print(sr)
    #             # if pres not in counts:
    #             #     counts[pres] = 0
    #             # counts[pres] += 1
    #         total += len(summaries)
    #         print(solver, len(summaries), counts)
    # print("total solver/plain query pair tested: ", total)
    # plot_basic(cfg, summaries)
    # print(intervals)
    # plot_time_stable(cfg, summaries)
    # plot_time_mixed(cfg, summaries)

    # print_summary_data(cfgs)
    # plot_query_sizes(cfgs)

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

if __name__ == '__main__':
    print("building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    assert stdout == "master"
    os.system("cargo build --release")

    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"

    analyze_results()

    # cfg = ExpConfig("S_CERTIKOS", S_CERTIKOS, [Z3_4_4_2], DB_PATH, count=100)
    # cfg.qcfg.max_mutants = 0
    # r = Runner([cfg], override=True)

    from analyzer import build_summary_table, append_summary_table
    # build_summary_table(D_LVBKV_CFG)
    # import_database("s1902")
    # append_summary_table(D_KOMODO_CFG, Z3_4_8_11)

    # cfg = ExpConfig("D_LVBKV", D_LVBKV, [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_8])
    # r = Runner([cfg], override=True)
