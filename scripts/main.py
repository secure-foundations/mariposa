from configs.projects import *
from configs.experiments import *
from runner import Runner, subprocess_run
from db_utils import *

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
S_KOMODO.assign_z3_dirs("data/s_komodo_clean/")
S_KOMODO.assign_cvc5_dirs("data/s_komodo_clean/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
# D_KOMODO.assign_cvc5_dirs("data/d_komodo_cvc5_clean/")

D_FVBKV = ProjectConfig("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectConfig("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)

FS_VWASM = ProjectConfig("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_VWASM.assign_cvc5_dirs("data/fs_vwasm_cvc5_clean/")

FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_8_6, Z3_4_8_7, Z3_4_8_8, Z3_4_8_11, Z3_4_8_17, Z3_4_11_2]

S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, ALL_SOLVERS)
D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, Z3_SOLVERS)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS)
D_FVBKV_CFG = ExpConfig("D_FVBKV", D_FVBKV, Z3_SOLVERS)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS)
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, ALL_SOLVERS)

ALL_CFGS = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG, FS_VWASM_CFG]

def analyze_results():
    from analyzer import dump_all, load_summary, get_categories
    cfgs = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_VWASM_CFG, FS_DICE_CFG]
    dump_all(cfgs, timeout_threshold=None, time_std_threshold=3000)
    # for cfg in cfgs:
    # # build_summary_table(cfg)
    #     print(cfg.qcfg.name)
    #     summaries = load_summary(cfg, 40)
    #     get_categories(summaries)
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

    # from clean_utils import clean_fs_project
    # clean_fs_project(FS_DICE, None, "data/fs_dice_cvc5_clean/")

    # import_database("s1905")
    # append_summary_table(D_FVBKV_CFG, Z3_4_8_11)

    # analyze_d_komodo_sus(D_KOMODO_CFG)

    # cfg = ExpConfig("D_KOMODO", D_KOMODO, [Z3_4_8_7])

    analyze_results()
    # build_summary_table(FS_DICE_CFG)