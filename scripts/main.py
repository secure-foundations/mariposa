from configs.projects import *
from configs.experiments import *
from runner import Runner
from db_utils import *
from analyzer import *

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

Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_11_2]

S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, ALL_SOLVERS)
D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, Z3_SOLVERS)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS)
D_FVBKV_CFG = ExpConfig("D_FVBKV", D_FVBKV, Z3_SOLVERS)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS)
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, ALL_SOLVERS)

ALL_CFGS = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG, FS_VWASM_CFG]

def analyze_results(cfg):
    # build_summary_table(cfg)
    # plot_basic_overall(cfg)
    get_unstable_intervals(cfg)
    # plot_result_overall(cfg)
    # build_summary_table(D_LVBKV_CFG)
    # print_summary_data(cfgs)
    # plot_query_sizes(cfgs)
    # dump_all(cfgs)
    # for cfg in cfgs:
    #     plot_time_mixed(cfg)
    #     plot_time_success(cfg)
    pass

def import_database():
    tables = [
        "FS_VWASM_cvc5_1_0_3"]
    import_tables("data/mariposa2.db", tables)

def clean_queries():
    from clean_utils import clean_dfy_project
    from clean_utils import clean_fs_project
    cfg = FS_VWASM
    clean_fs_project(cfg, cfg.clean_dirs[Z3_4_11_2])

def send_dir():
    pass

if __name__ == '__main__':
    os.system("cargo build --release")
    print("checking scaling_governor")
    os.system("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq")
    # S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, [CVC5_1_0_3])
    analyze_results(FS_VWASM_CFG)
    # clean_queries()
    # cfg = ExpConfig("test1", D_KOMODO, [Z3_4_8_5])
    # cfg = FS_VWASM_CFG
    # import_database()
    # analyze_results(cfg)
    # cfg.num_procs = 6
    # r = Runner(cfg, True)
    # clean_queries()

    # con, cur = get_cursor()
    # cur.execute(f"select * from {cfg.qcfg.get_solver_table_name(Z3_4_8_5)}")
    # for row in cur.fetchall():
    #     print(row)
    # clean_queries()


