from configs.projects import *
from configs.experiments import *
from runner import Runner
from db_utils import *
from analyzer import *

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
S_KOMODO.assign_z3_dirs("data/s_komodo_plain/")
# S_KOMODO.assign_cvc5_dirs("data/s_komodo_plain/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
# D_KOMODO.assign_cvc5_dirs("data/d_komodo_cvc5_clean/")

D_FVBKV = ProjectConfig("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectConfig("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)

FS_VWASM = ProjectConfig("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_11_2]

S_KOMODO_CFG = ExpConfig("S_KOMODO", S_KOMODO, Z3_SOLVERS)
D_KOMODO_CFG = ExpConfig("D_KOMODO", D_KOMODO, Z3_SOLVERS)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS)
D_FVBKV_CFG = ExpConfig("D_FVBKV", D_FVBKV, Z3_SOLVERS)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS)
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, Z3_SOLVERS)

ALL_CFGS = [S_KOMODO_CFG, D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG, FS_VWASM_CFG]

def analyze_results():
    # print_summary_data(cfgs)
    # plot_query_sizes(cfgs)
    # dump_all(cfgs)
    # for cfg in cfgs:
    #     plot_time_mixed(cfg)
    #     plot_time_success(cfg)
    pass

def import_tables():
    # build_summary_table(D_LVBKV_CFG)
    # append_summary_table(D_LVBKV_CFG, Z3_4_5_0)
    # tables = [
    #     "D_LVBKV_z3_4_5_0",
    #     "D_LVBKV_z3_4_6_0"]
    # import_tables("data/mariposa2.db", tables)
    pass

def clean_queries():
    from clean_utils import clean_dfy_project
    cfg = D_KOMODO
    clean_dfy_project(cfg, cfg.clean_dirs[Z3_4_11_2])

def send_dir():
    pass

if __name__ == '__main__':
    # cfg = ExpConfig("test1", D_FVBKV, [Z3_4_8_5], 10)
    # # cfg.qcfg.enabled_muts = [Mutation.LOWER_SHUFFLE, Mutation.SHUFFLE]
    # # r = Runner(cfg, True, False)

    # con, cur = get_cursor()
    # cur.execute(f"select * from {cfg.qcfg.get_solver_table_name(Z3_4_8_5)}")
    # for row in cur.fetchall():
    #     print(row)
    clean_queries()


