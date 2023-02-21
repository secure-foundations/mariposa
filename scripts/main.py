from configs.projects import *
from configs.experiments import *
from runner import Runner
from db_utils import *
from analyzer import *

S_KOMODO = ProjectConfig("s_komodo", FrameworkName.SERVAL, Z3_4_4_2)
S_KOMODO.assign_cvc5_dirs("data/s_komodo_plain/")
S_KOMODO.assign_z3_dirs("data/s_komodo_plain/")

D_KOMODO = ProjectConfig("d_komodo", FrameworkName.DAFNY, Z3_4_5_0)
D_KOMODO.assign_cvc5_dirs("data/d_komodo_cvc5_clean/")

D_FVBKV = ProjectConfig("d_fvbkv", FrameworkName.DAFNY, Z3_4_6_0)
D_LVBKV = ProjectConfig("d_lvbkv", FrameworkName.DAFNY, Z3_4_8_5)
FS_VWASM = ProjectConfig("fs_vwasm", FrameworkName.FSTAR, Z3_4_8_5)
FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)

Z3_SOLVERS = [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_8_5, Z3_4_11_2]

S_KOMODO_BASIC_CFG = ExpConfig("S_KOMODO", S_KOMODO, ALL_SOLVERS)
D_KOMODO_BASIC_CFG = ExpConfig("D_KOMODO", D_KOMODO, ALL_SOLVERS)
D_FVBKV_Z3_CFG = ExpConfig("D_FVBKV_Z3", D_FVBKV, [Z3_4_4_2, Z3_4_5_0, Z3_4_6_0, Z3_4_11_2])
FS_VWASM_CFG = ExpConfig("FS_VWASM", FS_VWASM, Z3_SOLVERS)
D_LVBKV_CFG = ExpConfig("D_LVBKV", D_LVBKV, Z3_SOLVERS)
FS_DICE_CFG = ExpConfig("FS_DICE", FS_DICE, Z3_SOLVERS)

if __name__ == '__main__':
    cfgs = [S_KOMODO_BASIC_CFG, D_KOMODO_BASIC_CFG, D_FVBKV_Z3_CFG, FS_VWASM_CFG, D_LVBKV_CFG, FS_DICE_CFG]

    # print_summary_data(cfgs)
    plot_query_sizes(cfgs)
    dump_all(cfgs)
    for cfg in cfgs:
        plot_time_mixed(cfg)
        plot_time_success(cfg)

    # build_summary_table(D_LVBKV_CFG)
    # append_summary_table(D_LVBKV_CFG, Z3_4_5_0)

    # tables = [
    #     "D_LVBKV_z3_4_5_0",
    #     "D_LVBKV_z3_4_6_0"]
    # import_tables("data/mariposa2.db", tables)

    # # cfg = ExpConfig("D_FVBKV_Z3", D_FVBKV, [Z3_4_4_2])
    # cfg = ExpConfig("D_KOMODO_SHUFFLE_2", D_KOMODO, [Z3_4_11_2], 10)
    # cfg.qcfg.enabled_muts = [Mutation.LOWER_SHUFFLE, Mutation.SHUFFLE]
    # # cfg = ExpConfig("D_LVBKV", D_LVBKV, [Z3_4_8_5, Z3_4_11_2])
    # r = Runner(cfg, True)
