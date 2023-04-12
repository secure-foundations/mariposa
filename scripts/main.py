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

if __name__ == '__main__':
    print("building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    assert stdout == "master"
    os.system("cargo build --release")

    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"

    # v_test()
    # dump_all()
    
    # plot_dkomodo_cutoff()

    # plot_sr_cdf(D_KOMODO_CFG)
    # plot_pert_diff(D_KOMODO_CFG)
    # do_what(D_KOMODO_CFG)
    plot_time_std(D_KOMODO_CFG)
    
    # for cfg in ALL_CFGS:
    #     plot_ext_cutoff(cfg)
    # cutoff_edge(D_KOMODO_CFG)

    # plot_query_sizes(ALL_CFGS)
    # compare_vbkvs(D_LVBKV_CFG, D_FVBKV_CFG)
    # export_timeouts(D_LVBKV_CFG, Z3_4_12_1)

    # cfg = ExpConfig("FS_DICE", FS_DICE, [Z3_4_12_1], DB_PATH)
    
    # for cfg in [D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG]:
    #     summaries = load_solver_summaries(cfg, skip_unknowns=False)
    #     th = Thresholds("strict")
    #     th.timeout = 6e4
    #     categories1 = categorize_qeuries(summaries[Z3_4_8_5], th)
    #     categories2 = categorize_qeuries(summaries[Z3_4_8_8], th)
    #     diff = categories2[Stablity.RES_UNSTABLE.value] - categories1[Stablity.RES_UNSTABLE.value]
    #     print(len(diff))

    # for cfg in tqdm(ALL_CFGS):
    #     do_stuff(cfg)

    # plot_ext_cutoff(D_LVBKV_CFG)
    # import_database("s1905")

    # extend_solver_summary_table(D_LVBKV_CFG, D_LVBKV_TO_CFG, Z3_4_12_1)
    # build_solver_summary_table(S_CERTIKOS_CFG, Z3_4_12_1)
