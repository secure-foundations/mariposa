from configs.projects import *
from configs.experiments import *
from runner import Runner, subprocess_run
from db_utils import *
from analyzer import *
# from bisect_utils import *

def import_database(other_server):
    other_db_path = "data/mariposa2.db"
    os.system(f"rm {other_db_path}")
    os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {other_db_path}")
    import_tables(other_db_path)

def clean_queries(cfg):
    from clean_utils import clean_dfy_project
    from clean_utils import clean_fs_project
    clean_dfy_project(cfg, cfg.clean_dirs[Z3_4_11_2])

def sample_projects(projects):
    for proj in projects:
        print(proj)

# from datetime import datetime

# def get_runtime():
#     con, cur = get_cursor()
#     total = 0
#     for cfg in ALL_CFGS:
#         for solver in cfg.samples:
#             solver_table = cfg.qcfg.get_solver_table_name(solver)
#             res = cur.execute(f"""
#                 SELECT SUM(elapsed_milli)
#                 FROM {solver_table}""")
#             time = res.fetchone()[0] / 1000 / 3600
#             # start, end = res.fetchone()
#             # date from string 
#             # start = datetime.strptime(start, '%Y-%m-%d %H:%M:%S')
#             # end = datetime.strptime(end, '%Y-%m-%d %H:%M:%S')
#             # diff = end - start
#             # convert into hours
#             total += time
#             print(cfg.qcfg.name, solver, time)
#     print(total)
#             # diff = diff.total_seconds() / 3600
#             # print(cfg.qcfg.name, solver, round(diff, 2))
#         # print(solver_df["time"].mean())
#     # solver_table = cfg.qcfg.get_solver_table_name(solver)

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
    
#   for unsat_core in UNSAT_CORE_CFGS:
#       print(unsat_core.name)
#       if unsat_core.name != "D_KOMODO_Z3_UNSAT_CORE":
#           continue
#       r = Runner([unsat_core], override=True, core=True)
    
#   for min_asserts in MIN_ASSERTS_CFGS:
#       print(min_asserts.name)
#       if min_asserts.name != "D_LVBKV_Z3_MIN_ASSERTS":
#           continue
#       r = Runner([min_asserts], override=True)


#   r = Runner([D_KOMODO_UNSAT_CORE_CFG], override=True, core=True)
#   r = Runner([D_KOMODO_MIN_ASSERTS_CFG], override=True)
#   build_solver_summary_table(D_KOMODO_UNSAT_CORE_CFG, Z3_4_12_1)

    # parse_bisect()
    
    # create_benchmark()

    # locality_analysis(cfg)

    # plot_paper_overall()
    # plot_paper_ext_cutoff()
    # plot_paper_pert_diff()
    # plot_paper_time_std()
    # plot_paper_time_scatter()

    # plot_appendix_ext_cutoff()
    # plot_appendix_pert_diff()
    # plot_appendix_time_std()
    # plot_appendix_time_scatter()
    # plot_appendix_sizes()
    # plot_appendix_srs()

    # cfg = D_FVBKV_CFG
    # plot_ext_cutoff(cfg)
    
    # project = ProjectConfig("core_benchmark_unstable", FrameworkName.DAFNY, Z3_4_12_1)
    # cfg = ExpConfig("core_benchmark_test", project, [Z3_4_12_1], "data/benchmarks.db")

    # r = Runner([cfg])

#   plot_size_reduction_graph()
#   plot_time_reduction_graph()                                                                                                                                                                                                 
#   plot_time_reduction_graph_zoomed()
#   plot_size_vs_time_correlations()
    plot_pie_chart()
#   generate_table()
