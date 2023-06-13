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
#             solver_table = cfg.qcfg.get_solver_ORIGINAL_CFGStable_name(solver)
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
#       if unsat_core.name != "D_LVBKV_Z3_UNSAT_CORE":
#           continue
#       r = Runner([unsat_core], override=True, core=True)
    
#   for min_asserts in MIN_ASSERTS_CFGS:
#       print(min_asserts.name)
#       if min_asserts.name != "D_LVBKV_Z3_MIN_ASSERTS":
#           continue
#       r = Runner([min_asserts], override=True)

#   print(f"""rule move
#            command = cp $in $out
#   """)

#   ## create pairs of original and unsat core queries
#   for project in PROJECTS:
#       # query mariposa database for all unsat queries
#       original_con, original_cur = get_cursor("data/mariposa.db")
#       unsat_con, unsat_cur = get_cursor("data/unsat_core.db")
#       project_name_caps = ""
#       if "_z3" in project.name:
#           project_name_caps = project.name[:-3].upper()
#       else:
#           project_name_caps = project.name.upper()
#       project_name = project_name_caps.lower()
#       original_table_name = f"{project_name_caps}_z3_4_8_5"
#       inst_table_name = f"{project.name.upper()}_UNSAT_CORE_z3_4_8_5"
#       unsat_core_table_name = f"{project.name.upper()}_MIN_ASSERTS_z3_4_8_5"

#       print(original_table_name)
#       print(inst_table_name)
#       print(unsat_core_table_name)

#       num_original_queries = original_cur.execute(f"""
#           SELECT count(*) FROM {original_table_name} WHERE query_path like 'data%' """)
#       print("number of original queries: ", num_original_queries.fetchall())

#       num_inst_queries = unsat_cur.execute(f"""
#           SELECT count(*) FROM {inst_table_name} """)
#       print("number of inst queries: ", num_inst_queries.fetchall())

#       unsat_inst_queries = unsat_cur.execute(f"""
#           SELECT count(*) FROM {inst_table_name} WHERE result_code = 'unsat' """)
#       print("number of unsat inst queries: ", unsat_inst_queries.fetchall())

#       unsat_unsat_core_queries = unsat_cur.execute(f"""
#           SELECT count(*) FROM {unsat_core_table_name} WHERE result_code = 'unsat' """)
#       print("number of unsat unsat core queries: ", unsat_unsat_core_queries.fetchall())

#       if project.name != "s_komodo":
#           continue

        # loop over all unsat unsat core queries and find the corresponding original query
#       unsat_unsat_core_queries = unsat_cur.execute(f"""
#           SELECT query_path FROM {unsat_core_table_name} WHERE result_code = 'unsat' """)
#       unsat_unsat_core_queries = unsat_unsat_core_queries.fetchall()
#       print(unsat_unsat_core_queries)

        
#       for unsatcore_path in unsat_unsat_core_queries:
#           unsatcore_path = unsatcore_path[0]
#           query_name = unsatcore_path.split("/")[-1]
#           print(unsatcore_path)

#           original_query_path = f"/home/yizhou7/mariposa/data/{project.name}_clean/{query_name}"
#           print(original_query_path)
#           print(f"build data/unsat_pairs/original/{project_name}/{query_name} : move {original_query_path}")
#           print(f"build data/unsat_pairs/unsat_core/{project_name}/{query_name} : move {unsatcore_path}")

#           os.system(f"mkdir -p data/unsat_pairs/original/{project_name}")
#           os.system(f"mkdir -p data/unsat_pairs/unsat_core/{project_name}")
#           os.system(f"cp {original_query_path} data/unsat_pairs/original/{project_name}")
#           os.system(f"cp {unsatcore_path} data/unsat_pairs/unsat_core/{project_name}")
    
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
#   plot_pie_chart()
#   plot_pie_chart_plotly()
    plot_size_vs_time_regression()
    plot_size_vs_time_regression_unsat_core()
