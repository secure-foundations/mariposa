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

def get_diff_mutants():
    f = open("unstable.list")
    cfg = D_KOMODO_CFG
    for l in f.readlines():
        l = l.strip()


if __name__ == '__main__':
    print("building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD", 0)
    # assert stdout == "master"
    os.system("cargo build --release")

    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq", 0)
    assert stdout == "performance"

    # entropy_test()
    # create_benchmark()
    # create_benchmark()
    # v_test()
    # dump_all()

    # cfg = D_KOMODO_CFG
    # plot_ext_cutoff(cfg)
    # plot_time_std(cfg)
    # plot_pert_diff(cfg)
    # plot_sr_cdf(cfg)
    # plot_vbkv_ext_cutoff()

    # plot_pert_diff(D_LVBKV_CFG)
    # plot_pert_diff(D_FVBKV_CFG)
    # plot_pert_diff(FS_DICE_CFG)

    # plot_query_sizes(ALL_CFGS)
    # compare_vbkvs(D_LVBKV_CFG, D_FVBKV_CFG)

    # export_timeouts(D_LVBKV_CFG, Z3_4_12_1)

    # cfg = ExpConfig("FS_DICE", FS_DICE, [Z3_4_12_1], DB_PATH)
    
    # for cfg in [D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG]:
    #     summaries = load_solver_summaries(cfg, skip_unknowns=False)
    #     th = Thresholds("strict")
    #     th.timeout = 6e4
    #     categories1 = categorize_qeuries(summaries[Z3_4_8_5], th)
    #     categories2 = categorize_qeuries(summaries[Z3_4_8_8], th)

    #     stable_1 = categories1[Stablity.STABLE.value]
    #     stable_2 = categories2[Stablity.STABLE.value]

    #     unstable_1 = categories1[Stablity.RES_UNSTABLE]
    #     unstable_2 = categories2[Stablity.RES_UNSTABLE]
        
    #     # print(len(unstable_1.intersection(stable_2)))
    #     for i in stable_1.intersection(unstable_2):
    #         print(i)
        
    # diff = categories2[Stablity.RES_UNSTABLE.value] - categories1[Stablity.RES_UNSTABLE.value]
    # diff2 = categories1[Stablity.RES_UNSTABLE.value] - categories2[Stablity.RES_UNSTABLE.value]
        # print(len(diff), len(diff2))

    for cfg in [D_KOMODO_CFG, D_LVBKV_CFG, D_FVBKV_CFG, FS_DICE_CFG]:
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
            out_path_root = "data/bisect/" + p.replace("/", "--") + "/"
            os.system(f"mkdir -p {out_path_root}")
            print(f"cp {l} {out_path_root}original.smt2")
            for row in res.fetchall():
                mpath = row[0]
                assert mpath.find(p) != -1
                args = mpath.split(".")[-3:]
                assert args[-1] == "smt2"
                out_path = out_path_root + ".".join(args)
                command = f"./target/release/mariposa -i {l} -p {args[1]} -o {out_path} -s {args[0]}"
                print(command)

    # # get_diff_mutants()
    # for cfg in tqdm(ALL_CFGS):
    #     do_stuff(cfg)

    # plot_ext_cutoff(D_LVBKV_CFG)
    # import_database("s1905")

    # extend_solver_summary_table(D_LVBKV_CFG, D_LVBKV_TO_CFG, Z3_4_12_1)
    # build_solver_summary_table(S_CERTIKOS_CFG, Z3_4_12_1)
