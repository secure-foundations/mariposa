from project import *
from experiment import *
from runner import *
from db_utils import *
from analysis_utils import *
import shutil
from basic_utils import *
# from bisect_utils import *
import argparse
from tabulate import tabulate

def import_database(other_server):
    other_db_path = "data/mariposa2.db"
    os.system(f"rm {other_db_path}")
    os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {other_db_path}")
    import_tables(other_db_path)

def plot_paper_figs():
    plot_paper_overall()
    plot_paper_ext_cutoff()
    plot_paper_pert_diff()
    plot_paper_time_std()
    plot_paper_time_scatter()

def plot_appendix_figs():
    plot_appendix_ext_cutoff()
    plot_appendix_pert_diff()
    plot_appendix_time_std()
    plot_appendix_time_scatter()
    plot_appendix_sizes()
    plot_appendix_srs()

# def load_config(config_path):
#     cfg = ExpConfig()
#     config = json.loads(open(config_path, "r").read())
#     cfg.load(config)
#     ana = Analyzer("z_test")
#     ana.load(config)
#     return cfg, ana

def create_single_mode_project(args):
    origin_path = args.query
    query_name = os.path.basename(origin_path)
    exit_with_on_fail(query_name.endswith(".smt2"), '[ERROR] query must end with ".smt2"')
    query_name.replace(".smt2", "")
    solver = solver_from_path(args.solver)
    gen_split_subdir = f"gen/{query_name}_"
    project = ProjectInfo("misc", gen_split_subdir, solver)
    return project

def dump_status(project, solver, cfg, ana):
    rows = load_sum_table(project, solver, cfg)
    # print("solver:", solver.path)
    print("solver:", solver.path)
    print("")

    for row in rows:
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

def single_mode(args):
    cfg, ana = load_known_experiment(args.config)
    project = create_single_mode_project(args)

    if cfg.db_path == "":
        cfg.db_path = f"{project.clean_dir}/test.db"

    print(f"[INFO] single mode will use db {cfg.db_path}")

    if args.clear:
        os.system(f"rm -rf gen/*")
        print("[INFO] cleared all data from past experiments")

    dir_exists = os.path.exists(project.clean_dir)

    if args.analysis_only:
        exit_with_on_fail(dir_exists, f"[ERROR] experiment dir {project.clean_dir} does not exist")
    else:
        if dir_exists:
            print(f"[INFO] experiment dir {project.clean_dir} exists, remove it? [Y]")
            exit_with_on_fail(input() == "Y", f"[INFO] aborting")
            shutil.rmtree(project.clean_dir, ignore_errors=True)
        os.makedirs(project.clean_dir)

        command = f"./target/release/mariposa -i {args.query} --chop --o {project.clean_dir}/split.smt2"
        print(command)
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] split failed")

        r = Runner(cfg)
        r.run_project_exps(project, project.artifact_solver)

    dump_status(project, project.artifact_solver, cfg, ana)

def multi_mode(args):
    cfg, ana = load_known_experiment(args.config)

    try:
        project = eval(args.project)
        assert isinstance(project, ProjectInfo)
    except:
        exit_with(f"[ERROR] not an existing project {args.project}")

    solver = solver_from_path(args.solver)

    if not args.analysis_only:
        check_existing_tables(cfg, project, solver)
        r = Runner(cfg)
        r.run_project_exps(project, solver)

    rows = load_sum_table(project, solver, cfg=cfg)
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)

    pp_table = [["category", "count", "percentage"]]
    for cat in {Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE}:
        pp_table.append([cat.value, len(items[cat]), ps[cat]])

    print(tabulate(pp_table, tablefmt="simple_grid"))

def flatten_path(base_dir, path):
    assert base_dir in path
    if not base_dir.endswith("/"):
        base_dir += "/"
    rest = path[len(base_dir):]
    rest = rest.replace("/", "-")
    return base_dir + rest

def convert_path(src_path, src_dir, dst_dir):
    dst_path = flatten_path(src_dir, src_path)
    dst_path = dst_path.replace(src_dir, dst_dir)
    return dst_path

def preprocess_mode(args):
    queries = list_smt2_files(args.in_dir)
    exit_with_on_fail(not os.path.exists(args.out_dir), f"[ERROR] output directory {args.out_dir} exists")
    os.makedirs(args.out_dir)

    print(f'[INFO] found {len(queries)} files with ".smt2" extension under {args.in_dir}')
    for in_path in queries:
        out_path = convert_path(in_path, args.in_dir, args.out_dir)
        command = f"./target/release/mariposa -i {in_path} --chop --o {out_path}"
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] query split failed")
    queries = list_smt2_files(args.out_dir)
    print(f'[INFO] generated {len(queries)} split queries under {args.out_dir}')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    single_parser = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')

    single_parser.add_argument("-q", "--query", required=True, help="the input query")
    single_parser.add_argument("--clear", default=False, action='store_true', help="clear past data from single mode experiments")

    single_parser.add_argument("--config", default="single", help="the configuration name in configs/experiments.json")

    multi_parser = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver. the project is specified by a python expression that evaluates to a ProjectInfo object. ')
    multi_parser.add_argument("-p", "--project", required=True, help="the project to run mariposa on")
    multi_parser.add_argument("--config", required=True, help="the configuration file")

    for sp in [single_parser, multi_parser]:
        sp.add_argument("-s", "--solver", required=True, help="the solver to use")
        sp.add_argument("--analysis-only", default=False, action='store_true', help="do not perform experiments, only analyze existing data")

    preprocess_parser = subparsers.add_parser('preprocess', help='preprocess mode. (recursively) traverse the input directory and split all queries with ".smt2" file extension, the split queries will be stored under the output directory.')
    preprocess_parser.add_argument("--in-dir", required=True, help='the input directory with ".smt2" files')
    preprocess_parser.add_argument("--out-dir", required=True, help="the output directory to store preprocessed files, flattened and split")

    args = parser.parse_args()

    if args.sub_command == "preprocess":
        preprocess_mode(args)
    elif args.sub_command == "single":
        single_mode(args)
    elif args.sub_command == "multiple":
        multi_mode(args)
