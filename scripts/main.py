from runner import *
from db_utils import *
# from analysis_utils import *
import shutil
from basic_utils import *
import argparse
from tabulate import tabulate
from configer import *

# def import_database(other_server):
#     other_db_path = "data/mariposa2.db"
#     os.system(f"rm {other_db_path}")
#     os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {other_db_path}")
#     import_tables(other_db_path)

def create_single_mode_project(args, solver):
    origin_path = args.query
    query_name = os.path.basename(origin_path)
    exit_with_on_fail(query_name.endswith(".smt2"), '[ERROR] query must end with ".smt2"')
    query_name.replace(".smt2", "")
    gen_split_subdir = f"gen/{query_name}_"
    project = ProjectInfo("misc", gen_split_subdir, solver)
    return project

def dump_status(project, solver, cfg, ana):
    rows = load_sum_table(project, solver, cfg)
    # print("solver:", solver.path)
    print("solver used:", solver.path)

    for row in rows:
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

def single_mode(args):
    c = Configer()
    exp = c.load_known_experiment(args.experiment)
    solver = c.load_known_solver(args.solver)
    project = create_single_mode_project(args, solver)
    ana = c.load_known_analyzer(args.analyzer)

    if exp.db_path == "":
        exp.db_path = f"{project.clean_dir}/test.db"

    print(f"[INFO] single mode will use db {exp.db_path}")

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
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] split failed")

        r = Runner(exp)
        r.run_single_project(project, project.artifact_solver)

    dump_status(project, project.artifact_solver, exp, ana)

def multi_mode(args):
    c = Configer()
    exp = c.load_known_experiment(args.experiment)
    solver = c.load_known_solver(args.solver)
    project = c.load_known_project(args.project)
    ana = c.load_known_analyzer(args.analyzer)

    if not args.analysis_only:
        check_existing_tables(exp, project, solver)
        r = Runner(exp)
        r.run_single_project(project, solver)

    rows = load_sum_table(project, solver, cfg=exp)
    items = ana.categorize_queries(rows)
    ps, _ = get_category_percentages(items)

    print("project directory:", project.clean_dir)
    print("solver used:", solver.path)
    print("total queries:", len(rows))

    pp_table = [["category", "count", "percentage"]]
    for cat in {Stability.UNSOLVABLE, Stability.UNSTABLE, Stability.INCONCLUSIVE, Stability.STABLE}:
        pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])

    print(tabulate(pp_table, tablefmt="github"))
    print("")
    print("listing unstable queries...")

    for row in rows:
        query = row[0]
        if query not in items[Stability.UNSTABLE]:
            continue
        print("")
        print("query:", row[0])
        mutations, blob = row[1], row[2]
        ana.dump_query_status(mutations, blob)

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
    single_parser.add_argument("-e", "--experiment", default="single", help="the experiment configuration name in configs.json")

    multi_parser = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver. the project is specified by a python expression that evaluates to a ProjectInfo object. ')
    multi_parser.add_argument("-p", "--project", required=True, help="the project name (from configs.json) to run mariposa on")
    multi_parser.add_argument("-e", "--experiment", required=True, help="the experiment configuration name (from configs.json)")

    for sp in [single_parser, multi_parser]:
        sp.add_argument("-s", "--solver", required=True, help="the solver name (from configs.json) to use")
        sp.add_argument("--analysis-only", default=False, action='store_true', help="do not perform experiments, only analyze existing data")
        sp.add_argument("--analyzer", default="default", help="the analyzer name (from configs.json) to use")

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
