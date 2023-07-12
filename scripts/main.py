from runner import *
from db_utils import *
# from bisect_utils import *
# from analysis_utils import *
import shutil
from basic_utils import *
import argparse
from tabulate import tabulate
from configer import *

# def import_database(other_server):
#     remote_db_path = "data/mariposa2.db"
#     os.system(f"rm {remote_db_path}")
#     os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {remote_db_path}")
#     import_tables(remote_db_path)

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

        command = f"./target/release/mariposa -i '{args.query}' --chop --o '{project.clean_dir}/split.smt2'"
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] split failed")

        r = Runner(exp)
        r.run_project(project, project.artifact_solver, 1, 1)
    dump_status(project, project.artifact_solver, exp, ana)

def dump_multi_status(project, solver, exp, ana):
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

def parse_partition(partition):
    import re
    pattern = re.compile(r"(\d+)/(\d+)")
    match = re.match(pattern, partition)
    exit_with_on_fail(match is not None, f"[ERROR] invalid partition {partition}")
    return int(match.group(1)), int(match.group(2))

def multi_mode(args):
    part_id, part_num = parse_partition(args.partition_id)

    c = Configer()
    exp = c.load_known_experiment(args.experiment)
    solver = c.load_known_solver(args.solver)
    project = c.load_known_project(args.project)
    ana = c.load_known_analyzer(args.analyzer)

    if not args.analysis_only:
        check_existing_tables(exp, project, solver, part_id, part_num)
        r = Runner(exp)
        r.run_project(project, solver, part_id, part_num)

    if not args.analysis_skip:
        dump_multi_status(project, solver, exp, ana)
    else:
        print("[INFO] skipping analysis")

    return (exp.db_path, part_id, part_num)

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
        if not args.out_dir.endswith("/"):
            args.out_dir += "/"
        out_path = convert_path(in_path, args.in_dir, args.out_dir)
        command = f"./target/release/mariposa -i '{in_path}' --chop --o '{out_path}'"
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] query split failed")
    queries = list_smt2_files(args.out_dir)
    print(f'[INFO] generated {len(queries)} split queries under {args.out_dir}')

import copy 

def get_self_ip():
    import socket
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect(("8.8.8.8", 80))
    addr = s.getsockname()[0]
    s.close()
    return addr

def start_server(args):
    from multiprocessing.managers import BaseManager
    m = BaseManager(address=('0.0.0.0', 50000), authkey=args.authkey.encode('utf-8'))
    s = m.get_server()
    s.serve_forever()

def manager_mode(args):
    c = Configer()
    exp = c.load_known_experiment(args.experiment)
    solver = c.load_known_solver(args.solver)
    project = c.load_known_project(args.project)
    check_existing_tables(exp, project, solver, 1, 1)

    from multiprocessing.managers import BaseManager
    from multiprocessing import process
    import threading
    import multiprocessing
    
    job_queue = multiprocessing.Queue()
    res_queue = multiprocessing.Queue()

    for i in range(1, args.partition_num + 1):
        wargs = copy.deepcopy(args)
        wargs.partition_id = f"{i}/{args.partition_num}"
        wargs.analysis_skip = True
        job_queue.put(wargs)

    # NOTE: we assume number of workers is less than number of partitions
    for i in range(args.partition_num):
        job_queue.put(None)

    BaseManager.register('get_job_queue', callable=lambda:job_queue)
    BaseManager.register('get_res_queue', callable=lambda:res_queue)

    addr = get_self_ip()

    st = threading.Thread(target=start_server, args=[args])
    st.setDaemon(True)
    st.start()

    print("[INFO] starting manager, run the following command on workers:")
    print(f"python3 scripts/main.py worker --manager-addr {addr} --authkey {args.authkey}")

    # exit when expected number of results are collected
    while res_queue.qsize() != args.partition_num:
        time.sleep(10)
        print(f"[INFO] {res_queue.qsize()}/{args.partition_num} partition message(s) received")

    workers = dict()
    for i in range(args.partition_num):
        (remote_db_path, part_id, part_num) = res_queue.get()
        if addr in remote_db_path:
            continue
        if remote_db_path not in workers:
            workers[remote_db_path] = []
        workers[remote_db_path].append((part_id, part_num))
    print("[DEBUG] ", workers)

    for remote_db_path in workers:
        temp_db_path = f"{exp.db_path}.temp"
        command = f"scp -r {remote_db_path} {temp_db_path}"
        print(f"[INFO] copying db: {command}")
        os.system(command)
        assert os.path.exists(temp_db_path)
        for (part_id, part_num) in workers[remote_db_path]:
            print(f"[INFO] importing partition {part_id}/{part_num} from {remote_db_path}")
            import_entries(exp.db_path, temp_db_path, exp, project, solver, part_id, part_num)
        os.remove(temp_db_path)

def worker_mode(args):
    from multiprocessing.managers import BaseManager
    import os.path

    BaseManager.register('get_job_queue')
    BaseManager.register('get_res_queue')
    m = BaseManager(address=(args.manager_addr, 50000), authkey=args.authkey.encode('utf-8'))
    m.connect()
    queue = m.get_job_queue()
    res_queue = m.get_res_queue()

    while queue.qsize() > 0:
        wargs = queue.get()
        if wargs is None:
            break
        (db_path, part_id, part_num) = multi_mode(wargs)
        db_path = f"{get_self_ip()}:{os.path.abspath(db_path)}"
        res_queue.put((db_path, part_id, part_num))
        print(f"[INFO] worker {get_self_ip()} completed partition {part_id}th out of {part_num}")
    print(f"[INFO] worker {get_self_ip()} finished")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    single_parser = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')

    single_parser.add_argument("-q", "--query", required=True, help="the input query")
    single_parser.add_argument("--clear", default=False, action='store_true', help="clear past data from single mode experiments")
    single_parser.add_argument("-e", "--experiment", default="single", help="the experiment configuration name in configs.json")

    multi_parser = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver. the project is specified by a python expression that evaluates to a ProjectInfo object. ')

    multi_parser.add_argument("--partition-id", default="1/1", help="which partition of the project to run mariposa on (probably should not be specified manually)")
    
    manager_parser = subparsers.add_parser('manager', help='sever pool manager mode.')
    manager_parser.add_argument("--partition-num", type=int, required=True, help="number of partitions to split the project into")

    for sp in [multi_parser, manager_parser]:
        sp.add_argument("-p", "--project", required=True, help="the project name (from configs.json) to run mariposa on")
        sp.add_argument("-e", "--experiment", required=True, help="the experiment configuration name (from configs.json)")

    for sp in [single_parser, multi_parser, manager_parser]:
        sp.add_argument("-s", "--solver", required=True, help="the solver name (from configs.json) to use")
        sp.add_argument("--analysis-only", default=False, action='store_true', help="do not perform experiments, only analyze existing data")
        sp.add_argument("--analysis-skip", default=False, action='store_true', help="skip analysis")
        sp.add_argument("--analyzer", default="default", help="the analyzer name (from configs.json) to use")

    worker_parser = subparsers.add_parser('worker', help='sever pool worker mode.')
    worker_parser.add_argument("--manager-addr", required=True, help="the manager address for the server pool")

    for sp in [worker_parser, manager_parser]:
        sp.add_argument("--authkey", required=True, help="the authkey to use for the server pool")

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
    elif args.sub_command == "manager":
        manager_mode(args)
    elif args.sub_command == "worker":
        worker_mode(args)
    elif args.sub_command is None:
        parser.print_help()
