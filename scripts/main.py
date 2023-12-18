from runner import *
# from bisect_utils import *
# from analysis_utils import *
import shutil, argparse
from exp_manager import *
from project_manager import *
from tabulate import tabulate
from solver_info import *

# def import_database(other_server):
#     remote_db_path = "data/mariposa2.db"
#     os.system(f"rm {remote_db_path}")
#     os.system(f"scp {other_server}:/home/yizhou7/mariposa/data/mariposa.db {remote_db_path}")
#     import_tables(remote_db_path)

def single_mode(args):
    exp = ExpPart.single_mode_exp(args.query, args.solver)

    proj_root = exp.proj.root_dir
    dir_exists = os.path.exists(proj_root)

    if args.analysis_only:
        exit_with_on_fail(dir_exists, f"[ERROR] experiment dir {proj_root} does not exist")
    else:
        if dir_exists:
            if args.clear:
                print(f"[INFO] experiment dir {proj_root} exists, removing")
                shutil.rmtree(proj_root, ignore_errors=True)
            else:
                print(f"[ERROR] experiment dir {proj_root} exists, aborting")
                return 
        os.makedirs(proj_root)

        command = f"./target/release/mariposa -i '{args.query}' --chop -o '{proj_root}/split.smt2'"
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
        print(result.stdout.decode('utf-8'), end="")
        exit_with_on_fail(result.returncode == 0, "[ERROR] split failed")

        r = Runner()
        r.run_project(exp)

    exp.dump_status()

# def dump_multi_status(project, solver, exp, ana):
#     rows = load_sum_table(project, solver, cfg=exp)
#     items = ana.categorize_queries(rows)
#     ps, _ = get_category_percentages(items)

#     print("project directory:", project.clean_dir)
#     print("solver used:", solver.path)
#     print("total queries:", len(rows))

#     pp_table = [["category", "count", "percentage"]]
#     for cat in [Stability.STABLE, Stability.INCONCLUSIVE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
#         pp_table.append([cat.value, len(items[cat]), round(ps[cat], 2)])

#     print(tabulate(pp_table, tablefmt="github"))
#     print("")
#     print("listing unstable queries...")

#     for row in rows:
#         query = row[0]
#         if query not in items[Stability.UNSTABLE]:
#             continue
#         print("")
#         print("query:", row[0])
#         mutations, blob = row[1], row[2]
#         ana.dump_query_status(mutations, blob)

def multi_mode(args):
    exp = ExpPart(args.experiment, 
            args.project, 
            args.solver, 
            args.part)

    if not args.analysis_only:
        r = Runner()
        r.run_project(exp)

    exp.dump_status()

    return (exp.db_path, args.part)

def preprocess_mode(args):
    if os.path.exists(args.out_dir):
        print(f"[WARN] output directory {args.out_dir} already exists, remove it? [Y]")
        exit_with_on_fail(input() == "Y", f"[INFO] aborting")
        shutil.rmtree(args.out_dir)
    os.makedirs(args.out_dir)

    queries = list_smt2_files(args.in_dir)
    print(f'[INFO] found {len(queries)} files with ".smt2" extension under {args.in_dir}')

    temp = open("preprocess.sh", "w+")
    for in_path in queries:
        out_path = convert_path(in_path, args.in_dir, args.out_dir)
        command = f"./target/release/mariposa -i '{in_path}' --chop --remove-debug -o '{out_path}'\n"
        temp.write(command)
    temp.close()
    print(f"[INFO] emitted to preprocess.sh, running using gnu parallel")
    os.system("cat preprocess.sh | parallel")
    os.system("rm preprocess.sh")

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
    exp = ExpPart(args.experiment, 
            args.project,
            args.solver, Partition(1, 1))

    from multiprocessing.managers import BaseManager
    # from multiprocessing import process
    import threading
    import multiprocessing
    
    job_queue = multiprocessing.Queue()
    res_queue = multiprocessing.Queue()

    for i in range(1, args.total_parts + 1):
        wargs = copy.deepcopy(args)
        wargs.partition_id = f"{i}/{args.total_parts}"
        # wargs.analysis_skip = True
        job_queue.put(wargs)

    # NOTE: we assume number of workers is less than number of partitions
    for i in range(args.total_parts):
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
    while res_queue.qsize() != args.total_parts:
        time.sleep(10)
        print(f"[INFO] {res_queue.qsize()}/{args.total_parts} partition message(s) received")

    workers = dict()

    for i in range(args.total_parts):
        (remote_db_path, part) = res_queue.get()
        if addr in remote_db_path:
            continue
        if remote_db_path not in workers:
            workers[remote_db_path] = []
        workers[remote_db_path].append(part)

    for remote_db_path in workers:
        temp_db_path = f"{exp.db_path}.temp"
        command = f"scp -r {remote_db_path} {temp_db_path}"
        print(f"[INFO] copying db: {command}")
        os.system(command)
        assert os.path.exists(temp_db_path)
        for part in workers[remote_db_path]:
            print(f"[INFO] importing {part} from {remote_db_path}")
            exp.import_tables(temp_db_path, temp_db_path, part)
        os.remove(temp_db_path)

# def recovery_mode(args):
#     #  -s z3_4_12_2 -p d_komodo_uc_trigger_10 -e min_asserts
#     c = Configer()
#     exp = c.load_known_experiment(args.experiment)
#     solver = c.load_known_solver(args.solver)
#     project = c.load_known_project(args.project)

#     for i in {1, 2 , 5, 6, 7, 8}:
#         temp_db_path = f"{exp.db_path}.{i}.temp"
#         remote_db_path = f"s190{i}:~/mariposa/{exp.db_path}"
#         if os.path.exists(temp_db_path):
#             continue
#         command = f"scp {remote_db_path} {temp_db_path}"
#         print(f"[INFO] copying db: {command}")
#         os.system(command)
#         assert os.path.exists(temp_db_path)
    
#     exp_tname = exp.get_exp_tname(project, solver)
#     sum_tname = exp.get_sum_tname(project, solver)

#     import re
#     pattern = re.compile(r"p(\d+)of(\d+)")
#     part_num = None
    
#     imports = dict()
#     finished = set()

#     for i in {1, 2 , 5, 6, 7, 8}:
#         temp_db_path = f"{exp.db_path}.{i}.temp"
#         print(f"[INFO] copying db {temp_db_path}")
#         tables = get_tables(temp_db_path)
#         imports[temp_db_path] = []
#         for table in tables:
#             if table.startswith(exp_tname + "_"):
#                 partition = table[len(exp_tname) + 1:]
#                 match = re.match(pattern, partition)
#                 assert part_num is None or part_num == int(match.group(2))
#                 part_num = int(match.group(2))
#                 part_id = int(match.group(1))
#                 if part_id in finished:
#                     print("[INFO] ignored duplicated part {part_id}")
#                     continue
#                 finished.add(part_id)
#                 imports[temp_db_path].append((part_id, part_num))
#     excepted = set(range(1, part_num + 1))

#     if finished != excepted:
#         print("[WARN] some partitions are missing, aborting", excepted - finished)
#         return

#     for temp_db_path in imports:
#         for (part_id, part_num) in imports[temp_db_path]:
#             print(f"[INFO] importing partition {part_id}/{part_num} from {temp_db_path}")
#             import_entries(exp.db_path, temp_db_path, exp, project, solver, part_id, part_num)

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
        (db_path, part) = multi_mode(wargs)
        db_path = f"{get_self_ip()}:{os.path.abspath(db_path)}"
        res_queue.put((db_path, part))
        print(f"[INFO] worker {get_self_ip()} completed {part}")
    print(f"[INFO] worker {get_self_ip()} finished")

# def update_mode(args):
#     c = Configer()
#     exp = c.load_known_experiment(args.experiment)
#     solver = c.load_known_solver(args.solver)
#     project = c.load_known_project(args.project)

#     sanity = args.query.startswith(project.clean_dir)
#     message = f"[ERROR] query {args.query} does not belong to project {project.clean_dir}"
#     exit_with_on_fail(sanity, message)
#     r = Runner(exp)
#     r.update_project(project, solver, args.query)

def load_project(project_name):
    m = ProjectManager()
    return m.load_project(project_name)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="mariposa is a tool for testing SMT proof stability")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    update_parser = subparsers.add_parser('update', help='update mode. update an existing experiment by (adding) a single query.')
    single_parser = subparsers.add_parser('single', help='single query mode. run mariposa on a single query with ".smt2" file extension, which will be split into multiple ".smt2" files based on check-sat(s), the split queries will be stored under the "gen/" directory and tested using the specified solver.')

    for sp in [update_parser, single_parser]:
        sp.add_argument("-q", "--query", required=True, help="the input query")

    single_parser.add_argument("--clear", default=False, action='store_true', help="clear past data from single mode experiments")
    single_parser.add_argument("-e", "--experiment", default="single", help="the experiment configuration name in configs.json")

    multi_parser = subparsers.add_parser('multiple', help='multiple query mode. test an existing (preprocessed) project using the specified solver. the project is specified by a python expression that evaluates to a ProjectInfo object. ')

    multi_parser.add_argument("--part", default="1/1", help="which part of the project to run mariposa on (probably should not be specified manually)")

    manager_parser = subparsers.add_parser('manager', help='sever pool manager mode.')
    manager_parser.add_argument("--total-parts", type=int, required=True, help="number of parts to split the project into")

    recovery_parser = subparsers.add_parser('recovery', help='recovery mode. recover the database from a crashed run (do not use unless on s190x cluster).')

    for sp in [multi_parser, manager_parser, recovery_parser, update_parser]:
        sp.add_argument("-p", "--project", required=True, help="the project name (from configs.json) to run mariposa on")
        sp.add_argument("-e", "--experiment", required=True, help="the experiment configuration name (from configs.json)")

    for sp in [single_parser, multi_parser, manager_parser, recovery_parser, update_parser]:
        sp.add_argument("-s", "--solver", required=True, help="the solver name (from configs.json) to use")
        if sp == recovery_parser:
            continue
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

    preprocess_parser.add_argument("--clean-debug", required=False, help="if queries fail during the verification process, remove the debug queries that arise during error localization", action='store_true')

    args = parser.parse_args()

    if hasattr(args, "solver"):
        args.solver = SolverInfo(args.solver)
    if hasattr(args, "part"):
        args.part = Partition.from_str(args.part)
    if hasattr(args, "project"):
        args.project = load_project(args.project)

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
    elif args.sub_command == "recovery":
        recovery_mode(args)
    elif args.sub_command == "update":
        update_mode(args)
    elif args.sub_command is None:
        parser.print_help()

# c = Configer()
# p = c.load_known_project("d_fvbkv")
# print(len(p.list_queries(200, 200)))