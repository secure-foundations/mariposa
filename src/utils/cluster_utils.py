import copy
import os, subprocess, time
from analysis.basic_analyzer import BasicAnalyzer
from base.defs import CTRL_HOST, S190X_HOSTS, SYNC_ZIP
from base.exper import Experiment

from base.project import Partition
from utils.local_utils import handle_multiple
from utils.option_utils import deep_parse_args
from utils.system_utils import confirm_input, exit_with, get_file_count, is_flat_dir, log_check, log_info, log_warn, subprocess_run

def get_self_ip():
    import socket
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect(("8.8.8.8", 80))
    addr = s.getsockname()[0]
    s.close()
    return addr

def start_server(args):
    from multiprocessing.managers import BaseManager
    m = BaseManager(address=('0.0.0.0', 50000), 
                    authkey=args.authkey.encode('utf-8'))
    s = m.get_server()
    s.serve_forever()

def __spinoff_server(args):
    import threading

    st = threading.Thread(target=start_server, args=[args])
    st.setDaemon(True)
    st.start()
    
    addr = get_self_ip()

    log_info("starting manager, run the following command to start workers:")
    for host in S190X_HOSTS:
        if host == "s1904":
            continue
        remote_cmd = f"""ssh {host} "(cd mariposa; python3 src/exper_wizard.py worker --manager-addr {addr} --authkey {args.authkey}) &> mariposa.log &" """
        print(remote_cmd)

def handle_manager(args):
    # handle_sync(args.input_dir, args.clear)
    wargs = copy.deepcopy(args)
    args = deep_parse_args(args)
    exp = args.experiment
    exp.create_db(clear=args.clear_existing)

    from multiprocessing.managers import BaseManager
    import multiprocessing
    
    job_queue = multiprocessing.Queue()
    res_queue = multiprocessing.Queue()

    for i in range(args.total_parts):
        wargs = copy.deepcopy(wargs)
        wargs.part = str(Partition(i + 1, args.total_parts))
        job_queue.put(wargs)

    # NOTE: we assume number of workers is less than number of partitions
    for i in range(args.total_parts):
        job_queue.put(None)

    BaseManager.register('get_job_queue', callable=lambda:job_queue)
    BaseManager.register('get_res_queue', callable=lambda:res_queue)

    __spinoff_server(args)

    # exit when expected number of results are collected
    while res_queue.qsize() != args.total_parts:
        time.sleep(10)
        log_info(f"{res_queue.qsize()}/{args.total_parts} partition message(s) received")

    workers = dict()

    for i in range(args.total_parts):
        (remote_db_path, part) = res_queue.get()
        if remote_db_path not in workers:
            workers[remote_db_path] = []
        workers[remote_db_path].append(part)

    for remote_db_path in workers:
        temp_db_path = f"{exp.db_path}.temp"
        command = f"scp -r {remote_db_path} {temp_db_path}"
        log_info(f"copying db: {command}")
        os.system(command)
        log_check(os.path.exists(temp_db_path), f"failed to copy db {remote_db_path}!")
        for part in workers[remote_db_path]:
            log_info(f"importing {part} from {remote_db_path}")
            exp.import_partition_tables(temp_db_path, part)
        os.remove(temp_db_path)
    log_info(f"done importing")

    BasicAnalyzer(exp, args.analyzer).print_status(args.verbose)

def handle_worker(args):
    args = deep_parse_args(args)
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
        (db_path, part) = handle_multiple(wargs)
        db_path = f"{get_self_ip()}:{os.path.abspath(db_path)}"
        res_queue.put((db_path, part))
        log_info(f"worker {get_self_ip()} completed {part}")
    log_info(f"worker {get_self_ip()} finished")

def handle_recovery(args):
    args = deep_parse_args(args)
    exp: Experiment = args.experiment

    available_db_paths = []
    for host in S190X_HOSTS:
        if host == CTRL_HOST:
            continue
        temp_db_path = f"{exp.db_path}.{host}.temp"
        remote_db_path = f"{host}:~/mariposa/{exp.db_path}"

        if os.path.exists(temp_db_path):
            available_db_paths.append(temp_db_path)
            log_info(f"already has local db: {temp_db_path}")
            continue

        status = subprocess.call(['ssh', host, "test -f ~/mariposa/'{}'".format(exp.db_path)])

        if status == 0:
            command = f"scp {remote_db_path} {temp_db_path}"
            log_info(f"copying db: {command}")
            os.system(command)

        if not os.path.exists(temp_db_path):
            log_warn(f"failed to copy db {remote_db_path}, skipping")
        else:
            available_db_paths.append(temp_db_path)

    found_parts = set()

    for temp_db_path in available_db_paths:
        found_parts |= exp.probe_other_db(temp_db_path)

    part_nums = None
    found_ids = set()

    for part in found_parts:
        if part_nums is None:
            part_nums = part.num
        else:
            assert part_nums == part.num
        assert part.id not in found_ids
        found_ids.add(part.id)

    log_check(part_nums != None, "no partitions found, aborting")

    missing_count = 0

    for missing_id in set(range(1, part_nums + 1)) - found_ids:
        log_warn(f"partition {missing_id} is missing")
        missing_count += 1
    if missing_count > 0:
        log_warn(f"{missing_count} partitions missing, aborting")
        return

    exp.create_db(clear=True)

    for temp_db_path in available_db_paths:
        log_info(f"importing from {temp_db_path}")
        for part in exp.probe_other_db(temp_db_path):
            log_info(f"importing {part} from {temp_db_path}")
            exp.import_partition_tables(temp_db_path, part)

    log_info(f"done importing")

def run_command_over_ssh(host, cmd):
    print(f"running {cmd} on {host}")
    return subprocess_run(f"ssh {host} '{cmd}'", shell=True)

def handle_sync(input_dir, clear):
    log_check(is_flat_dir(input_dir), 
              f"{input_dir} is not a flat directory")
    file_count = get_file_count(input_dir)

    if os.path.exists(SYNC_ZIP):
        os.remove(SYNC_ZIP)

    cur_host = subprocess_run("hostname")[0]
    lines = []

    for host in S190X_HOSTS:
        if host == cur_host:
            continue

        # very basic check if file count matches
        r_std, r_err, _ = run_command_over_ssh(host, f"ls mariposa/{input_dir} | wc -l")
        if "No such file or directory" in r_err:
            lines.append(f"rcp {SYNC_ZIP} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {SYNC_ZIP} && rm {SYNC_ZIP}'")
            continue

        if clear:
            log_warn(f"force syncing on {host}")
            run_command_over_ssh(host, f"rm -r mariposa/{input_dir}")
            lines.append(f"rcp {SYNC_ZIP} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {SYNC_ZIP} && rm {SYNC_ZIP}'")
        else:
            if int(r_std) != file_count:
                exit_with(f"file count mismatch {host}")

    if len(lines) == 0:
        log_info(f"no sync required")
        return

    os.system(f"zip -r {SYNC_ZIP} {input_dir}")

    with open("sync.sh", "w") as f:
        f.write("#!/bin/bash\n")
        f.write("\n".join(lines))
        f.close()

    log_info(f"{len(lines)} commands written to sync.sh")
    confirm_input("run `cat sync.sh | parallel`?")
    os.system("cat sync.sh | parallel")

    confirm_input("remove temp files?")
    os.remove("sync.sh")
    os.remove(SYNC_ZIP)

def handle_update():
    print("run the following to update mariposa on all workers")
    for host in S190X_HOSTS:
        if host == "s1904":
            continue
        remote_cmd = f"""ssh {host} "(cd mariposa; rm -r data/dbs/ ; rm -r gen/ ; git checkout master; git pull; cd src/smt2action/; cargo build --release) &> /dev/null &" """
        print(remote_cmd)
