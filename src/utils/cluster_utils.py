import copy
import random
import os, subprocess, time
from base.defs import CTRL_HOST, S190X_HOSTS, SYNC_ZIP, get_worker_hosts
from base.exper import Experiment

from base.project import Partition
from base.exper_analyzer import ExperAnalyzer
from utils.local_utils import handle_multiple
from utils.option_utils import deep_parse_args
from utils.system_utils import (
    confirm_input,
    exit_with,
    get_file_count,
    is_flat_dir,
    log_check,
    log_info,
    log_warn,
    subprocess_run,
)


def get_self_ip():
    import socket

    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect(("8.8.8.8", 80))
    addr = s.getsockname()[0]
    s.close()
    return addr


def start_server(args):
    from multiprocessing.managers import BaseManager

    m = BaseManager(address=("0.0.0.0", 50000), authkey=args.authkey.encode("utf-8"))
    s = m.get_server()
    s.serve_forever()


def run_on_workers(cmd):
    hosts = get_worker_hosts()
    command = f'parallel-ssh -i -H "{hosts}" "{cmd}"'
    log_info(f"running {command} on workers")
    os.system(command)


def __spinoff_server(args):
    import threading

    st = threading.Thread(target=start_server, args=[args])
    st.setDaemon(True)
    st.start()

    addr = get_self_ip()

    log_info("manager initialized, starting workers:")
    for host in S190X_HOSTS:
        if host == "s1904":
            continue
        # this seems to work, so I am not using parallel-ssh
        remote_cmd = f"""ssh {host} "(cd mariposa; python3 src/exper_wizard.py worker --manager-addr {addr} --authkey {args.authkey}) &> log_mariposa &" """
        print(remote_cmd)
        os.system(remote_cmd)


def handle_manager(args, wargs):
    from binascii import hexlify

    branch = subprocess_run("git rev-parse --abbrev-ref HEAD", shell=True)[0]

    if branch != "master":
        confirm_input(f"manager is not on master branch, continue?")

    log_info(f"running data sync on {args.input_dir}")
    handle_data_sync(args.input_dir, True)

    authkey = hexlify(os.urandom(24)).decode("utf-8")
    # TODO: I forgot why we need to pass wargs
    wargs.authkey = authkey.encode("utf-8")
    args.authkey = authkey

    exp = args.experiment
    exp.create_db(clear=args.clear_existing)

    from multiprocessing.managers import BaseManager
    import multiprocessing

    job_queue = multiprocessing.Queue()
    res_queue = multiprocessing.Queue()

    for i in range(args.total_parts):
        wargs = copy.deepcopy(wargs)
        wargs.part = str(Partition(i + 1, args.total_parts))
        wargs.fix_missing = False
        job_queue.put(wargs)

    # NOTE: we assume number of workers is less than number of partitions
    for i in range(args.total_parts):
        job_queue.put(None)

    BaseManager.register("get_job_queue", callable=lambda: job_queue)
    BaseManager.register("get_res_queue", callable=lambda: res_queue)

    __spinoff_server(args)

    # exit when expected number of results are collected
    while res_queue.qsize() != args.total_parts:
        time.sleep(10)
        log_info(
            f"{res_queue.qsize()}/{args.total_parts} partition message(s) received"
        )

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

    ExperAnalyzer(exp, args.analyzer).print_status()


def handle_worker(args):
    from multiprocessing.managers import BaseManager
    import os.path

    BaseManager.register("get_job_queue")
    BaseManager.register("get_res_queue")
    m = BaseManager(
        address=(args.manager_addr, 50000), authkey=args.authkey.encode("utf-8")
    )
    m.connect()

    queue = m.get_job_queue()
    res_queue = m.get_res_queue()

    while queue.qsize() > 0:
        wargs = queue.get()
        if wargs is None:
            break
        wargs = deep_parse_args(wargs)
        (db_path, part) = handle_multiple(wargs)
        db_path = f"{get_self_ip()}:{os.path.abspath(db_path)}"
        res_queue.put((db_path, part))
        log_info(f"worker {get_self_ip()} completed {part}")
    log_info(f"worker {get_self_ip()} finished")


def handle_recovery(args):
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

        status = subprocess.call(
            ["ssh", host, "test -f ~/mariposa/'{}'".format(exp.db_path)]
        )

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


def handle_data_sync(input_dir, clear):
    file_count = get_file_count(input_dir)

    if os.path.exists(SYNC_ZIP):
        os.remove(SYNC_ZIP)

    cur_host = subprocess_run(["hostname"])[0]
    lines = []
    clear_on_match = None

    for host in S190X_HOSTS:
        if host == cur_host:
            continue

        # a very basic check if file count matches
        r_std, r_err, _ = run_command_over_ssh(host, f"ls mariposa/{input_dir} | wc -l")
        if "No such file or directory" in r_err:
            lines.append(
                f"rcp {SYNC_ZIP} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {SYNC_ZIP} && rm {SYNC_ZIP}'"
            )
            continue

        count_match = int(r_std) == file_count

        if clear:
            if count_match and clear_on_match is None:
                choice = input(f"file count matches {host} {file_count} are you sure you want to clear?")
                if choice != "y":
                    clear_on_match = False
                else:
                    clear_on_match = True
                log_info(f"clear_on_match is set to: {clear_on_match}, will apply to all")

            if clear_on_match is False:
                log_warn(f"skipping {host} due to clear_on_match")
                continue

            log_warn(f"force syncing on {host}")
            run_command_over_ssh(host, f"rm -r ~/mariposa/{input_dir}")
            lines.append(
                f"rcp {SYNC_ZIP} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {SYNC_ZIP} && rm {SYNC_ZIP}'"
            )
        else:
            log_check(
                int(r_std) == file_count,
                f"file count mismatch {host}, run data-sync with --clear to force sync",
            )

    if len(lines) == 0:
        log_info(f"no sync is required")
        return

    log_info(f"compressing {input_dir}")

    os.system(f"zip -r {SYNC_ZIP} {input_dir} > /dev/null")

    with open("sync.sh", "w") as f:
        f.write("#!/bin/bash\n")
        f.write("\n".join(lines))
        f.close()

    log_info(f"syncing {input_dir}")

    os.system("cat sync.sh | parallel > /dev/null")

    # confirm_input("remove temp files?")
    os.remove("sync.sh")
    os.remove(SYNC_ZIP)


def handle_code_sync():
    log_info("syncing code")
    cmd = f"(cd mariposa; rm -r data/dbs/ ; rm -r gen/ ; git checkout master; git pull; cd src/smt2action/; cargo build --release)"
    run_on_workers(cmd)


def handle_stop():
    log_info("stopping workers")
    cmd = "ps -aux | grep 'python3 src/exper_wizard.py' | awk  {'print \\$2'} | xargs kill -9"
    run_on_workers(cmd)


def handle_offload_single(args):
    log_check(os.path.exists(args.input_query_path), "input query does not exist")
    realpath = os.path.realpath(args.input_query_path)
    base_name = os.path.basename(realpath)
    server = random.choice(S190X_HOSTS)
    log_info(f"offloading to {server}")
    cmd = f"scp {realpath} {server}:~/mariposa/"
    os.system(cmd)
    cmd = f"ssh {server} 'cd mariposa; python3 src/exper_wizard.py single --input-query-path {base_name} -qv 1 -cv 4 -s {args.solver} -e {args.exp_config.exp_name} --clear-existing'"
    os.system(cmd)
