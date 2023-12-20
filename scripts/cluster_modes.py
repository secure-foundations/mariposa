import os, subprocess, copy, time

from configure.project import Partition
from execute.exp_part import ExpPart
from local_modes import multi_mode

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

def manager_mode(args):
    exp = ExpPart(args.experiment, 
            args.project,
            args.solver, Partition(1, 1))

    exp.check_tables(args.clear)

    from multiprocessing.managers import BaseManager
    import threading
    import multiprocessing
    
    job_queue = multiprocessing.Queue()
    res_queue = multiprocessing.Queue()

    for i in range(1, args.total_parts + 1):
        wargs = copy.deepcopy(args)
        wargs.part = Partition(i, args.total_parts)
        wargs.analysis_skip = True
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
            exp.import_tables(temp_db_path, part)
        os.remove(temp_db_path)

def recovery_mode(args):
    exp = ExpPart(args.experiment, 
        args.project,
        args.solver, Partition(1, 1))

    available_db_paths = []
    for i in {1, 2, 5, 6, 7, 8}:
        temp_db_path = f"{exp.db_path}.{i}.temp"
        host = f"s190{i}"
        remote_db_path = f"{host}:~/mariposa/{exp.db_path}"

        if os.path.exists(temp_db_path):
            available_db_paths.append(temp_db_path)
            continue
        
        status = subprocess.call(['ssh', host, "test -f ~/mariposa/'{}'".format(exp.db_path)])

        if status == 0:
            command = f"scp {remote_db_path} {temp_db_path}"
            print(f"[INFO] copying db: {command}")
            os.system(command)

        if not os.path.exists(temp_db_path):
            print(f"[WARN] failed to copy db {remote_db_path}, skipping")
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
    
    if part_nums is None:
        print(f"[WARN] no partitions found, aborting")
        return

    missing_count = 0
    for missing_id in set(range(1, part_nums + 1)) - found_ids:
        print(f"[WARN] partition {missing_id} is missing")
        missing_count += 1
    if missing_count > 0:
        print(f"[WARN] {missing_count} partitions missing, aborting")
        return

    exp.check_tables(clear=True)

    for temp_db_path in available_db_paths:
        print(f"[INFO] importing from {temp_db_path}")
        for part in exp.probe_other_db(temp_db_path):
            print(f"[INFO] importing {part} from {temp_db_path}")
            exp.import_tables(temp_db_path, part)

    print(f"[INFO] done importing")

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
