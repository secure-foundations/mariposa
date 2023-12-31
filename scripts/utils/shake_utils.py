from utils.smt2_utils import *
import os

def parse_shake_log(filename):
    cmds = dict()
    for line in open(filename):
        line = line.strip().split("|||")
        stamp = int(line[0])
        nl = normalize_line(line[1])
        if nl.startswith("(assert"):
            cmds[nl] = stamp
    return cmds

def key_set(d):
    return set(d.keys())

def emit_partial_shake_file(output_path, fmt_contents, stamps, max_depth):
    if os.path.exists(output_path):
        print(f"[WARN] {output_path} already exists")

    out_file = open(output_path, "w+")
    for line in fmt_contents:
        if line.startswith("(assert "):
            nl = normalize_line(line)
            if nl not in stamps or stamps[nl] > max_depth:
                continue
        out_file.write(line)
    out_file.close()
    
SHAKE_TIMEOUT = 60
NUM_SHAKE_PROCESSES = 4

class ShakeTask:
    def __init__(self, orig_path, name_hash, fmt_contents, stamps, depth):
        self.orig_path = orig_path
        self.name_hash = name_hash
        self.fmt_contents = fmt_contents
        self.stamps = stamps
        self.depth = depth

    def run_task(self, solver):
        if self.depth != -1:
            temp_file = f"gen/{self.name_hash}.{self.depth}.smt2"
            emit_partial_shake_file(temp_file, self.fmt_contents, self.stamps, self.depth)
        else:
            temp_file = self.orig_path
        rcode, elapsed = solver.run(temp_file, SHAKE_TIMEOUT)
        return rcode, elapsed, self.depth, temp_file

def run_shake_tasks(solver, task_queue, result_queue):
    while task_queue.qsize() > 0:
        task = task_queue.get()

        if task is None:
            break

        rc, et, depth, temp_file = task.run_task(solver)

        result_queue.put((rc, et, depth, temp_file))

def shake_partial(output_path, orig_path, fmt_path, log_path, remove=True):
    import multiprocessing as mp
    from execute.solver_runner import RCode, SolverRunner
    from configure.solver import SolverInfo
    import time

    fmt_contents = list(open(fmt_path).readlines())
    stamps = parse_shake_log(log_path)
    max_depth = max(stamps.values())

    name_hash = get_name_hash(fmt_path)

    task_queue = mp.Queue()
    # lock = mp.Lock()
    result_queue = mp.Queue()

    solver = SolverRunner(SolverInfo("z3_4_12_2"))
    
    task_queue.put(ShakeTask(orig_path, name_hash, fmt_contents, stamps, -1))

    for depth in range(max_depth + 1):
        task_queue.put(ShakeTask(orig_path, name_hash, fmt_contents, stamps, depth))

    processes = []

    for _ in range(NUM_SHAKE_PROCESSES):
        p = mp.Process(target=run_shake_tasks, 
                       args=(solver, task_queue, result_queue))
        p.start()
        processes.append(p)
    
    out_content = []
    expected = max_depth + 1

    while expected > 0:
        rc, et, d, path = result_queue.get()
        print(f"[INFO] {d} {path} {RCode(rc)} {et}")
        out_content.append(f"[INFO] report {d}\t{path}\t{RCode(rc)}\t{et}\n")
        expected -= 1

        if RCode(rc) == RCode.UNSAT:
            # drain task queue
            while not task_queue.empty():
                try:
                    t = task_queue.get(block=False)
                    out_content.append(f"[INFO] cancelled {t.depth}\n")
                except mp.queues.Empty:
                    break

            grace_period = int(et * 0.8 /1000) + 1
            time.sleep(grace_period)
            print("[INFO] grace period", grace_period)
            out_content.append(f"[INFO] grace period {grace_period}\n")

            while result_queue.qsize() > 0:
                rc, et, d, path = result_queue.get()
                print(f"[INFO] {d} {path} {RCode(rc)} {et}")
                out_content.append(f"[INFO] report {d}\t{path}\t{RCode(rc)}\t{et}\n")
            break

    for _ in range(NUM_SHAKE_PROCESSES):
        task_queue.put(None)

    for p in processes:
        p.kill()

    log_file = open(output_path, "w+")
    for line in out_content:
        log_file.write(line)

    log_file.close()
    print(f"[INFO] {output_path}")

    if remove:
        os.system(f"rm gen/{name_hash}.*.smt2")

def shake_oracle(output_path, fmt_path, log_path, depth):
    fmt_contents = list(open(fmt_path).readlines())
    stamps = parse_shake_log(log_path)
    emit_partial_shake_file(output_path, fmt_contents, stamps, depth)
    print(f"[INFO] {output_path} generated")

def parse_shake_partial_log(shkp_log_path):
    import re
    lines = open(shkp_log_path).readlines()
    lines = [line.strip() for line in lines]
    depths = dict()
    for line in lines:
        assert line.startswith("[INFO]")
        if not line.startswith("[INFO] report"):
            continue
        items = re.split(r'\t| ', line)[2:]
        if items[2] != "unsat":
            assert items[2] in {"sat", "unknown", "timeout"}
            continue
        d, time = int(items[0]), int(items[3])
        depths[d] = time
    return depths
