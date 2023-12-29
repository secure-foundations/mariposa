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
    def __init__(self, name_hash, fmt_contents, stamps, depth):
        self.name_hash = name_hash
        self.fmt_contents = fmt_contents
        self.stamps = stamps
        self.depth = depth

    def run_task(self, solver):
        temp_file = f"gen/{self.name_hash}.{self.depth}.smt2"
        emit_partial_shake_file(temp_file, self.fmt_contents, self.stamps, self.depth)
        rcode, elapsed = solver.run(temp_file, SHAKE_TIMEOUT)
        return rcode, elapsed, self.depth, temp_file

def run_shake_tasks(solver, task_queue, result_queue):
    while task_queue.qsize() > 0:
        task = task_queue.get()

        if task is None:
            break

        rc, et, depth, temp_file = task.run_task(solver)

        result_queue.put((rc, et, depth, temp_file))

# def shake_partial(output_path, fmt_path, log_path):
#     import multiprocessing as mp
#     from execute.solver_runner import RCode, SolverRunner
#     from configure.solver import SolverInfo
#     import time

#     fmt_contents = list(open(fmt_path).readlines())
#     stamps = parse_shake_log(log_path)
#     max_depth = max(stamps.values())

#     name_hash = get_name_hash(fmt_path)

#     task_queue = mp.Queue()
#     result_queue = mp.Queue()

#     solver = SolverRunner(SolverInfo("z3_4_12_2"))

#     for depth in range(max_depth + 1):
#         task_queue.put(ShakeTask(name_hash, fmt_contents, stamps, depth))

#     processes = []

#     for _ in range(NUM_SHAKE_PROCESSES):
#         p = mp.Process(target=run_shake_tasks, 
#                        args=(solver, task_queue, result_queue))
#         p.start()
#         processes.append(p)
    
#     out_content = []
#     expected = max_depth + 1

#     print(task_queue.qsize())

#     while expected > 0:
#         rc, et, d, path = result_queue.get()
#         print(f"[INFO] {d} {path} {RCode(rc)} {et}")
#         out_content.append(f"{d}\t{path}\t{RCode(rc)}\t{et}\n")
#         expected -= 1

#         if RCode(rc) == RCode.UNSAT:
#             # drain task queue
#             while not task_queue.empty():
#                 t = task_queue.get()
#                 print(f"[INFO] {t.depth} cancelled")
#                 expected -= 1
#                 out_content.append(f"{t.depth} cancelled {expected}\n")
#         else:
#             os.remove(path)

#     for _ in range(NUM_SHAKE_PROCESSES):
#         task_queue.put(None)

#     for p in processes:
#         p.join()

#     log_file = open(output_path, "w+")
#     for line in out_content:
#         log_file.write(line)
#     log_file.close()
#     print(f"[INFO] {output_path}")

def shake_partial(output_path, fmt_path, log_path):
    import multiprocessing as mp
    from execute.solver_runner import RCode, SolverRunner
    from configure.solver import SolverInfo

    fmt_contents = list(open(fmt_path).readlines())
    stamps = parse_shake_log(log_path)
    max_depth = max(stamps.values())

    name_hash = get_name_hash(fmt_path)

    task_queue = mp.Queue()
    result_queue = mp.Queue()

    solver = SolverRunner(SolverInfo("z3_4_12_2"))

    for depth in range(max_depth + 1):
        task_queue.put(ShakeTask(name_hash, fmt_contents, stamps, depth))

    processes = []

    for _ in range(NUM_SHAKE_PROCESSES):
        p = mp.Process(target=run_shake_tasks, 
                       args=(solver, task_queue, result_queue))
        p.start()
        processes.append(p)
    
    out_content = []
    expected = max_depth + 1

    print(task_queue.qsize())

    while expected > 0:
        rc, et, d, path = result_queue.get()
        print(f"[INFO] {d} {path} {RCode(rc)} {et}")
        out_content.append(f"{d}\t{path}\t{RCode(rc)}\t{et}\n")
        expected -= 1

        if RCode(rc) == RCode.UNSAT:
            # drain task queue
            while not task_queue.empty():
                t = task_queue.get()
                print(f"[INFO] {t.depth} cancelled")
                expected -= 1
                out_content.append(f"{t.depth} cancelled {expected}\n")
                
                while result_queue.qsize() > 0:
                    rc, et, d, path = result_queue.get()
                    print(f"[INFO] {d} {path} {RCode(rc)} {et}")
                    out_content.append(f"{d}\t{path}\t{RCode(rc)}\t{et}\n")
                break
        else:
            os.remove(path)

    for _ in range(NUM_SHAKE_PROCESSES):
        task_queue.put(None)

    for p in processes:
        p.kill()

    log_file = open(output_path, "w+")
    for line in out_content:
        log_file.write(line)

    log_file.close()
    print(f"[INFO] {output_path}")


# class ShakeRunner:
#     def __init__(self, out_path, fmt_path=None, log_path=None):
#         # if fmt_path is None and log_path is None:
#         #     assert orig_path is not None
#         # self.orig_path = orig_path
#         self.fmt_path = fmt_path
#         self.log_path = log_path
#         self.out_path = out_path

# def shake_no_oracle(orig_path, initial_depth, fmt_path=None, log_path=None):
#     name_hash = get_name_hash(orig_path)

#     if log_path is None:
#         assert fmt_path is None
#         log_path = f"temp/{name_hash}.shk"
#         fmt_path = f"temp/{name_hash}.smt2"

#     if not os.path.exists(fmt_path):
#         subprocess.run([
#             "./target/release/mariposa",
#             "-i", orig_path,
#             "-o", fmt_path,
#             "-m", "tree-shake",
#             "--shake-log-path", log_path])

#     assert os.path.exists(fmt_path)
#     assert os.path.exists(log_path)


#     fmt_contents = list(open(fmt_path).readlines())
#     stamps = parse_shake_log(log_path)
#     orig = get_asserts(fmt_path)
#     assert len(stamps) != 0
#     assert key_set(stamps).issubset(key_set(orig))

#     max_depth = max(stamps.values())
#     depth = min(max_depth, initial_depth)
#     temp_file = f"temp/{name_hash}.{depth}.smt2"

#     __emit_partial_shake_file(fmt_contents, stamps, temp_file, depth)
