from utils.smt2_utils import *
import subprocess, os

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

def __emit_partial_shake_file(output_path, fmt_contents, stamps, max_depth):
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
    
SHAKE_TIMEOUT = 6000

def shake_partial(output_path, fmt_path, log_path, initial_depth):
    from execute.solver_runner import RCode, SolverRunner
    from configure.solver import SolverInfo

    fmt_contents = list(open(fmt_path).readlines())
    stamps = parse_shake_log(log_path)
    max_depth = max(stamps.values())
    initial_depth = min(max_depth, initial_depth)

    name_hash = get_name_hash(fmt_path)
    temp_file = f"gen/{name_hash}.smt2"
    __emit_partial_shake_file(temp_file, fmt_contents, stamps, initial_depth)

    solver = SolverRunner(SolverInfo("z3_4_12_2"))
    rcode, elapsed = solver.run(temp_file, SHAKE_TIMEOUT)
    rcode = RCode(rcode)
    # if rcode == RCode.TIMEOUT:

    print(rcode, elapsed)
    
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
