import sys
from utils.smt2_utils import *

def normalize_line(line):
    return line.replace(" ", "").strip()

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

def shake_partial(fmt_path, log_path, max_depth, output_path):
    stamps = parse_shake_log(log_path)
    assert(len(stamps) != 0)
    orig = get_asserts(fmt_path)
    assert key_set(stamps).issubset(key_set(orig))

    out_file = open(output_path, "w+")
    for line in open(output_path):
        if line.startswith("(assert "):
            nl = normalize_line(line)
            if nl not in stamps or stamps[nl] > max_depth:
                continue
        out_file.write(line)
    out_file.close()

if __name__ == "__main__":
    action = sys.argv[1]
    if action == "shake-partial":
        shake_partial(sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5])
