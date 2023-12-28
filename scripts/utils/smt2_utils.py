import os

def normalize_line(line):
    return line.replace(" ", "").strip()

def get_asserts(filename):
    cmds = dict()
    if filename is None or not os.path.exists(filename):
        return cmds
    with open(filename) as f:
        for line in f.readlines():
            if line.startswith("(assert "):
                cmds[normalize_line(line)] = line.strip()
    return cmds

def get_name_hash(filename):
    import hashlib
    return hashlib.sha256(filename.encode()).hexdigest()

def count_asserts(filename):
    import subprocess, numpy as np
    cmd = r'rg -e "\(assert" -c' + f" '{filename}'"
    output = subprocess.run(cmd,
        shell=True, capture_output=True, text=True).stdout
    if output == "":
        print(f"[WARN] {filename} has no asserts")
        return np.nan
    return int(output)
