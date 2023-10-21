import sys
from basic_utils import *

def get_asserts(filename):
    cmds0 = dict()
    if filename is None:
        return cmds0
    for line in open(filename):
        if line.startswith("(assert "):
            cmds0[line.replace(" ", "").strip()] = line.strip()
    return cmds0

def key_set(d):
    return set(d.keys())

def value_set(d):
    return set(d.values())

def mariposa_format(orig_path, format_path=None):
    if format_path is None:
        outputs = subprocess_run(f"./target/release/mariposa -i {orig_path}")
        return outputs[0]
    else:
        os.system(f"./target/release/mariposa -i {orig_path} -o {format_path}")

if __name__ == "__main__":
    a = get_asserts(sys.argv[1])
    b = get_asserts(sys.argv[2])
    for i in a.keys() - b.keys():
        print(a[i])
    print(len(a), len(b), len(a.keys() & b.keys()))