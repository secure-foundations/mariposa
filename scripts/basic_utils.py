import os, sys

def exit_with(msg):
    print(msg)
    sys.exit(1)

def exit_with_on_fail(cond, msg):
    if not cond:
        exit_with(msg)

def list_smt2_files(sub_root):
    exit_with_on_fail(os.path.isdir(sub_root), f"[ERROR] {sub_root} is not a directory")
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths
