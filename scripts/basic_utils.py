import os, sys, subprocess

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

def list_all_files(sub_root):
    exit_with_on_fail(os.path.isdir(sub_root), f"[ERROR] {sub_root} is not a directory")
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            file_paths.append(os.path.join(root, file))
    return file_paths


def run_subprocess(command, debug=False, cwd=None):
    if debug:
        print(command)
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr

def scrub(name):
    return ''.join([c if c.isalnum() else "_" for c in name])