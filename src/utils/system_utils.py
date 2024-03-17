import os, sys, time
import shutil
import subprocess
from base.defs import DEBUG_ENABLE

class BColors:
    INFO = '\033[92m'
    WARNING = '\033[93m'
    ERROR = '\033[91m'
    DEBUG = '\033[94m'
    ENDC = '\033[0m'

def log_info(msg, end="\n"):
    print(f"{BColors.INFO}[INFO] {msg} {BColors.ENDC}", end=end)

def log_warn(msg):
    print(f"{BColors.WARNING}[WARN] {msg} {BColors.ENDC}")

def log_error(msg):
    print(f"{BColors.ERROR}[ERROR] {msg} {BColors.ENDC}")

def log_debug(msg, end="\n"):
    if DEBUG_ENABLE:
        print(f"{BColors.DEBUG}[DEBUG] {msg} {BColors.ENDC}", end=end)

def print_banner(msg):
    print(f"=== {msg} ===")

def exit_with(msg):
    log_error(msg)
    assert False
    sys.exit(1)

def log_check(cond, msg):
    if not cond:
        exit_with(msg)

def confirm_input(msg):
    log_info(f"{msg} [Y]", end="")
    log_check(input() == "Y", f"aborting")

def subprocess_run(command, timeout=None, debug=False, cwd=None, shell=False):
    if debug:
        print(" ".join(command))
    start_time = time.time()
    if timeout is not None:
        if shell:
            command = f"timeout {timeout}s {command}"
        else:
            command = ["timeout", f"{timeout}s"] + command
    res = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=shell, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

def list_files_ext(sub_root, ext):
    log_check(os.path.isdir(sub_root), f"{sub_root} is not a directory")
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(ext):
                file_paths.append(os.path.join(root, file))
    return file_paths

def list_smt2_files(sub_root):
    return list_files_ext(sub_root, ".smt2")

def list_files(sub_root):
    return list_files_ext(sub_root, "")

def get_file_count(sub_root):
    return len(list_files(sub_root))

def is_flat_dir(sub_root):
    for root, dirs, _ in os.walk(sub_root):
        if len(dirs) > 0:
            return False
    return True

def flatten_path(base_dir, path):
    assert base_dir in path
    if not base_dir.endswith("/"):
        base_dir += "/"
    rest = path[len(base_dir):]
    rest = rest.replace("/", "-")
    rest = rest.replace("!", "_")
    rest = rest.replace("&", "_")
    rest = rest.replace(" ", "_")
    return base_dir + rest

def convert_path(src_path, src_dir, dst_dir):
    if not src_dir.endswith("/"): src_dir += "/"
    if not dst_dir.endswith("/"): dst_dir += "/"
    log_check(src_path.startswith(src_dir), f"{src_path} does not start with {src_dir}")
    dst_path = flatten_path(src_dir, src_path)
    dst_path = dst_path.replace(src_dir, dst_dir)
    return dst_path

def scrub(name):
    return ''.join([c if c.isalnum() else "_" for c in name])

def is_simple_id(name):
    import re
    return re.match("^[a-z0-9_]*$", name)

def line_count(filename):
    with open(filename) as f:
        for i, _ in enumerate(f):
            pass
    return i + 1

def get_name_hash(filename):
    import hashlib
    return hashlib.sha256(filename.encode()).hexdigest()

def read_last_line(filename):
    with open(filename, 'rb') as f:
        try:  # catch OSError in case of a one line file 
            f.seek(-2, os.SEEK_END)
            while f.read(1) != b'\n':
                f.seek(-2, os.SEEK_CUR)
        except OSError:
            exit_with(f"failed to read last line of {filename}")
        last = f.readline().decode()
    return last

def reset_dir(path, overwrite):
    if not os.path.exists(path):
        # non-existent directory, we can create it
        os.makedirs(path)
        return

    log_check(os.path.isdir(path), f"{path} is not a directory!")

    if len(os.listdir(path)) == 0:
        # empty directory, we are done
        return

    if not overwrite:
        confirm_input(f"directory {path} already exists, remove it?")

    shutil.rmtree(path)

    os.makedirs(path)

def create_dir(path):
    if not os.path.exists(path):
        os.makedirs(path)

def file_exists(path):
    return os.path.exists(path) and os.path.isfile(path)

def remove_file(path):
    if file_exists(path):
        log_check(os.path.isfile(path), f"{path} is a directory, not a file!")
        os.remove(path)

def remove_dir(path):
    if os.path.exists(path):
        log_check(os.path.isdir(path), f"{path} is a file, not a directory!")
        shutil.rmtree(path)
