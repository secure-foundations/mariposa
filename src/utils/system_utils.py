import os, sys, time
import shutil
import subprocess

class BColors:
    INFO = '\033[92m'
    WARNING = '\033[93m'
    ERROR = '\033[91m'
    ENDC = '\033[0m'

def log_info(msg, end="\n"):
    print(f"{BColors.INFO}[INFO] {msg} {BColors.ENDC}", end=end)

def log_warn(msg):
    print(f"{BColors.WARNING}[WARN] {msg} {BColors.ENDC}")

def log_error(msg):
    print(f"{BColors.ERROR}[ERROR] {msg} {BColors.ENDC}")

def exit_with(msg):
    log_error(msg)
    sys.exit(1)

def log_check(cond, msg):
    if not cond:
        log_error("check failed!")
        exit_with(msg)

def confirm_input(msg):
    log_info(f"{msg} [Y]", end=" ")
    log_check(input() == "Y", f"aborting")

def subprocess_run(command, timeout=None, debug=False, cwd=None):
    if debug:
        print(command)
    start_time = time.time()
    if timeout is not None:
        command = f"timeout {timeout}s {command}"
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

def list_files_ext(sub_root, ext):
    log_check(os.path.isdir(sub_root), f"[ERROR] {sub_root} is not a directory")
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
    dst_path = flatten_path(src_dir, src_path)
    dst_path = dst_path.replace(src_dir, dst_dir)
    return dst_path

def scrub(name):
    return ''.join([c if c.isalnum() else "_" for c in name])

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

def pre_create_file(path, force_clear):
    dir_path = os.path.dirname(path)
    create_dir(dir_path)

    if os.path.exists(path):
        if not force_clear:
            confirm_input(f"file {path} already exists, remove it?")
        os.remove(path)
    