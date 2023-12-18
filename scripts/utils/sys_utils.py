import os, sys, time
import subprocess

def exit_with(msg):
    print(msg)
    sys.exit(1)

def exit_with_on_fail(cond, msg):
    if not cond:
        exit_with(msg)

def subprocess_run(command, debug=False, cwd=None):
    if debug:
        print(command)
    start_time = time.time()
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

def check_serenity_status():
    print("checking scaling_governor...")
    stdout, _, _ = subprocess_run("cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | uniq")
    assert stdout == "performance"

    print("[INFO] building mariposa...")
    stdout, _, _ = subprocess_run("git rev-parse --abbrev-ref HEAD")
    if stdout != "master":
        print("[WARNING] not on master branch")
    os.system("cargo build --release")

def list_smt2_files(sub_root):
    return list_files_ext(sub_root, ".smt2")

def list_files(sub_root):
    return list_files_ext(sub_root, "")

def list_files_ext(sub_root, ext):
    exit_with_on_fail(os.path.isdir(sub_root), f"[ERROR] {sub_root} is not a directory")
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(ext):
                file_paths.append(os.path.join(root, file))
    return file_paths

def flatten_path(base_dir, path):
    assert base_dir in path
    if not base_dir.endswith("/"):
        base_dir += "/"
    rest = path[len(base_dir):]
    rest = rest.replace("/", "-")
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

# def percent(a, b):
#     return a * 100 / b

# def rd_percent(a, b):
#     return round(a * 100 / b, 2)

# def rd_percent_str(a, b):
#     return f"{rd_percent(a, b)}%"
