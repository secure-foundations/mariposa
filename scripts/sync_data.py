from basic_utils import *

dir = sys.argv[1]
assert dir.startswith("data/")
assert os.path.isdir(dir)

zipped = "sync.zip"

if os.path.exists(zipped):
    os.remove(zipped)

os.system(f"zip -r {zipped} {dir}")

file_count = subprocess_run(f'ls -l {dir} | wc -l')[0]
cur_host = subprocess_run("hostname")[0]
# print(cur_host)

for i in {1, 2 ,4, 5, 6, 7, 8}:
    host = f"s190{i}"
    if host == cur_host:
        continue
    # very basic check if file count matches
    remote_count = subprocess_run(f"ssh -t {host} 'ls -l mariposa/{dir} | wc -l'")[0]
    if "No such file or directory" in remote_count:
        # print(f"[INFO] sending zip to {host}")
        print(f"rcp {zipped} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {zipped} && rm {zipped}'")
    else:
        exit_with_on_fail(remote_count == file_count, f"[ERROR] file count mismatch {host}")
