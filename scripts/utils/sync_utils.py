from sys_utils import *

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

lines = []

for i in {1, 2 , 4, 5, 6, 7, 8}:
    host = f"s190{i}"
    if host == cur_host:
        continue
    # very basic check if file count matches
    remote_count = subprocess_run(f"ssh -t {host} 'ls -l mariposa/{dir} | wc -l'")[0]
    if "No such file or directory" in remote_count:
        # print(f"[INFO] sending zip to {host}")
        lines.append(f"rcp {zipped} {host}:~/mariposa && ssh -t {host} 'cd mariposa && unzip {zipped} && rm {zipped}'")
    else:
        # print(remote_count == file_count)
        san_check(remote_count == file_count, f"[ERROR] file count mismatch {host}")

with open("sync.sh", "w") as f:
    f.write("#!/bin/bash\n")
    f.write("\n".join(lines))
    f.close()

print(f"[INFO] {len(lines)} commands written to sync.sh")