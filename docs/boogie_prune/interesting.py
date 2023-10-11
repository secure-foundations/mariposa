#! /usr/bin/env python3

import os, sys, time
import subprocess

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

orig_cmd = """timeout 2 dotnet tool run boogie woot.mini2.bpl /timeLimit:1 /proverOpt:O:auto_config=false /proverOpt:O:type_check=true /proverOpt:O:smt.case_split=3 /proverOpt:O:smt.qi.eager_threshold=100 /proverOpt:O:smt.delay_units=true"""

cwd = os.getcwd()

# change directory to directory of script
abspath = os.path.abspath(__file__)
dname = os.path.dirname(abspath)
os.chdir(dname)

origi, err0, _ = subprocess_run(orig_cmd.replace("woot.mini2.bpl", cwd + "/woot.mini2.bpl"))
origi += err0

pruned, err1, _ = subprocess_run(orig_cmd.replace("woot.mini2.bpl", cwd + "/woot.mini2.bpl /prune"))
pruned += err1

if "Boogie program verifier finished with 2 verified, 0 errors" in origi and \
    "Boogie program verifier finished with 0 verified, 2 errors" in pruned:
    print("INTERESTING")
    sys.exit(0)

if "Boogie program verifier finished with 1 verified, 0 errors" in origi and \
    "Boogie program verifier finished with 0 verified, 1 error" in pruned:
    print("INTERESTING")
    sys.exit(0)

else:
    print(origi)
    print(pruned)
    print("NOT INTERESTING")
    sys.exit(1)
