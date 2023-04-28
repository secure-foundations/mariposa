### bisect.py -- Script that runs git bisect.
### Author: Yoshiki Takashima <ytakashi@andrew.cmu.edu>
#
# This script is the helper script for git bisection. This script
# builds Z3 and checks if the SMT file given as an argument is slow on
# this version or not.
#
# Way to run this is
# cd z3
# git bisect run python3 $THIS_SCRIPT $SMT_FILE
#
from typing import List
from subprocess import check_output, run, DEVNULL
from os import environ, path
import time

Z3_PATH = "./build/z3"

def compile_z3() -> bool:
    """Compiles Z3. Use short circuit to quit early if the build
    config fails.

    """

    start_time = time.time()
    BUILD_MAX_PARALLEL = 16
    print("building z3")

    run(["rm", "-rf", "build"])
    build_env = environ.copy()
    build_env["CC"] = "/usr/lib/ccache/gcc"
    build_env["CXX"] = "/usr/lib/ccache/g++"
    
    if run(["python3", "scripts/mk_make.py"], env=build_env, stdout=DEVNULL, stderr=DEVNULL).returncode == 0 \
        and run(["bash", "-c", f"(cd build; make -j{BUILD_MAX_PARALLEL})"], env=build_env, stdout=DEVNULL, stderr=DEVNULL).returncode == 0\
        and path.exists(Z3_PATH):
        elapsed = round((time.time() - start_time), 1)
        print("done building z3", elapsed)
        return True
    return False
            
def main(argv: List[str]) -> int:
    """Main logic of the script. This will first compile z3. If it
    fails to compile, then it returns 125. If it compiles, then z3 is
    run with a time bound. If the time bound is exceeded, return 1
    else 0 for success within time bound.
    """
    SKIP_COMIT_GIT_BISECT = 125

    if not compile_z3():
        return SKIP_COMIT_GIT_BISECT

    CMD = ["python3", f"/home/yizhou7/mariposa/scripts/runner.py", argv[1]]
    start_time = time.time()
    print("running mariposa")
    exe = run(
        CMD,
        capture_output=True,
        cwd=f"/home/yizhou7/mariposa/"
    )
    out = exe.stdout.decode()
    err = exe.stderr.decode()
    elapsed = round((time.time() - start_time), 1)    
    print(f"res: {exe.returncode} \n out: {out} \n err: {err}")
    print("done running mariposa", elapsed)
    return exe.returncode

if __name__ == "__main__":
    from sys import argv

    exit(main(list(argv)))
