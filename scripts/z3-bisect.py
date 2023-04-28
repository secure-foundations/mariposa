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
from subprocess import check_output, run
from os import environ, path

Z3_PATH = "./build/z3"


def compile_z3() -> bool:
    """Compiles Z3. Use short circuit to quit early if the build
    config fails.

    """
    BUILD_MAX_PARALLEL = 16

    run(["rm", "-rf", "build"])
    build_env = environ.copy()
    build_env["CC"] = "/usr/lib/ccache/gcc"
    build_env["CXX"] = "/usr/lib/ccache/g++"
    return (
        run(["python3", "scripts/mk_make.py"], env=build_env).returncode == 0
        and run(["bash", "-c", f"(cd build; make -j{BUILD_MAX_PARALLEL})"]).returncode
        == 0
        and path.exists(Z3_PATH)
    )

timeout = 60

from analyzer import RCode 
from analyzer import Classifier
from analyzer import Stablity
from runner import parse_basic_output_z3
from runner import subprocess_run
import numpy as np

def async_run_single_mutant(results, command):
    items = command.split(" ")
    os.system(command)
    items = command.split(" ")
    command = f"solvers/z3_place_holder {items[6]} -T:{timeout}"
    out, err, elapsed = subprocess_run(command, timeout + 1)
    rcode = parse_basic_output_z3(out)
    os.system(f"rm {items[6]}")
    results.append((elapsed, rcode))


def mariposa(task_file):
    commands = [t.strip() for t in open(task_file, "r").readlines()]
    plain = commands[0]
    commands = commands[1:]

    import multiprocessing as mp
    manager = mp.Manager()
    pool = mp.Pool(processes=7)

    command = f"solvers/z3_place_holder {plain} -T:{timeout}"
    out, err, elapsed = subprocess_run(command, timeout + 1)
    rcode = parse_basic_output_z3(out)
    pr = (elapsed, rcode)
    classifier = Classifier("z_test")
    classifier.timeout = 6e4 # 1 min

    reseeds = manager.list([pr])
    renames = manager.list([pr])
    shuffles = manager.list([pr])

    for command in commands:
        if "rseed" in command:
            pool.apply_async(async_run_single_mutant, args=(reseeds, command))
        elif "rename" in command:
            pool.apply_async(async_run_single_mutant, args=(renames, command))
        elif "shuffle" in command:
            pool.apply_async(async_run_single_mutant, args=(shuffles, command))
        else:
            assert False
    
    pool.close()
    pool.join()

    assert len(reseeds) == len(renames) == len(shuffles) == 61

    blob = np.zeros((3, 2, 61), dtype=int)
    for i, things in enumerate([reseeds, renames, shuffles]):
        for j, (veri_times, veri_res) in enumerate(things):
            blob[i, 0, j] = RCode.from_str(veri_res).value
            blob[i, 1, j] = veri_times

    cat = classifier.categorize_query(blob)
    if cat == Stablity.STABLE:
        return 0 # good
    if Stablity.INCONCLUSIVE:
        return 125
    return 1 # bad 

def main(argv: List[str]) -> int:
    """Main logic of the script. This will first compile z3. If it
    fails to compile, then it returns 125. If it compiles, then z3 is
    run with a time bound. If the time bound is exceeded, return 1
    else 0 for success within time bound.

    """
    SKIP_COMIT_GIT_BISECT = 125

    if len(argv) < 3:
        raise Exception("not enough inputs")

    if not compile_z3():
        return SKIP_COMIT_GIT_BISECT

    return mariposa()

if __name__ == "__main__":
    from sys import argv

    exit(main(list(argv)))
