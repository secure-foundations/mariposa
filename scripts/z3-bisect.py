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
    BUILD_MAX_PARALLEL = 1

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


def z3_solves_within_time_bound(smt_formula_path) -> bool:
    """Run z3 with Z3_TIMEOUT as the limit."""

    out: str = run(
        ["python3", "/home/ytakashima/mariposa/scripts/runner.py", smt_formula_path],
        capture_output=True,
    ).stdout.decode()
    print(f"mariposa  result: {out}")
    return "[RESULT]:  unstable" not in out


def main(argv: List[str]) -> int:
    """Main logic of the script. This will first compile z3. If it
    fails to compile, then it returns 125. If it compiles, then z3 is
    run with a time bound. If the time bound is exceeded, return 1
    else 0 for success within time bound.

    """
    SKIP_COMIT_GIT_BISECT = 125
    NEGATIVE = 1
    POSITIVE = 0

    if len(argv) < 1:
        return SKIP_COMIT_GIT_BISECT

    if not compile_z3():
        return SKIP_COMIT_GIT_BISECT

    if not z3_solves_within_time_bound(argv[1]):
        return NEGATIVE

    return POSITIVE


if __name__ == "__main__":
    from sys import argv

    exit(main(list(argv)))
