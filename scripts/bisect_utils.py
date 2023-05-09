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
import re

Z3_PATH = "./build/z3"

# def gen_bisec_tasks():
#     for cfg in ALL_CFGS:
#         summaries = load_solver_summaries(cfg, skip_unknowns=False)
#         classifier = Classifier("z_test")
#         classifier.timeout = 6e4
#         categories1 = categorize_queries(summaries[Z3_4_8_5], classifier)
#         categories2 = categorize_queries(summaries[Z3_4_8_8], classifier)
#         diff = categories1[Stability.STABLE.value].intersection(categories2[Stability.UNSTABLE.value])
#         # print(len(diff))
#         for l in diff:
#             solver_table = cfg.qcfg.get_solver_table_name(Z3_4_8_8)
#             con, cur = get_cursor(cfg.qcfg.db_path)
#             res = cur.execute(f"""SELECT query_path FROM {solver_table}
#                 WHERE vanilla_path = '{l}'
#                 AND perturbation != ''
#                 """)
#             assert(l.startswith("data/"))
#             assert(l.endswith(".smt2"))
#             p = l[5:-5]
#             tsk = open("data/bisect_tasks/" + p.replace("/", "--") + ".txt", "w+")
#             tsk.write(f"{l}\n")
#             for row in res.fetchall():
#                 mpath = row[0]
#                 assert mpath.find(p) != -1
#                 args = mpath.split(".")[-3:]
#                 assert args[-1] == "smt2"
#                 command = f"./target/release/mariposa -i {l} -p {args[1]} -o {row[0]} -s {args[0]}\n"
#                 tsk.write(command)

# def parse_bisect():
#     commit_re = re.compile("\[([a-z0-9]+)\]")
#     blames = dict()
#     logs = os.listdir("data/bisect_tasks")
#     all = set()
#     for log in logs:
#         if log.endswith(".txt"):
#             all.add(log)
#             continue
#         f = open(f"data/bisect_tasks/{log}")
#         lines = f.readlines()
#         log = log[:-4]
#         blames[log] = set()
#         for l in lines:
#             if "# first bad commit:" in l:
#                 blames[log].add(commit_re.search(l).group(1))
#                 break
#             if "# possible first bad commit:" in l:
#                 blames[log].add(commit_re.search(l).group(1))
#         assert blames[log] != set()

#     scores = {"inconclusive": 0}
    
#     for log in blames:
#         count = len(blames[log])
#         if count >= 2:
#             scores["inconclusive"] += 1
#             # print(log, count)
#             # print("../mariposa/scripts/bisect-metascript.sh", log)
#         else:
#             # score = 1.0 / len(blames[log])
#             for commit in blames[log]:
#                 scores[commit] = scores.get(commit, 0) + 1
#     incs = scores["inconclusive"]
#     scores = sorted(scores.items(), key=lambda x: x[1], reverse=True)
#     os.chdir('../z3')
#     commits = dict()
    
#     for commit, score in scores:
#         if commit == "inconclusive":
#             continue
#         res = subprocess_run(f"git show -s --format=%ct {commit}", 0)
#         commits[commit] = (score, int(res[0]))
#     os.chdir('../mariposa')
    
#     commits = sorted(commits.items(), key=lambda x: x[1][1])
    
#     start = 0

#     # print(start)
#     for commit, (count, date) in commits:
#         start += count
#         print(start)

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
