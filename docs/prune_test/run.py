import os, time, sys, subprocess

TEST_ROOT = os.path.dirname(os.path.abspath(__file__))
BPL_PATH = TEST_ROOT + "/test.bpl"
SMT_BPL_DEFAULT_PATH = TEST_ROOT + "/booige_default.smt2"
SMT_DFY_DEFAULT_PATH = TEST_ROOT + "/dafny_default.smt2"
SMT_BPL_PRUNE_PATH = TEST_ROOT + "/booige_prune.smt2"

BPL_OPTS = "/proverOpt:O:auto_config=false /proverOpt:O:type_check=true /proverOpt:O:smt.case_split=3 /proverOpt:O:smt.qi.eager_threshold=100 /proverOpt:O:smt.delay_units=true /proverOpt:O:smt.arith.solver=2 /useArrayAxioms /typeEncoding:a "#  + " /normalizeNames:1 /emitDebugInformation:0"

DFY_OPTS = "/compile:0 /functionSyntax:3 /deprecation:0" + " /normalizeNames:0 /emitDebugInformation:1"

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

os.system(f"rm {BPL_PATH}")

o, e, _ = subprocess_run(f"/home/yizhou7/dafny/Binaries/Dafny {sys.argv[1]} {DFY_OPTS} /print:{BPL_PATH} /proverLog:{SMT_DFY_DEFAULT_PATH}")
print(o, e)

cmd = f"dotnet tool run boogie {BPL_PATH} {BPL_OPTS} /proverLog:{SMT_BPL_DEFAULT_PATH}"
o, e, _ = subprocess_run(cmd, cwd=TEST_ROOT)
print("-" * 50)
print(o, e)

print("-" * 50)
cmd = f"dotnet tool run boogie {BPL_PATH} {BPL_OPTS} /prune /proverLog:{SMT_BPL_PRUNE_PATH}"
o, e, _ = subprocess_run(cmd, cwd=TEST_ROOT)
print(o, e)

