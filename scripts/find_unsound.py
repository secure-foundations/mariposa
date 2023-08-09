from basic_utils import *
import os, re

pattern = re.compile(r"DafnyPreludebpl\.([0-9]+)")
# os.system("dotnet tool run boogie docs/dfy_unsound/DafnyPrelude.bpl /proverLog:DafnyPrelude.smt2")

def parse_core(core):
    cores = []
    for line in core.split("\n"):
        if "unsat-cores-dump-name" in line:
            cores.append(line)
    return cores

bpl_lines = open("docs/dafny/DafnyPrelude.bpl").readlines()

def to_file_name(depth):
    return f"docs/dafny/DafnyPrelude.inst.{depth}.smt2"

def print_bpl_axiom(line_num):
    while True:
        line = bpl_lines[line_num-1]
        print(line, end="")
        if ";" in line:
            break
        line_num += 1

def print_and_remove_core(depth, cores):
    cores = "|".join(cores)
    stdout, _ = run_subprocess(f"grep -E '{cores}' {to_file_name(depth)}")
    for line in stdout.split("\n"):
        line = int(re.search(pattern, line).group(1))
        print_bpl_axiom(line)
    command = f"sed -E -e '/{cores}/d' {to_file_name(depth)} > {to_file_name(depth+1)}"
    os.system(command)

def run_vampire(depth):
    while True:
        command = f"./solvers/vampire-4.8 {to_file_name(depth)} --input_syntax smtlib2 --output_mode ucore --time_limit 10"
        stdout, stderr = run_subprocess(command, debug=False)
        cores = parse_core(stdout)
        if len(cores) == 0:
            break
        print("iteration ", depth)
        # print(depth, cores)
        print_and_remove_core(depth, cores)
        print("")
        depth += 1

run_vampire(0)
