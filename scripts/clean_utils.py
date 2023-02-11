import re
from tqdm import tqdm
from configs.projects import *
import time
import subprocess

PUSH_CMD = re.compile("\(push( 1)?\)")
POP_CMD = re.compile("\(pop( 1)?\)")

def clean_dfy_komodo():
    p = D_KOMODO
    plain_dir = p.get_plain_dir()
    z3_clean_dir = p.clean_dirs[Z3_4_5_0]
    cvc_clean_dir = p.clean_dirs[CVC5_1_0_3]

    for path in tqdm(list_smt2_files(plain_dir)):
        z3_new_path = path.replace(plain_dir, z3_clean_dir)
        cvc_clean_path = path.replace(plain_dir, cvc_clean_dir)

        depth = 0
        f = open(path)
        z3o = open(z3_new_path, "w+")
        cvc5o = open(cvc_clean_path, "w+")

        for line in f.readlines():
            if re.search(PUSH_CMD, line):
                # skip the push, check for at most one push
                depth += 1
                assert(depth <= 1)
            else:
                z3o.write(line)

                if "bv2int" in line:
                    # for cvc5, use bv2nat instead
                    line = line.replace("bv2int", "bv2nat")

                cvc5o.write(line)
                if "(check-sat)" in line:
                    # cut off the rest
                    break

def subprocess_run(command, time_limit, debug=False, cwd=None):
    command = f"timeout {time_limit} " + command
    if debug:
        print(command)
    start_time = time.time()
    res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
    # milliseconds
    elapsed = round((time.time() - start_time) * 1000)
    stdout = res.stdout.decode("utf-8").strip()
    stderr = res.stderr.decode("utf-8").strip()
    return stdout, stderr, elapsed

def clean_dfy_frames_vbkv():
    p = D_FVBKV
    plain_dir = p.get_plain_dir()
    z3_clean_dir = p.clean_dirs[Z3_4_5_0]
    cvc_clean_dir = p.clean_dirs[CVC5_1_0_3]
    for path in tqdm(list_smt2_files(plain_dir)):
        z3_new_path = path.replace(plain_dir, z3_clean_dir)
        cvc_clean_path = path.replace(plain_dir, cvc_clean_dir)

        depth = 0
        f = open(path)
        z3o = open(z3_new_path, "w+")
        cvc5o = open(cvc_clean_path, "w+")

        for line in f.readlines():
            if re.search(PUSH_CMD, line):
                # skip the push, check for at most one push
                depth += 1
                assert(depth <= 1)
            else:
                z3o.write(line)
                if "bv2int" in line:
                    # for cvc5, use bv2nat instead
                    line = line.replace("bv2int", "bv2nat")
                cvc5o.write(line)

                if "(check-sat)" in line:
                    # cut off the rest
                    break

def remove_z3_options():
    p = D_KOMODO
    z3_clean_dir = p.clean_dirs[Z3_4_5_0]
    out_dir = "data/d_komodo_z3_opt/"

    for path in tqdm(list_smt2_files(z3_clean_dir)):
        z3_new_path = path.replace(z3_clean_dir, out_dir)
        f = open(path)
        z3o = open(z3_new_path, "w+")
        # z3o.write("(set-option :AUTO_CONFIG false)")

        for line in f.readlines():
            if line.startswith("(set-option"):
                continue
            z3o.write(line)
        # print(z3_new_path)

# remove_z3_options()

def not_matching(cur_command):
    assert (cur_command[0]) == "("
    # this should be fine
    return cur_command.count("(") != cur_command.count(")")

FUEL_PAT = """(declare-datatypes () ((Fuel (ZFuel) (SFuel (prec Fuel)))))"""

FUEL_ALT = """(declare-sort Fuel)
(declare-fun ZFuel () Fuel)
(declare-fun SFuel (Fuel) Fuel)
(declare-fun MaxIFuel () Fuel)"""

def clean_parentheses(lines):
    i = 0
    result_lines = []
    cur_command = ""
    while i < len(lines):
        cur_line = lines[i].strip()
        # print("cur_line: ", cur_line)
        cur_command += cur_line
        # print("cur_command: ", cur_command)
        # print("not matching? ", not_matching(cur_command))
        while not_matching(cur_command):
            i += 1
            cur_command += " " + lines[i].strip()
        if cur_command == FUEL_PAT:
            result_lines.append(FUEL_ALT + "\n")
        else:
            result_lines.append(cur_command + "\n")
        # print("command: ", cur_command)
        cur_command = ""
        i += 1
    return result_lines

def clean_fstar_vwasm():
    p = FS_VWASM
    plain_dir = p.get_plain_dir()
    z3_clean_dir = p.clean_dirs[Z3_4_5_0]
    for path in tqdm(list_smt2_files(plain_dir)):
        rel_path = path[len(plain_dir):]
        z3_new_path = z3_clean_dir + rel_path.replace("/", "-")
        f = open(path)
        z3o = open(z3_new_path, "w+")
        content = f.read()
        assert content.count("(check-sat)") == 1
        f.seek(0, 0)
        outlines = []
        for line in f:
            if re.search(PUSH_CMD, line) or re.search(POP_CMD, line):
                continue
            if ";" in line or line.startswith("(echo") or line.strip() == "":
                continue
            outlines.append(line)
            if "(check-sat)" in line:
                break
        outlines = clean_parentheses(outlines)
        z3o.writelines(outlines)

clean_fstar_vwasm()