import re
from tqdm import tqdm
from configs.projects import *

SPACED_CMD = re.compile("\(( +)[a-z]+")
def remove_cmd_space(cmd):
    match = re.search(SPACED_CMD, cmd)
    if match:
        s, e = match.start(1), match.end(1)
        return cmd[:s] + cmd[e:]
    return cmd

# should not neeed stack if we know the input is well formed
def parentheses_not_matching(cur_command):
    # assert (cur_command[0]) == "("
    return cur_command.count("(") != cur_command.count(")")

def convert_to_standard_cmds(lines):
    i = 0
    commands = []
    cur_command = ""

    new_lines = []
    for line in lines:
        line = line.strip()
        if line.startswith(";") or line == "":
            continue
        new_lines.append(line)

    lines = new_lines

    while i < len(lines):
        cur_line = lines[i].strip()
        i += 1

        cur_command += cur_line
        while parentheses_not_matching(cur_command):
            cur_command += " " + lines[i].strip()
            i += 1
        cur_command = remove_cmd_space(cur_command)
        commands.append(cur_command + "\n")
        cur_command = ""
    return commands

def remove_target_cmds(commands, targets):
    new_commands = []
    for command in commands:
        remove = False
        for target in targets:
            if command.startswith("(" + target):
                remove = True
                break
        if not remove:
            new_commands.append(command.strip() + "\n")
    return new_commands

def cutoff_check_sat(commands, ignore_rest):
    index = None
    for i, command in enumerate(commands):
        if "check-sat" in command:
            # there should be one check-sat?
            assert index is None

            index = i
            if ignore_rest:
                break
    return commands[:index+1]

def flatten_path(base_dir, path):
    assert base_dir in path
    if not base_dir.endswith("/"):
        base_dir += "/"
    rest = path[len(base_dir):]
    rest = rest.replace("/", "-")
    return base_dir + rest

def convert_path(src_path, src_dir, dst_dir):
    dst_path = flatten_path(src_dir, src_path)
    dst_path = dst_path.replace(src_dir, dst_dir)
    return dst_path

STD_REMOVE_CMDS = {
    # "push",
    # "pop",
    "echo",
    "set-option :rlimit",
    "set-option :RLIMIT",
    "set-option :timeout",
    "set-option :TIMEOUT",
    "set-option :fixedpoint.TIMEOUT",
}

def read_standard_cmds(in_path):
    in_f = open(in_path)
    lines = in_f.readlines()
    # convert to command standard form
    cmds = convert_to_standard_cmds(lines)
    # remove push, pop, echo and rlimit
    cmds = remove_target_cmds(cmds, STD_REMOVE_CMDS)
    cmds = cutoff_check_sat(cmds, ignore_rest=True)
    return cmds

FUEL_CMD = """(declare-datatypes () ((Fuel (ZFuel) (SFuel (prec Fuel)))))\n"""

FUEL_ALT_CMD = """(declare-sort Fuel)
(declare-fun ZFuel () Fuel)
(declare-fun SFuel (Fuel) Fuel)\n"""

def replace_fs_fuel(commands):
    replaced = False
    for i, command in enumerate(commands):
        if command == FUEL_CMD:
            replaced = True
            commands[i] = FUEL_ALT_CMD
            break
    assert replaced
    return commands

DSORT_CMD = re.compile("\(declare-sort ([^\)]+)\)")
QID_ATTR = re.compile(":qid @([^ \)]+)")
NAMED_ATTR = re.compile(":named @([^ \)]+)")
BOXINT_NEG = re.compile("BoxInt (-[0-9]+)")

import string

# def check_single_pattern(command):

def clean_cmds_cvc5(commands):
    for i, command in enumerate(commands):
        match = re.search(DSORT_CMD, command)
        if match:
            res = f"(declare-sort {match.group(1)} 0)"
            command = command.replace(match.group(0), res)
        if "bv2int" in command:
            command = command.replace("bv2int", "bv2nat")
        command = command.replace("(iff ", "(= ")
        command = command.replace("(implies ", "(=> ")
        match = re.search(NAMED_ATTR, command)
        if match:
            res = ''.join(random.choices(string.ascii_lowercase, k=10))
            command = command.replace(match.group(0), f":named {res}")

        matches = re.finditer(BOXINT_NEG, command)

        for match in matches:
            num = match.group(1)
            command = command.replace(num, f"(- {num[1:]})")
        command = command.replace(":pattern (Prims.precedes t1 t2 e1 e2)", ":pattern ((Prims.precedes t1 t2 e1 e2))")
        commands[i] = command

def clean_fs_project(project, z3_dst_dir, cvc5_dst_dir):
    src_dir = project.get_plain_dir()

    for in_path in tqdm(list_smt2_files(src_dir)):
        cmds = read_standard_cmds(in_path)
        cmds = replace_fs_fuel(cmds)
        clean_cmds_cvc5(cmds)

        cvc5_out_path = convert_path(in_path, src_dir, cvc5_dst_dir)
        cvc5_out_f = open(cvc5_out_path, "w+")
        cvc5_out_f.writelines(cmds)

        # z3_out_path = convert_path(in_path, src_dir, z3_dst_dir)
        # z3_out_f = open(z3_out_path, "w+")
        # z3_out_f.writelines(cmds)

def clean_dfy_project(project, dst_dir):
    src_dir = project.get_plain_dir()

    for in_path in tqdm(list_smt2_files(src_dir)):
        out_path = convert_path(in_path, src_dir, dst_dir)
        cmds = read_standard_cmds(in_path)
        open(out_path, "w+").writelines(cmds)

def split_queries(file_path):
    in_f = open(file_path)
    lines = in_f.readlines()
    # convert to command standard form
    cmds = convert_to_standard_cmds(lines)
    # remove push, pop, echo and rlimit
    cmds = remove_target_cmds(cmds, STD_REMOVE_CMDS)
    depth = 0
    stack = [[]]
    splits = 0
    for cmd in cmds:
        if cmd.startswith("(push"):
            depth += 1
            stack.append([])
        elif cmd.startswith("(pop"):
            depth -= 1
            stack = stack[:-1]
        else:
            assert depth == len(stack) - 1
            stack[depth].append(cmd)

        if "check-sat" in cmd:
            splits += 1
            out_f = open(f"data/v_test3_z3_clean/{file_path[:-5]}.{splits}.smt2", "w+")
            for item in stack:
                out_f.writelines(item)
    return cmds

split_queries("top_sort_dfs.smt2")

# FS_DICE = ProjectConfig("fs_dice", FrameworkName.FSTAR, Z3_4_8_5)
# clean_fs_project(FS_DICE, None, None)
# def subprocess_run(command, time_limit, debug=False, cwd=None):
#     command = f"timeout {time_limit} " + command
#     if debug:
#         print(command)
#     start_time = time.time()
#     res = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
#     # milliseconds
#     elapsed = round((time.time() - start_time) * 1000)
#     stdout = res.stdout.decode("utf-8").strip()
#     stderr = res.stderr.decode("utf-8").strip()
#     return stdout, stderr, elapsed
