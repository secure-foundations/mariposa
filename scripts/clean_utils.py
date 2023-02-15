import re
from tqdm import tqdm
from configs.projects import *
import time
import subprocess

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
    "push",
    "pop",
    "echo",
    "set-option :rlimit",
    "set-option :timeout"
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
(declare-fun SFuel (Fuel) Fuel)
(declare-fun MaxIFuel () Fuel)\n"""

def replace_fs_fuel(commands):
    replaced = False
    for i, command in enumerate(commands):
        if command == FUEL_CMD:
            replaced = True
            commands[i] = FUEL_ALT_CMD
            break
    assert replaced
    return commands

def clean_fs_project(project):
    assert project.framework == FrameworkName.FSTAR
    src_dir = project.get_plain_dir()
    dst_dir = project.clean_dirs[str(Z3_4_11_2)]

    for in_path in tqdm(list_smt2_files(src_dir)):
        cmds = read_standard_cmds(in_path)
        cmds = replace_fs_fuel(cmds)

        out_path = convert_path(in_path, src_dir, dst_dir)
        out_f = open(out_path, "w+")
        out_f.writelines(cmds)

def clean_dfy_project(project):
    assert project.framework == FrameworkName.DAFNY
    src_dir = project.get_plain_dir()
    dst_dir = project.clean_dirs[Z3_4_11_2]

    for in_path in tqdm(list_smt2_files(src_dir)):
        out_path = convert_path(in_path, src_dir, dst_dir)
        cmds = read_standard_cmds(in_path)
        open(out_path, "w+").writelines(cmds)

clean_dfy_project(D_LVBKV)

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
