from enum import Enum
import os
import subprocess

from base.defs import MARIPOSA
from utils.system_utils import log_check, log_warn

def normalize_line(line):
    return line.replace(" ", "").strip()

def get_asserts(filename):
    import os
    cmds = dict()
    if filename is None or not os.path.exists(filename):
        return cmds
    with open(filename) as f:
        for line in f.readlines():
            if line.startswith("(assert "):
                cmds[normalize_line(line)] = line.strip()
    return cmds

def count_asserts(filename):
    import subprocess, numpy as np
    cmd = r'rg -e "\(assert" -c' + f" '{filename}'"
    output = subprocess.run(cmd,
        shell=True, capture_output=True, text=True).stdout
    if output == "":
        log_warn(f"{filename} has no asserts")
        return np.nan
    return int(output)

_PARTIAL_ORDER_ALT = [
    "(declare-fun partial-order (Height Height) Bool)",
    "(assert (forall ((x Height)) (partial-order x x)))",
    "(assert (forall ((x Height) (y Height)) (=> (and (partial-order x y) (partial-order y x)) (= x y))))",
    "(assert (forall ((x Height) (y Height) (z Height)) (=> (and (partial-order x y) (partial-order y z)) (partial-order x z))))",
    "(assert (forall ((x Height) (y Height)) (! (= (height_lt x y) (and (partial-order x y) (not (= x y)))) :pattern ((height_lt x y)) :qid prelude_height_lt :skolemid skolem_prelude_height_lt)))"
]

QUAKE_MESSAGE = "[INFO] mariposa-quake"

def convert_verus_smtlib(in_file, out_file):
    lines = open(in_file, 'r').readlines()
    lines = [line.strip() for line in lines]
    new_lines = []
    new_lines.append("(set-logic ALL)")
    new_lines.append("(set-option :incremental true)")

    for line in lines:
        # Remove unsupported set-option commands
        if line.startswith('(set-option'):
            continue
        # Remove any lines with partial-order (compare to adding replacement definition)
        if "partial-order" in line:
            new_lines += _PARTIAL_ORDER_ALT
            continue
        if "(declare-datatypes () ())" in line:
            continue
        new_lines.append(line)

    with open(out_file, 'w') as f:
        for line in new_lines:
            f.write(line + '\n')
    print("[INFO] converted file: {}".format(out_file))

def __split_query_context(query_path):
    lines = open(query_path, "r").readlines()
    main_context = []
    push_indices = []
    check_sat_indices = []

    for i, line in enumerate(lines):
        if line.startswith("(push"):
            push_indices.append(i)
        if line.startswith("(check-sat"):
            check_sat_indices.append(i)
    assert len(check_sat_indices) == 1

    check_sat_index = check_sat_indices[0]

    if len(push_indices) == 0:
        # unusual case
        # take whatever command before check-sat
        main_index = check_sat_index - 1
        sub_index = main_index
    else:
        main_index = push_indices[-1]
        sub_index = main_index + 1

    # ignore everything after check-sat
    lines = lines[:check_sat_index+1]

    main_context = lines[:main_index]
    query_context = lines[sub_index:]

    assert query_context[-1].startswith("(check-sat")

    # add push/pop
    query_context.insert(0, "(push 1)\n")
    query_context.append(f"(echo \"{QUAKE_MESSAGE}\")\n")
    query_context.append("(pop 1)\n")

    return main_context, query_context

def emit_quake_query(query_path, output_path, repeat=4):
    out_file = open(output_path, "w")
    main_context, query_context = __split_query_context(query_path)
    out_file.writelines(main_context)

    for _ in range(repeat):
        out_file.write("".join(query_context))

def find_verus_procedure_name(file):
    lines = open(file).readlines()

    for line in reversed(lines):
        if line.startswith("(set-info :comment \";; Function-Def") \
            or line.startswith("(set-info :comment \";; Function-Decl-Check-Recommends") \
            or line.startswith("(set-info :comment \";; Function-Termination") \
            or line.startswith("(set-info :comment \";; Function-Recommends"):
            return line[23:-3]
    return None

class Mutation(str, Enum):
    SHUFFLE = "shuffle"
    RENAME = "rename"
    RESEED = "reseed"
    QUAKE = "quake"
    COMPOSE = "compose"
    NONE = "none"

    def __str__(self):
        return self.value
    
    @staticmethod
    def basic_mutations():
        return {Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED}

def emit_mutant_query(query_path, output_path, mutation, seed):
    log_check(query_path != output_path, "query and output should not be the same")
    log_check(mutation in {Mutation.SHUFFLE, Mutation.RENAME, Mutation.COMPOSE}, 
              f"{mutation} is not a valid mutation here")

    command = f"{MARIPOSA} -i '{query_path}' -a {mutation} -o '{output_path}' -s {seed}"
    
    if mutation == Mutation.COMPOSE:
        command += " --lower-asserts"

    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    log_check(result.returncode == 0 and os.path.exists(output_path),
                f"mariposa query mutation failed: {command}")

def format_query(query_path, output_path):
    log_check(query_path != output_path, "query and output should not be the same")
    command = f"{MARIPOSA} -i '{query_path}' -a format -o '{output_path}'"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    log_check(result.returncode == 0 and os.path.exists(output_path),
                f"mariposa query format failed: {command}")

def key_set(m):
    return set(m.keys())

def is_assertion_subset(query, subset_query):
    base = key_set(get_asserts(query))
    subset = key_set(get_asserts(subset_query))
    print(f"base: {len(base)} subset: {len(subset)}")
    log_check(len(subset) != 0, f"subset query has no asserts: {subset_query}")
    return subset.issubset(base)
