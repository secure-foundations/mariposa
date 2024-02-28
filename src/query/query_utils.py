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
        print(f"[WARN] {filename} has no asserts")
        return np.nan
    return int(output)

_PARTIAL_ORDER_ALT = [
    "(declare-fun partial-order (Height Height) Bool)",
    "(assert (forall ((x Height)) (partial-order x x)))",
    "(assert (forall ((x Height) (y Height)) (=> (and (partial-order x y) (partial-order y x)) (= x y))))",
    "(assert (forall ((x Height) (y Height) (z Height)) (=> (and (partial-order x y) (partial-order y z)) (partial-order x z))))",
    "(assert (forall ((x Height) (y Height)) (! (= (height_lt x y) (and (partial-order x y) (not (= x y)))) :pattern ((height_lt x y)) :qid prelude_height_lt :skolemid skolem_prelude_height_lt)))"
]

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
    query_context.append("(echo \"[INFO] mariposa-quake\")\n")
    query_context.append("(pop 1)\n")

    return main_context, query_context

def emit_quake_query(query_path, output_path, timeout, repeat=4):
    out_file = open(output_path, "w")
    main_context, query_context = __split_query_context(query_path)
    out_file.writelines(main_context)
    query_context.insert(1, "(set-option :timeout {})\n".format(timeout * 1000))

    for _ in range(repeat):
        out_file.write("".join(query_context))
