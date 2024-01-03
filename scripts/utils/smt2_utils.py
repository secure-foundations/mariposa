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

def get_name_hash(filename):
    import hashlib
    return hashlib.sha256(filename.encode()).hexdigest()

def count_asserts(filename):
    import subprocess, numpy as np
    cmd = r'rg -e "\(assert" -c' + f" '{filename}'"
    output = subprocess.run(cmd,
        shell=True, capture_output=True, text=True).stdout
    if output == "":
        print(f"[WARN] {filename} has no asserts")
        return np.nan
    return int(output)

# Run file with --incremental flag
_PARTIAL_ORDER_ALT = [
    "(declare-fun partial-order (Height Height) Bool)",
    "(assert (forall ((x Height)) (partial-order x x)))",
    "(assert (forall ((x Height) (y Height)) (=> (and (partial-order x y) (partial-order y x)) (= x y))))",
    "(assert (forall ((x Height) (y Height) (z Height)) (=> (and (partial-order x y) (partial-order y z)) (partial-order x z))))",
    "(assert (forall ((x Height) (y Height)) (! (= (height_lt x y) (and (partial-order x y) (not (= x y)))) :pattern ((height_lt x y)) :qid prelude_height_lt :skolemid skolem_prelude_height_lt)))"
]

def convert_single_verus_query_cvc5(in_file, out_file):
    lines = open(in_file, 'r').readlines()
    lines = [line.strip() for line in lines]
    new_lines = []
    new_lines.append("(set-logic ALL)")
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

def convert_verus_queries_cvc5(input_path, output_path):
    import os
    from utils.sys_utils import list_smt2_files, san_check

    assert input_path != output_path

    san_check(os.path.exists(input_path), 
              f"[ERROR] {input_path} does not exist")

    if os.path.exists(output_path):
        print(f"[INFO] output path {output_path} exists, remove? [Y]")
        san_check(input() == "Y", "[INFO] aborting")
        os.system(f"rm -r {output_path}")

    if os.path.isfile(input_path):
        convert_single_verus_query_cvc5(input_path, output_path)
        assert os.path.exists(output_path)
        return

    files = list_smt2_files(input_path)
    if len(files) == 0:
        print("[WARN] no files found in {}".format(input_path))
        return

    os.makedirs(output_path)

    for file in files:
        out_file = output_path  + "/" + os.path.basename(file)
        convert_single_verus_query_cvc5(file, out_file)
        assert os.path.exists(out_file)
