from basic_utils import *
import os

def clean_file(file, new_folder_path):
    with open(file, 'r') as f:
        lines = f.readlines()
        lines = [line.strip() for line in lines]
        new_lines = []
        # (set-logic ALL)
        new_lines.append("(set-logic ALL)")
        for line in lines:
            # Remove unsupported set-option commands
            if line.startswith('(set-option'):
                continue
            # Remove any lines with partial-order (compare to adding replacement definition)
            if "partial-order" in line:
                continue
            if "(declare-datatypes () ())" in line:
                continue
            new_lines.append(line)
    # Write new file
    new_file = os.path.join(new_folder_path, os.path.basename(file))
    with open(new_file, 'w') as f:
        for line in new_lines:
            f.write(line + '\n')
        print("Wrote file: {}".format(new_file))

# Run file with --incremental flag
replacement = ["(declare-fun partial-order (Height Height) Bool)",
"(assert (forall ((x Height)) (partial-order x x)))",
"(assert (forall ((x Height) (y Height)) (=> (and (partial-order x y) (partial-order y x)) (= x y))))",
"(assert (forall ((x Height) (y Height) (z Height)) (=> (and (partial-order x y) (partial-order y z)) (partial-order x z))))",
"(assert (forall ((x Height) (y Height)) (! (= (height_lt x y) (and (partial-order x y) (not (= x y)))) :pattern ((height_lt x y)) :qid prelude_height_lt :skolemid skolem_prelude_height_lt)))"]

def clean_file_partial_order_fix(file, new_folder_path):
    with open(file, 'r') as f:
        lines = f.readlines()
        lines = [line.strip() for line in lines]
        new_lines = []
        # (set-logic ALL)
        new_lines.append("(set-logic ALL)")
        for line in lines:
            # Remove unsupported set-option commands
            if line.startswith('(set-option'):
                continue
            # Remove any lines with partial-order (compare to adding replacement definition)
            if "partial-order" in line:
                new_lines += replacement
                continue
            if "(declare-datatypes () ())" in line:
                continue
            new_lines.append(line)
    # Write new file
    new_file = os.path.join(new_folder_path, os.path.basename(file))
    with open(new_file, 'w') as f:
        for line in new_lines:
            f.write(line + '\n')
        print("Wrote file: {}".format(new_file))


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: python3 verus_cleanup.py <folder_path> <new_folder_path>")
        exit(1)
    folder_path = sys.argv[1]
    new_folder_path = sys.argv[2]
    if not os.path.exists(new_folder_path):
        os.makedirs(new_folder_path)
    files = list_smt2_files(folder_path)
    for file in files:
        clean_file_partial_order_fix(file, new_folder_path)
