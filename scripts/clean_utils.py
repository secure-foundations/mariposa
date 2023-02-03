import re
from tqdm import tqdm
from configs.projects import *
import time
import subprocess

PUSH_CMD = re.compile("\(push (1)?\)")
# POP_CMD = re.compile("\(pop (1)?\)")

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

remove_z3_options()

# count = 0
# for i in tqdm(list_smt2_files(D_FVBKV.clean_dirs[CVC5_1_0_3])):
#     command = f"./solvers/cvc5-1.0.3 --parse-only {i}"
#     out, err, t = subprocess_run(command, 10, debug=False, cwd=None)
#     if "Error" in out or "error" in out:
#         count += 1
#         print(i)


# import os
# from tqdm import tqdm
# from path_utils import *

# ## one time file renaming
# def clean_smtlib_queries():
#     file_paths = list_smt2_files(SMT_ALL_DIR)
#     for file_path in file_paths:
#         if ":" in file_path or "=" in file_path:
#             new_path = file_path.replace(":", "_")
#             new_path = new_path.replace("=", "_")
#             os.system(f"mv {file_path} {new_path}")

# ERROR_PATTERN = "(check-sat)\n(get-info :reason-unknown)"
# ALT_PATTERN = "(check-sat)\n(pop 1)\n"

# def clean_dafny_queries_for_z3():
#     file_paths = list_smt2_files(DFY_RAW_DIR)
#     for file_path in file_paths:
#         content = open(file_path).read()
#         out_path = file_path.replace(DFY_RAW_DIR, DFY_CLEAN_DIR, 1)
#         out_file = open(out_path, "w+")
#         index = content.find(ERROR_PATTERN)
#         if index != -1:
#             if "; Invalid" in content:
#                 content = content[:index] + ALT_PATTERN + "; Invalid\n"
#                 out_file.write(content)
#             else:
#                 assert("; Out of resource" in content)
#                 content = content[:index] + ALT_PATTERN + "; Out of resource\n"
#                 out_file.write(content)  
#         else:
#             assert("; Valid" in content)
#             index = content.find("(pop 1)")
#             assert(index != -1)
#             content = content[:index+7] + "\n; Valid\n";
#             out_file.write(content)

# DECLARE_REGEX = "(declare-sort RegEx 0)\n"
# RLIMIT_RESET = "(set-option :rlimit 0)\n"
    
# def clean_cdafny_for_cvc5():
#     file_paths = list_smt2_files(DFY_CLEAN_DIR)
#     for file_path in file_paths:
#         content = open(file_path).read()
#         out_path = file_path.replace(DFY_CLEAN_DIR, DFY_CVC5_CLEAN_DIR, 1)
#         contents = open(file_path).read()
#         contents = contents.replace(RLIMIT_RESET, "")
#         out_file = open(out_path, "w+")
#         out_file.write(DECLARE_REGEX + contents)

# if __name__ == "__main__":
#     # convert_cdafny_queries_cvc5()
#     clean_serval_queries()
