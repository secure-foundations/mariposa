from basic_utils import *

min_dir = "/home/yizhou7/unsat_cores/s_komodo/min_asserts/"
ins_dir = "/home/yizhou7/unsat_cores/d_lvbkv_z3/inst/"

for min_path in list_all_files(min_dir):
    # check file exists 
    base = os.path.basename(min_path)
    ins_path = ins_dir + base
    # if not os.path.exists(ins_path):
    #     print(ins_path)
    last = None
    stdout, _ = run_subprocess("tail " + min_path)

    for line in stdout.split("\n"):
        if line.startswith("(assert "):
            last = line
    if not last.startswith("(assert (not") and not last.startswith("(assert (! (not"):
        print(min_path)
        # print(last)
    # assert last.startswith("(assert (! (not (=>")
    # index = last.index("unsat-cores-dump-name")
    # ident = last[index:-2]
    
    # print(os.path.basename(f))
    
