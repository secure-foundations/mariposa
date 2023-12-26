import os, shutil, subprocess
from utils.sys_utils import san_check, list_smt2_files, convert_path

from analysis.basic_analyzer import ExpAnalyzer
from execute.exp_part import ExpPart
from execute.runner import Runner

def single_mode(args):
    exp = ExpPart.single_mode_exp(args.query, args.solver)

    proj_root = exp.proj.root_dir
    dir_exists = os.path.exists(proj_root)

    if dir_exists:
        if args.clear:
            print(f"[INFO] experiment dir {proj_root} exists, removing")
            shutil.rmtree(proj_root, ignore_errors=True)
        else:
            print(f"[INFO] experiment dir {proj_root} exists")
            ExpAnalyzer(exp, args.analyzer).print_detailed_status()
            return

    os.makedirs(proj_root)

    command = f"./target/release/mariposa -i '{args.query}' --remove-debug --chop -o '{proj_root}/split.smt2'"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    print(result.stdout.decode('utf-8'), end="")
    san_check(result.returncode == 0, "[ERROR] split failed")

    r = Runner()
    r.run_project(exp, args.clear)

    ExpAnalyzer(exp, args.analyzer).print_detailed_status()

def multi_mode(args):
    exp = ExpPart(args.experiment, 
            args.project, 
            args.solver, 
            args.part)

    r = Runner()
    r.run_project(exp, args.clear)

    return (exp.db_path, args.part)

def preprocess_mode(args):
    if os.path.exists(args.out_dir):
        print(f"[WARN] output directory {args.out_dir} already exists, remove it? [Y]")
        san_check(input() == "Y", f"[INFO] aborting")
        shutil.rmtree(args.out_dir)
    os.makedirs(args.out_dir)

    queries = list_smt2_files(args.in_dir)
    print(f'[INFO] found {len(queries)} files with ".smt2" extension under {args.in_dir}')

    temp = open("preprocess.sh", "w+")
    for in_path in queries:
        out_path = convert_path(in_path, args.in_dir, args.out_dir)
        command = f"./target/release/mariposa -i '{in_path}' --chop --remove-debug -o '{out_path}'\n"
        temp.write(command)
    temp.close()
    print(f"[INFO] emitted to preprocess.sh, running using gnu parallel")
    os.system("cat preprocess.sh | parallel")
    os.system("rm preprocess.sh")