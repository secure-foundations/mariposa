import sys, os, subprocess, re, platform
from subprocess import PIPE, Popen
from os.path import exists
from configs.projects import list_smt2_files

def rules():
    return f"""
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -p unsat-core
rule get-cores
    command = ./solvers/z3-4.4.2 -T:10 $in > $out
rule minimize-query
    command = ./target/release/mariposa -i $in -c $core -o $out -p minimize-query
"""

def emit_build_commands(plain_root):
    print(rules())
    inst_root = plain_root + "_insts"
    core_root = plain_root + "_cores"
    sus_root = plain_root + "_sus"
    os.system(f"mkdir -p {inst_root}")
    os.system(f"mkdir -p {core_root}")
    os.system(f"mkdir -p {sus_root}")
    cout = 0
    for plain_path in list_smt2_files(plain_root):
        insts_path = plain_path.replace(plain_root, inst_root)
        core_path = plain_path.replace(plain_root, core_root).replace(".smt2", ".core")
        sus_path = plain_path.replace(plain_root, sus_root)
        print(f"build {insts_path}: instrument-query {plain_path}")
        print(f"build {core_path}: get-cores {insts_path}")
        print(f"build {sus_path}: minimize-query {insts_path} | {core_path}")
        print(f"    core = {core_path}")
        if cout >= 800:
            break
        cout += 1

emit_build_commands("data/d_komodo_z3_clean")
