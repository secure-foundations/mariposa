import os 
from configs.projects import list_smt2_files
from db_utils import *

def inst_rules():
    return f"""
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -p unsat-core
    """

class Project:
    def __init__(self, name): # example of name: d_fvbkv_z3 or s_komodo
        self.name = name
        self.inst_root = f"data/unsat_cores/{name}/inst/"
        self.core_root = f"data/unsat_cores/{name}/core/"
        self.min_assert_root = f"data/unsat_cores/{name}/min_asserts/"
        self.original_root = f"/home/yizhou7/mariposa/data/{name}_clean/"


D_FVBKV_Z3 = Project("d_fvbkv_z3")
D_KOMODO_Z3 = Project("d_komodo_z3")
D_LVBKV_Z3 = Project("d_lvbkv_z3")
FS_DICE_Z3 = Project("fs_dice_z3")
FS_VWASM_Z3 = Project("fs_vwasm_z3")
S_KOMODO = Project("s_komodo")

PROJECTS = [D_FVBKV_Z3, D_KOMODO_Z3, D_LVBKV_Z3, S_KOMODO, FS_DICE_Z3, FS_VWASM_Z3]

def instrument_queries():
    print(inst_rules())
    for project in PROJECTS:
        os.system(f"mkdir -p {project.inst_root}")
        for plain_path in list_smt2_files(project.original_root):
            inst_path = plain_path.replace(project.original_root, project.inst_root)
            print(f"build {inst_path}: instrument-query {plain_path}")

# instrument_queries()

def create_min_assert_rules():
    return f"""
rule minimize-query
    command = ./target/release/mariposa -i $in -c $core -o $out -p minimize-query
    """

def list_core_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".core"):
                file_paths.append(os.path.join(root, file))
    return file_paths

def create_min_assert_files(project):
    print(create_min_assert_rules())
    # custom output root
    os.system(f"mkdir -p {project.min_assert_root}")
    
    for core_path in list_core_files(f"{project.core_root}"):
        min_assert_path = core_path.replace("/core/", "/min_asserts/").replace(".core", ".smt2")
        inst_path = core_path.replace("/core/", "/inst/").replace(".core", ".smt2")
        print(f"build {min_assert_path}: minimize-query {inst_path} | {core_path}")
        print(f"    core = {core_path}")
    
create_min_assert_files(D_LVBKV_Z3)
