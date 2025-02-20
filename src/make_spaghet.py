#!/usr/bin/env python3

import argparse
import os
from utils.system_utils import list_smt2_files, log_info, log_warn


def main():
    parser = argparse.ArgumentParser(description="NO TOUCHE, SPAGHET!!")
    parser.add_argument(
        "-i", "--input-project-path", required=True, help="the input project path"
    )
    parser.add_argument(
        "--verus", dest="is_verus", action="store_true", help="this is a verus query"
    )
    parser.add_argument(
        "--not-verus", dest="is_verus", action="store_false", help="this is not a verus query"
    )
    parser.add_argument(
        "--max-iter",
        default=6,
        type=int,
        help="max iterations before full stability test",
    )
    args = parser.parse_args()

    if not isinstance(args.is_verus, bool):
        parser.error("must specify if this is a verus query or not")

    if args.is_verus:
        filter_cfg = "filter_quick"
        full_cfg = "verus_quick"
    else:
        filter_cfg = "filter"
        full_cfg = "default"

    project_dir = args.input_project_path

    if project_dir.endswith("/"):
        project_dir = project_dir[:-1]

    if not project_dir.endswith(".filtered/base.z3"):
        assert project_dir.endswith("/base.z3")

        exp_command = f"./src/exper_wizard.py manager -e verify --total-parts 12 -s z3_4_13_0 -i {project_dir} --clear"
        os.system(exp_command)

        filter_command = (
            f"./src/analysis_wizard.py filter -s z3_4_13_0 -i {project_dir}"
        )
        os.system(filter_command)
        filter_dir = project_dir.replace("/base.z3", ".filtered/base.z3")
    else:
        filter_dir = project_dir

    last_count = -1

    for i in range(args.max_iter):
        query_count = len(list_smt2_files(filter_dir))

        if last_count != query_count:
            last_count = query_count
        elif (query_count <= 12 and i > 4) or query_count == 0:
            break

        exp_command = f"./src/exper_wizard.py manager -e {filter_cfg} --total-parts 12 -s z3_4_13_0 -i {filter_dir} --clear"
        log_info(f"iteration {i}, current query count: {query_count}, experimenting...")
        os.system(exp_command)

        carve_command = f"./src/analysis_wizard.py carve -e {filter_cfg} -s z3_4_13_0 -i {filter_dir}"
        log_info(f"iteration {i}, current query count: {query_count}, carving...")
        os.system(carve_command)

    query_count = len(list_smt2_files(filter_dir))

    if query_count == 0:
        log_warn("no queries left!")

    log_info(f"carving done, running full stability test... on {query_count} queries")
    exp_command = f"./src/exper_wizard.py manager -e {full_cfg} --total-parts 12 -s z3_4_13_0 -i {filter_dir} --clear"
    os.system(exp_command)


if __name__ == "__main__":
    main()
