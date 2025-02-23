#!/usr/bin/env python3

import argparse
import os
from utils.system_utils import list_smt2_files, log_info, log_warn


def get_exp_command(project_dir, cfg, local):
    if local:
        return f"./src/exper_wizard.py multiple -e {cfg} -s z3_4_13_0 -i {project_dir} --clear"

    return f"./src/exper_wizard.py manager -e {cfg} --total-parts 12 -s z3_4_13_0 -i {project_dir} --clear"


def main():
    parser = argparse.ArgumentParser(description="NO TOUCHE, SPAGHET!!")
    parser.add_argument(
        "-i", "--input-project-path", required=True, help="the input project path"
    )
    parser.add_argument(
        "--verus", dest="is_verus", action="store_true", help="this is a verus query"
    )
    parser.add_argument(
        "--not-verus",
        dest="is_verus",
        action="store_false",
        help="this is not a verus query",
    )
    parser.set_defaults(is_verus=None)
    parser.add_argument(
        "--max-iter",
        default=8,
        type=int,
        help="max iterations before full stability test",
    )
    parser.add_argument(
        "--local",
        action="store_true",
        dest="is_local",
        help="only use the local machine",
    )
    parser.add_argument(
        "--cluster",
        dest="is_local",
        action="store_false",
        help="use the cluster",
    )
    parser.set_defaults(is_local=None)

    args = parser.parse_args()

    if not isinstance(args.is_verus, bool):
        parser.error("must specify if this is a verus project or not")

    if not isinstance(args.is_local, bool):
        parser.error("must specify to run it locally or on the cluster")

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

        exp_command = get_exp_command(project_dir, "verify", args.is_local)
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
        elif (query_count <= 12 and i >= 6) or query_count == 0:
            break

        exp_command = get_exp_command(filter_dir, filter_cfg, args.is_local)
        log_info(f"iteration {i}, current query count: {query_count}, experimenting...")
        os.system(exp_command)

        carve_command = f"./src/analysis_wizard.py carve -e {filter_cfg} -s z3_4_13_0 -i {filter_dir}"
        log_info(f"iteration {i}, current query count: {query_count}, carving...")
        os.system(carve_command)

    query_count = len(list_smt2_files(filter_dir))

    if query_count == 0:
        log_warn("no queries left!")

    log_info(f"carving done, running full stability test... on {query_count} queries")
    exp_command = get_exp_command(filter_dir, full_cfg, args.is_local)
    os.system(exp_command)


if __name__ == "__main__":
    main()
