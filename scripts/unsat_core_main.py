from basic_utils import *
from diff_smt import *
from configer import *
from db_utils import *
from cache_utils import *
from unsat_core_build import *
from unsat_core_stats import *
import argparse

def emit_build(contents):
    random.seed(12345)
    random.shuffle(contents)

    with open("build.ninja", "w+") as f:
        f.write(BUILD_RULES)
        for i in contents:
            f.write(i)
        f.write("\n")
        f.close()
    print("build rules written to build.ninja")

def handle_build(args, projects):
    if args.action == "mini":
        func = lambda qm: qm.emit_create_mini()
    elif args.action == "complete":
        func = lambda qm: qm.emit_complete_mini()
    elif args.action == "strip":
        func = lambda qm: qm.emit_strip()
    elif args.action == "shake":
        func = lambda qm: qm.emit_shake()
    elif args.action == "oracle":
        func = lambda qm: qm.shake_from_oracle()

    contents = []

    for p in projects:
        for qm in p.qms:
            contents.append(func(qm))

    emit_build(contents)

def handle_stats(args, projects):
    if args.target == "missing":
        for p in projects:
            p.print_missing_stats()
    elif args.target == "shake-incomplete":
        for p in projects:
            stat_shake_incomplete(p.qms, args.clear_cache)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="a separate tool managing/building unsat core experiments")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    build_parser = subparsers.add_parser('build', help='emit build script')
    build_parser.add_argument("-p", "--project", required=True, help="the target project, use 'all' to run on all projects")
    build_parser.add_argument("-a", "--action", required=True, help="the build action")
    
    stats_parser = subparsers.add_parser('stats', help='dump stats (should not change the db or persistent files)')
    stats_parser.add_argument("-p", "--project", required=True, help="the target project, use 'all' to run on all projects")
    stats_parser.add_argument("-t", "--target", required=True, help="the target stats")
    stats_parser.add_argument("-c", "--clear_cache", default=False, action='store_true',help="clear the cache")

    args = parser.parse_args()

    if args.project != "all" and args.project not in UNSAT_CORE_PROJECTS:
        print(f"unknown project {args.project}")
        exit(1)

    if args.project == "all":
        projects = list(UNSAT_CORE_PROJECTS.values())
    else:
        projects = [UNSAT_CORE_PROJECTS[args.project]]

    if args.sub_command == "build":
        handle_build(args, projects)
    elif args.sub_command == "stats":
        handle_stats(args, projects)



