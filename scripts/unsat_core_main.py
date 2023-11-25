from basic_utils import *
from diff_smt import *
from configer import *
from db_utils import *
from cache_utils import *
from unsat_core_build import *
from unsat_core_stats import *
from unsat_core_plot import *
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
    # elif args.action == "oracle":
    #     func = lambda qm: qm.shake_from_oracle()
    elif args.action == "shake-unstable-oracle":
        for p in projects:
            p.shake_from_oracle()
        return
    elif args.action == "shake-clean":
        for p in projects:
            os.system(f"rm -r {p.shke.clean_dir}")
        return
    else:
        print(f"[WARN] unknown action {args.action}")
        return

    contents = []

    for p in projects:
        for qm in p.qms:
            contents.append(func(qm))

    emit_build(contents)

def handle_stats(args, projects):
    for p in projects:
        print(f"# {p.name}")
        if args.target == "missing":
            p.stat_missing()
        elif args.target == "shake-incomplete":
            stat_shake_incomplete(p.qms, args.clear_cache, args.verbose)
        elif args.target == "shake-unstable-oracle":
            p.stat_shake_oracle(args.verbose)
        elif args.target == "baseline":
            p.stat_baseline(args.verbose)
        else:
            print(f"[WARN] unknown target {args.target}")

def handle_plot(args, projects):
    if args.target == "core-retention":
        plot_core_retention(projects)
    elif args.target == "shake-retention":
        figure, axis = setup_fig(len(projects), 2)
        for i, proj in enumerate(projects):
            plot_shake_context_retention(axis[i], proj)
        plt.savefig(f"fig/context/retention_shake.png", dpi=200)
        plt.close()
    elif args.target == "shake-depth":
        figure, axis = setup_fig(len(projects), 1)
        for i, proj in enumerate(projects):
            plot_shake_max_depth(axis[i][0], proj)
        plt.savefig(f"fig/context/shake_max_depth.png", dpi=200)
        plt.close()
    elif args.target == "migration":
        for p in projects:
            plot_migration(p)
    else:
        print(f"[WARN] unknown target {args.target}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="a separate tool managing/building unsat core experiments")

    subparsers = parser.add_subparsers(dest='sub_command', help="mode to run mariposa in")

    build_parser = subparsers.add_parser('build', help='emit build script')
    build_parser.add_argument("-p", "--project", required=True, help="the target project, use 'all' to run on all projects")
    build_parser.add_argument("-a", "--action", required=True, help="the build action")
    
    stats_parser = subparsers.add_parser('stats', help='dump stats (should not change the db or persistent files)')
    stats_parser.add_argument("-p", "--project", required=True, help="the target project, use 'all' to run on all projects")
    stats_parser.add_argument("-t", "--target", required=True, help="the target stats")
    stats_parser.add_argument("-c", "--clear-cache", default=False, action='store_true', help="clear the cache")
    stats_parser.add_argument("-v", "--verbose", default=False, action='store_true', help="verbose")

    plot_parser = subparsers.add_parser('plot', help='plot stats')
    plot_parser.add_argument("-p", "--project", required=True, help="the target project, use 'all' to run on all projects")
    plot_parser.add_argument("-t", "--target", required=True, help="the target stats")

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
    elif args.sub_command == "plot":
        handle_plot(args, projects)
