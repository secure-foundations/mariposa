import subprocess, sys
from analysis.expr_analyzer import ExperAnalyzer
from base.defs import MARIPOSA, SINGLE_PROJ_ROOT
from base.factory import FACT
from base.project import get_qid
from base.runner import Runner

from utils.system_utils import list_smt2_files, log_check, log_info, log_warn, reset_dir

def handle_single(args):
    in_query = args.input_query_path
    exp = args.experiment

    if exp.sum_table_exists() and args.clear_existing == False:
        log_warn(f"experiment results already exists for {SINGLE_PROJ_ROOT}")
        log_warn(f"you might want to use --clear-existing to overwrite the results.")
        ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    reset_dir(SINGLE_PROJ_ROOT, args.clear_existing)

    command = f"{MARIPOSA} -i {in_query} -o {SINGLE_PROJ_ROOT}/split.smt2 -a split --convert-comments"
    result = subprocess.run(command, shell=True, stdout=subprocess.PIPE)
    log_check(result.returncode == 0, "single mode split failed!")

    if list_smt2_files(SINGLE_PROJ_ROOT) == []:
        log_info(f"no queries were generated from {in_query}")
        sys.exit(0)

    # this is a hack to make sure qids are loaded
    exp.proj.reload()

    r = Runner(exp)
    r.run_experiment(args.clear_existing)
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)

def handle_multiple(args):
    exp = args.experiment
    
    if args.fix_missing:
        r = Runner(exp)
        r.fix_missing()
        return

    if exp.sum_table_exists() and args.clear_existing == False:
        log_warn(f"experiment results already exists for {exp.proj.sub_root}")
        ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    r = Runner(exp)
    r.run_experiment(args.clear_existing)
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
    return (exp.db_path, args.part)

def handle_info(args):
    for pg in FACT.get_project_groups():
        print(f"project group: {pg.gid}")
        for proj in pg.get_projects():
            print(f"\t{proj.ptype} ({len(proj.list_queries())})")
            exps = FACT.get_project_experiments(proj)
            for exp in exps:
                print(f"\t\t{exp.exp_name} - {exp.solver.name}")
        print("")

def handle_update(args):
    exp = args.experiment
    in_query = args.input_query_path
    proj = exp.proj
    qid = get_qid(in_query)
    log_check(qid in proj.qids, f"query {qid} does not exist in the project")

    r = Runner(exp)
    r.update_experiment([qid])
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
