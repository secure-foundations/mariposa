from base.factory import FACT
from base.project import get_qid
from base.exper_runner import Runner

from base.exper_analyzer import ExperAnalyzer
from utils.system_utils import log_check, log_warn

def handle_single(args):
    in_query = args.input_query_path
    exp = args.experiment

    if exp.is_done() and args.clear_existing == False:
        log_warn(f"experiment results already exists for {in_query}")
        log_warn(f"you might want to use --clear-existing to overwrite the results.")
        ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    Runner(exp).run_experiment(args.clear_existing)
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)

def handle_multiple(args):
    exp = args.experiment
    
    if args.fix_missing:
        Runner(exp).fix_missing()
        return

    if exp.is_done() and args.clear_existing == False:
        log_warn(f"experiment results already exists for {exp.proj.sub_root}")
        ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
        return

    Runner(exp).run_experiment(args.clear_existing)
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)
    return (exp.db_path, args.part)

def handle_info(args):
    for pg in FACT.get_project_groups():
        print(f"project group: {pg.gid}")
        for proj in pg.get_projects():
            print(f"\t{proj.ptype} ({len(proj.list_queries())})")
            exps = FACT.get_available_expers(proj)
            for exp in exps:
                print(f"\t\t{exp.exp_name} - {exp.solver.name}")
        print("")

def handle_update(args):
    exp = args.experiment
    in_query = args.input_query_path
    proj = exp.proj
    qid = get_qid(in_query)
    log_check(qid in proj.qids, f"query {qid} does not exist in the project")

    Runner(exp).update_experiment([qid])
    ExperAnalyzer(exp, args.analyzer).print_status(args.verbose)

def test_stability(input_query, exp_config):
    cfg = FACT.get_config(exp_config)
    ana = FACT.get_analyzer("60nq")
    sol = FACT.get_solver("z3_4_12_5")
    exp = FACT.get_single_exper(input_query, cfg, sol, skip_split=True, clear=True)
    Runner(exp).run_experiment(True)
    exp = ExperAnalyzer(exp, ana)
    assert len(exp.qids) == 1
    qid = exp.qids[0]
    ss = exp.get_stability(qid)
    ft = exp.get_failure_type(qid)
    # print(f"stability: {ss}, failure type: {ft}")
    return ss, ft
