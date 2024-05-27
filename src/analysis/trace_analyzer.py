import os
from base.defs import MARIPOSA, QUERY_WIZARD
from base.factory import FACT
from base.project import KnownExt, ProjectGroup
from base.query_analyzer import QueryAnalyzer
from base.project import ProjectType as PT
from base.solver import RCode, Solver
from utils.query_utils import emit_mutant_query
from utils.system_utils import subprocess_run
from tqdm import tqdm
from base.query_analyzer import Stability as STB


def parse_mutant_path(qid, query_path):
    base = query_path.split("/")[-1]
    assert base.startswith(qid)
    rest = base[len(qid) :]
    rest = rest.split(".")
    assert len(rest) == 4
    seed = int(rest[1])
    mutation = rest[2]
    return mutation, seed


class TraceAnalyzer:
    def __init__(self, group: ProjectGroup):
        orig = group.get_project(PT.from_str("base.z3"))
        core = group.get_project(PT.from_str("core.z3"))
        woco = group.get_project(PT.from_str("woco.z3"), build=True)
        cfg = FACT.get_config("verus_ext")
        ana = FACT.get_analyzer("5sec")
        sol: Solver = FACT.get_solver("z3_4_12_5")
        exp = FACT.load_analysis(orig, cfg, sol, ana)
        log_dir = exp.get_log_dir(KnownExt.Z3_TRACE)

        if not os.path.exists(log_dir):
            os.makedirs(log_dir)

        # exp.print_status()
        for qid in exp.stability_categories[STB.UNSTABLE]:
            orig_path = exp.get_path(qid)
            core_path = core.get_path(qid)
            woco_path = woco.get_path(qid)
            mutants = exp.get_mutants(qid)

            trace_dir = log_dir + "/" + qid

            if not os.path.exists(trace_dir):
                os.makedirs(trace_dir)

            for mutant in mutants:
                (mut_path, rc, et) = mutant
                if rc == RCode.UNSAT.value:
                    continue

                if "quake" in mut_path:
                    continue

                if mut_path == orig_path:
                    mut, seed = "reseed", None
                else:
                    mut, seed = parse_mutant_path(qid, mut_path)

                if mut != "reseed":
                    emit_mutant_query(orig_path, mut_path, mut, seed)

                trace_path = (
                    trace_dir
                    + "/"
                    + mut
                    + "."
                    + str(seed)
                    + "."
                    + str(RCode(rc))
                    + "."
                    + str(et)
                    + ".trace"
                )

                if mut == "reseed":
                    mut_path = orig_path

                subprocess_run(
                    [
                        QUERY_WIZARD,
                        "trace-z3",
                        "-i",
                        mut_path,
                        "-o",
                        trace_path,
                        "--timeout",
                        "5",
                        "--seed",
                        seed,
                    ], 
                    check=True,
                    debug=True,
                )
                
                print(trace_path)
                assert os.path.exists(trace_path)

            # print(
            #     QUERY_WIZARD,
            #     "debug-trace",
            #     "-i",
            #     orig_path,
            #     "--input-log-path",
            #     trace_dir,
            #     "--core-query-path",
            #     core_path,
            #     "-o",
            #     woco_path,
            #     ">",
            #     "doc/v_bench/" + qid + ".md",
            # )
