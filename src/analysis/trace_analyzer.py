import os
from base.defs import MARIPOSA
from base.factory import FACT
from base.project import KnownExt, ProjectGroup
from base.query_analyzer import QueryAnalyzer
from base.project import ProjectType as PT
from base.solver import RCode, Solver
from utils.query_utils import emit_mutant_query
from utils.system_utils import subprocess_run

def parse_mutant_path(qid, query_path):
    base = query_path.split("/")[-1]
    assert base.startswith(qid)
    rest = base[len(qid):]
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
        cfg = FACT.get_config("verus")
        ana = FACT.get_analyzer("5sec")
        sol: Solver = FACT.get_solver("z3_4_12_5")
        exp = FACT.load_analysis(orig, cfg, sol, ana)
        log_dir = exp.get_log_dir(KnownExt.Z3_TRACE)

        if not os.path.exists(log_dir):
            os.makedirs(log_dir)

        # exp.print_status()
        for qid in exp.qids:
            orig_path = exp.get_path(qid)
            core_path = core.get_path(qid)
            woco_path = woco.get_path(qid)
            mutants = exp.get_mutants(qid)

            if not os.path.exists(core_path):
                continue

            trace_path = log_dir + "/" + qid + f".fail.trace"

            if not os.path.exists(trace_path):
                print(qid)
                fail_path = None
                for mutant in mutants:
                    (path, rc, et) = mutant
                    if rc == RCode.UNSAT.value:
                        continue
                    if "quake" in path:
                        continue
                    fail_path = path

                if fail_path is None:
                    continue

                mutant_path = orig_path

                if fail_path == orig_path:
                    mut = "reseed"
                    seed = None
                else:
                    mut, seed = parse_mutant_path(qid, fail_path)

                if mut != "reseed":
                    mutant_path = fail_path
                    emit_mutant_query(orig_path, mutant_path, mut, seed)

                sol.trace(mutant_path, 10, trace_path, seed)

            insts = subprocess_run([
                MARIPOSA,
                "-a" , 
                "parse-inst-z3",
                "-i",
                orig_path,
                "--z3-trace-log-path",
                trace_path
            ])[0]
            
            lines = insts.split("\n")

            qs = dict()

            for line in lines:
                line = line.split(": ")
                qtid, count = line[0], int(line[1])
                qs[qtid] = [count, False]

            for line in open(core_path).readlines():
                for qtid in qs:
                    if qs[qtid][1]:
                        continue
                    if qtid + ")" in line:
                        qs[qtid][1] = True
            
            remove_count = 0
            to_remove = set()

            for qtid in qs:
                if not qs[qtid][1]:
                    to_remove.add(":qid " + qtid + ")")
                    remove_count += 1
                if remove_count == 3:
                    break

            with open(woco_path, "w+") as woco_file:
                for line in open(orig_path).readlines():
                    if any([qtid in line for qtid in to_remove]):
                        print(f"Removing {line}")
                        continue
                    woco_file.write(line)

            print(woco_path)

            # print(original_path)
            # print(trace_path)

            # for qid, (count, core) in qs.items():
            #     print(qid, count, core)

            # break
            # print(f"\t{failed}")
            # qr.print_status(2)
            # print(exp[qid].get_status())