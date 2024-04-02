
from query.core_builder import MutCoreBuilder
from utils.query_utils import Mutation, count_asserts, count_lines, emit_mutant_query
from utils.system_utils import *
import random
from base.defs import GEN_ROOT, MARIPOSA
from base.factory import FACT
from base.solver import RCode, Z3Solver

def handle_trace_z3(input_query, output_trace, search, timeout, restarts):
    solver: Z3Solver = FACT.get_solver_by_name("z3_4_12_5")

    remove_file(output_trace)

    if not search:
        rc, _ = solver.trace(input_query, timeout, output_trace)
        log_info(f"not in search mode, trace result {rc}")
    else:
        name_hash = get_name_hash(input_query)
        mutant_query = f"{GEN_ROOT}/{name_hash}.trace.mut.smt2"
        for i in range(restarts):
            remove_file(mutant_query)
            s = random.randint(0, 0xffffffffffffffff)

            emit_mutant_query(input_query, mutant_query, Mutation.SHUFFLE, s)
            rc, _ = solver.trace(mutant_query, timeout, output_trace, seeds=s)
            log_info(f"trace iteration {i}, {rc}")

            if rc == RCode.UNSAT:
                break
            else:
                remove_file(output_trace)
        remove_file(mutant_query)

    log_check(os.path.exists(output_trace), f"failed to create {output_trace}")

def handle_wombo_combo_z3(input_query, output_query_path, timeout, restarts):
    random.seed(213123)

    count = count_lines(input_query)
    log_info(f"original query has {count} commands")
    solver = FACT.get_solver_by_name("z3_4_12_5")

    name_hash = get_name_hash(input_query)
    cur_query = f"{GEN_ROOT}{name_hash}.woco.smt2"
    trace_path = f"{GEN_ROOT}/{name_hash}.z3-trace"
    remove_file(cur_query)

    subprocess_run([MARIPOSA, 
            "-a", "pre-inst-z3", 
            "-i", input_query, 
            "-o", cur_query], check=True, debug=True)

    prev_count = count_lines(cur_query)
    log_info(f"combo iteration 0, {prev_count} commands after simplification")

    for i in range(1, 2):
        MutCoreBuilder(cur_query, solver, cur_query, 10, True, restarts)
        count = count_lines(cur_query)
        log_info(f"combo iteration {i}, {count} commands after core")
        break
        # remove_file(trace_path)
        # handle_trace_z3(cur_query, trace_path, True, 10, restarts)

        # subprocess_run([MARIPOSA, 
        #     "-a", "inst-z3", 
        #     "-i", cur_query, 
        #     "--z3-trace-log-path", trace_path, 
        #     "-o", cur_query], check=True, debug=True)

        # count = count_lines(cur_query)
        # log_info(f"combo iteration {i}, {count} commands after instantiation")

        # subprocess_run([MARIPOSA, 
        #     "-a", "simp", 
        #     "-i", cur_query, 
        #     "-o", cur_query], check=True, debug=True)

        # log_info(f"combo iteration {i}, {count} commands after simplification")
        # print(prev_count, count)        
        # prev_count = count

    # os.system(f"mv {cur_query} {output_query_path}")
