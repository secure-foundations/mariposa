
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
            log_info(f"iteration {i}, trace result {rc}")

            if rc == RCode.UNSAT:
                break
            else:
                remove_file(output_trace)
        remove_file(mutant_query)

    log_check(os.path.exists(output_trace), f"failed to create {output_trace}")

def handle_wombo_combo_z3(input_query, output_query_path, timeout, restarts):
    count = count_lines(input_query)
    log_info(f"original query has {count} commands")

    name_hash = get_name_hash(input_query)
    iter_query = f"{GEN_ROOT}/{name_hash}.smt2"
    remove_file(iter_query)

    subprocess_run([MARIPOSA, 
            "-a", "clean", 
            "-i", input_query, 
            "-o", iter_query])
    
    count = count_lines(iter_query)
    log_info(f"cleaned query has {count} commands")

    trace_path = f"{GEN_ROOT}/{name_hash}.z3-trace"
    handle_trace_z3(input_query, trace_path, True, timeout, restarts)

    subprocess_run([MARIPOSA, 
         "-a", "inst-z3", 
         "-i", iter_query, 
         "--z3-trace-log-path", trace_path, 
         "-o", iter_query])

    count = count_lines(iter_query)
    log_info(f"instantiated query has {count} commands")

    solver = FACT.get_solver_by_name("z3_4_12_5")

    MutCoreBuilder(iter_query, solver, iter_query, timeout, False, restarts)

    count = count_lines(iter_query)
    log_info(f"cored query has {count} commands")

    subprocess_run([MARIPOSA, 
            "-a", "clean", 
            "-i", input_query, 
            "-o", iter_query])

    count = count_lines(iter_query)
    log_info(f"cleaned query has {count} commands")
    os.rename(iter_query, output_query_path)
