from query.core_builder import CompleteCoreBuilder
from utils.query_utils import Mutation, count_lines, emit_mutant_query
from utils.system_utils import *
import random
from base.defs import GEN_ROOT, MARIPOSA
from base.factory import FACT
from base.solver import RCode, Z3Solver
import re


def get_quantifier_count(path):
    if os.path.exists(path):
        o = subprocess_run(["rg", "-e", ":qid ", "-c", path], check=True)[0]
        return int(o)
    return "-"


def handle_trace_z3(input_query, output_trace, search, timeout, restarts):
    solver: Z3Solver = FACT.get_solver("z3_4_12_5")

    remove_file(output_trace)

    if not search:
        rc, _ = solver.trace(input_query, timeout, output_trace)
        log_info(f"not in search mode, trace result {rc}")
    else:
        name_hash = get_name_hash(input_query)
        mutant_query = f"{GEN_ROOT}/{name_hash}.trace.mut.smt2"
        for i in range(restarts):
            remove_file(mutant_query)
            s = random.randint(0, 0xFFFFFFFFFFFFFFFF)
            emit_mutant_query(input_query, mutant_query, Mutation.SHUFFLE, s)
            rc, et = solver.trace(mutant_query, timeout, output_trace, seeds=s)
            log_info(f"trace iteration {i}, {rc}, {round(et/1000, 2)}s")

            if rc == RCode.UNSAT:
                break
            else:
                remove_file(output_trace)
        remove_file(mutant_query)

    log_check(os.path.exists(output_trace), f"failed to create {output_trace}")


def handle_pre_inst_z3(input_query, output_query_path):
    count = count_lines(input_query)
    log_info(f"original query has {count} commands")
    name_hash = get_name_hash(input_query)
    cur_query = f"{GEN_ROOT}{name_hash}.pins.smt2"

    shutil.copy(input_query, cur_query)

    subprocess_run(
        [MARIPOSA, "-a", "pre-inst-z3", "-i", input_query, "-o", cur_query],
        check=True,
        debug=True,
    )

    subprocess_run(
        [MARIPOSA, "-a", "clean", "-i", cur_query, "-o", cur_query],
        check=True,
        debug=True,
    )

    count = count_lines(cur_query)
    log_info(f"combo end, {count} commands")
    os.system(f"mv {cur_query} {output_query_path}")


def handle_inst_z3(input_query, output_query, timeout, restarts):
    name_hash = get_name_hash(input_query)
    trace_path = f"{GEN_ROOT}/{name_hash}.z3-trace"
    handle_trace_z3(input_query, trace_path, True, timeout, restarts)

    subprocess_run(
        [
            MARIPOSA,
            "-a",
            "inst-z3",
            "-i",
            input_query,
            "--z3-trace-log-path",
            trace_path,
            "--max-trace-insts=3000",
            "-o",
            output_query,
        ],
        check=True,
        debug=True,
    )

    # remove the trace file if nothing went wrong?
    # remove_file(trace_path)


query_pattern = re.compile("^([0-9]+)\.smt2")


class ComboBuilder:
    def __init__(self, input_query, output_dir):
        self.input_query = input_query

        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
            shutil.copy(input_query, f"{output_dir}/0.smt2")

        self.output_dir = output_dir

        counts = dict()
        for c in list_smt2_files(output_dir):
            base = os.path.basename(c)
            m = re.match(query_pattern, base)
            if m is not None:
                qc = get_quantifier_count(c)
                counts[int(m.group(1))] = qc

        self.counts = sorted(counts.items(), key=lambda x: x[0])
        self.curr, self.c_qc = self.counts[-1]

        self.cur_file = f"{output_dir}/{self.curr}.smt2"
        self.temp_file = f"{self.output_dir}/{self.curr}.temp.smt2"
        self.next_file = f"{self.output_dir}/{self.curr + 1}.smt2"
        self.prev, self.p_qc = -1, -1

        if len(self.counts) >= 2:
            self.prev, self.p_qc = self.counts[-2]

    def run(self, trace_timeout=5, trace_restarts=10, core_timeout=65, core_restarts=5):
        if self.c_qc >= self.p_qc:
            log_info("no change in quantifiers")
            return
        log_info(f"wombo start: previous {self.prev} {self.p_qc} -> current {self.curr} {self.c_qc}")
        log_info(f"processing {self.cur_file}\t{self.c_qc}")

        handle_inst_z3(self.cur_file, self.temp_file, trace_timeout, trace_restarts)

        solver = FACT.get_solver("z3_4_12_5")

        CompleteCoreBuilder(
            self.temp_file, self.next_file, solver, core_timeout, True, core_restarts
        )
        next_qc = get_quantifier_count(self.next_file)
        log_info(f"wombo end: previous {self.curr} {self.c_qc} -> current {self.curr+1} {next_qc}")
