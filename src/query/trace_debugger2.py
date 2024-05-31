import binascii, random
import multiprocessing
import os, subprocess, re
from typing import Dict
from base.defs import DEBUG_ROOT, MARIPOSA
from utils.query_utils import Mutation, emit_mutant_query, parse_trace
from utils.system_utils import log_check, log_info, subprocess_run
from tabulate import tabulate
from sexpdata import loads

CORE_TRIALS = 10
CORE_TIME_LIMIT_SEC = 60
TRACE_TIME_LIMIT_SEC = 10
TRACE_TRIALS = 10
PROC_COUNT = 6
QID_TABLE_LIMIT = 30


def _try_build_core(args):
    pins_path, core_dir, temp_dir, mut, s = args
    log_info(f"[build-core] trying {mut} {s}")

    mut_path = f"{temp_dir}/{mut}.{s}.smt2"
    core_log_path = f"{temp_dir}/core.{mut}.{s}.log"
    core_path = f"{core_dir}/core.{mut}.{s}.smt2"

    if mut != Mutation.RESEED:
        emit_mutant_query(pins_path, mut_path, mut, s)
    else:
        os.system(f"cp {pins_path} {mut_path}")

    with open(mut_path, "a") as f:
        f.write("(get-unsat-core)\n")

    solver_args = [
        "./bin/z3-4.12.5",
        f"-t:{CORE_TIME_LIMIT_SEC*1000}",
        "unsat_core=true",
        mut_path,
    ]

    if mut == Mutation.RESEED:
        solver_args += [f"sat.random_seed={s}", f"smt.random_seed={s}"]

    with open(core_log_path, "w+") as log_file:
        subprocess.run(solver_args, stdout=log_file)

    with open(core_log_path, "r") as log_file:
        lines = log_file.readlines()

    if len(lines) == 0 or "unsat\n" not in lines:
        os.remove(core_log_path)
        log_info(f"[build-core] failure {mut} {s}")
        return None

    args = [
        MARIPOSA,
        "-i",
        pins_path,
        "--action=reduce-core",
        f"--core-log-path={core_log_path}",
        f"-o",
        core_path,
    ]

    subprocess_run(args, check=True, debug=True)

    log_check(
        os.path.exists(core_path),
        f"failed to create core query {core_path}",
    )

    log_info(f"[build-core] success {mut} {s}")
    return core_path


def parse_solver_output(output):
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "timeout" in output:
        return "timeout"
    elif "unknown" in output:
        return "unknown"
    return "error"


def _build_trace(args):
    mut_path, trace_path, seeds = args

    solver_args = [
        "./bin/z3-4.12.5",
        f"-t:{TRACE_TIME_LIMIT_SEC*1000}",
        mut_path,
        "trace=true",
        f"trace_file_name={trace_path}",
    ]

    if seeds is not None:
        solver_args += [f"sat.random_seed={seeds}", f"smt.random_seed={seeds}"]

    stdout, stderr, elapsed = subprocess_run(solver_args, check=True, debug=True)
    res = parse_solver_output(stdout)
    os.system(f"mv {trace_path} {trace_path}.{elapsed}.{res}")
    log_info(f"[build-trace] finished {mut_path} {res} {elapsed}")


def load_quantifier_ids(query_path):
    qids = set()
    pattern = re.compile(":qid (mariposa_qid_([0-9]+))")
    for line in open(query_path).readlines():
        if ":qid mariposa_qid" in line:
            match = pattern.search(line)
            if match:
                qids.add(match.group(1))
    return qids


def print_expr(expr, depth=0):
    prefix = "  " * depth
    res = ""
    if isinstance(expr, list):
        res += "\n" + prefix + "("
        if not isinstance(expr[0], list):
            res += str(expr[0]) + " "
            expr = expr[1:]
        all_atoms = all([not isinstance(e, list) for e in expr])
        if all_atoms:
            res += " ".join([str(e) for e in expr])
            res += ")"
        else:
            for e in expr:
                res += print_expr(e, depth=depth + 1)
            res += "\n" + prefix + ")"
    else:
        res = "\n" + prefix + str(expr)
    return res


def format_print_sexpr(st):
    # print(loads(st))
    return print_expr(loads(st))

class TraceInfo:
    def __init__(self, trace_path):
        self.trace_path = trace_path

        base = os.path.basename(trace_path)
        items = base.split(".")
        self.mutation = items[0]
        self.seed = int(items[1])
        self.tag = items[2]
        assert self.tag == "core" or self.tag == "pins"
        self.time = int(items[3])
        self.rcode = items[4]

    def __str__(self):
        return self.trace_path

    def get_qids(self, pins_path):
        return parse_trace(pins_path, self.trace_path)

class CoreInfo:
    def __init__(self, core_name):
        self.core_name = core_name
        items = core_name.split(".")
        self.mutation = items[1]
        self.seed = int(items[2])
        self.trace_info = None

class TraceDebugger2:
    def __init__(self, query_path, clear):
        base_name = os.path.basename(query_path)
        # name_hash = get_name_hash(query_path)
        self.sub_root = f"{DEBUG_ROOT}{base_name}"
        self.orig_path = f"{self.sub_root}/orig.smt2"
        self.pins_path = f"{self.sub_root}/pins.smt2"
        self.core_dir = f"{self.sub_root}/cores"
        self.trace_dir = f"{self.sub_root}/traces"
        self.temp_dir = f"{self.sub_root}/temp"

        if not os.path.exists(self.sub_root):
            os.makedirs(self.sub_root)

        if not os.path.exists(self.temp_dir):
            os.makedirs(self.temp_dir)

        # elif clear:
        #     os.system(f"rm -rf {self.sub_root}")
        #     os.makedirs(self.sub_root)

        os.system(f"cp {query_path} {self.orig_path}")

        subprocess_run(
            [
                MARIPOSA,
                "-a",
                "pre-inst-z3",
                "-i",
                query_path,
                "-o",
                f"{self.pins_path}",
            ],
            check=True,
            debug=True,
        )

        self.init_cores(False)
        self.init_traces(False)

        # self.print_cores()
        self.print_traces()

        # some_core = self.pick_any_core()
        # print(some_core)

        slow_trace = self.pick_slowest_trace()
        print(slow_trace)
        self.analyze_trace(slow_trace)

    def init_cores(self, clear):
        if clear:
            os.system(f"rm -rf {self.core_dir}")
        if not os.path.exists(self.core_dir):
            os.makedirs(self.core_dir)
            self.build_cores()

        self.cores = dict()

        for core in os.listdir(self.core_dir):
            core_path = f"{self.core_dir}/{core}"
            self.cores[core_path] = CoreInfo(core)

    def build_cores(self):
        pool = multiprocessing.Pool(PROC_COUNT)
        args = []

        for mut in [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]:
            for _ in range(CORE_TRIALS):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                args.append((self.pins_path, self.core_dir, self.temp_dir, mut, s))

        random.shuffle(args)

        while len(args) > 0:
            batch, args = args[:PROC_COUNT], args[PROC_COUNT:]
            results = pool.map(_try_build_core, batch)

            if any(r is not None for r in results):
                break

        pool.close()

    def print_cores(self):
        table = []
        for _, v in self.cores.items():
            row = [v.mutation, v.seed, v.trace_info != None]
            table.append(row)
        log_info(f"listing {len(self.cores)} cores:")
        print(tabulate(table, headers=["mutation", "seed", "has trace"]))

    def init_traces(self, clear):
        if clear:
            os.system(f"rm -rf {self.trace_dir}")

        if not os.path.exists(self.trace_dir):
            os.makedirs(self.trace_dir)
            self.build_traces()

        self.traces: Dict[str, TraceInfo] = dict()

        for trace in os.listdir(self.trace_dir):
            trace_path = f"{self.trace_dir}/{trace}"
            tio = TraceInfo(trace_path)
            self.traces[trace_path] = tio
            if tio.tag == "core":
                core_path = f"{self.core_dir}/core.{tio.mutation}.{tio.seed}.smt2"
                self.cores[core_path].trace_info = tio

        log_check(len(self.traces) != 0, f"no traces found: {self.trace_dir}")
        return self.traces

    def build_traces(self):
        pool = multiprocessing.Pool(PROC_COUNT)
        args = []

        for core, cio in self.cores.items():
            trace_path = f"{self.trace_dir}/{cio.mutation}.{cio.seed}.core"
            if cio.mutation != Mutation.RESEED.value:
                s = None
            else:
                s = cio.seed
            args.append((core, trace_path, s))

        for mut in [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]:
            for _ in range(TRACE_TRIALS):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                mut_path = f"{self.temp_dir}/{mut}.{s}.smt2"
                trace_path = f"{self.trace_dir}/{mut}.{s}.pins"

                if mut != Mutation.RESEED:
                    emit_mutant_query(self.pins_path, mut_path, mut, s)
                    s = None
                else:
                    mut_path = self.pins_path

                args.append((mut_path, trace_path, s))

        random.shuffle(args)
        pool.map(_build_trace, args)
        pool.close()
        pool.join()

    def print_traces(self):
        pins_table, core_table = [], []
        for _, v in self.traces.items():
            if v.tag == "core":
                core_table.append([v.mutation, v.seed, v.time, v.rcode])
            else:
                pins_table.append([v.mutation, v.seed, v.time, v.rcode])
        log_info(f"listing pins {len(pins_table)} traces:")
        print(tabulate(pins_table, headers=["mutation", "seed", "time", "result"]))
        log_info(f"listing core {len(core_table)} traces:")
        print(tabulate(core_table, headers=["mutation", "seed", "time", "result"]))

    def pick_any_core(self):
        core_path = random.choice(list(self.cores.keys()))
        return core_path

    def pick_slowest_trace(self):
        slowest = None
        slowest_time = -1
        for _, tio in self.traces.items():
            if tio.tag == "core":
                continue
            if tio.time > slowest_time:
                slowest_time = tio.time
                slowest = tio
        return slowest

    def analyze_trace(self, trace):
        core_qids = []

        for cio in self.cores.values():
            core_qids.append(cio.trace_info.get_qids(self.pins_path))

        qids = trace.get_qids(self.pins_path)
        table = []

        for qid, count in qids.items():
            row = [qid, count]
            for a_core in core_qids:
                if qid in a_core:
                    in_core = round(a_core[qid] * 100 / count, 2)
                else:
                    # if len(remove_qids) != 3:
                    #     remove_qids.add(":qid " + qid + ")")
                    in_core = "X"
                row += [in_core]
            table.append(row)

            if len(table) > QID_TABLE_LIMIT:
                break

        headers = ["QID", "Count"] + [f"Core {i}" for i in range(len(core_qids))]
        print(tabulate(table, headers=headers, tablefmt="github"))
