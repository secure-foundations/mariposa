import os, random, subprocess
from base.query_analyzer import Stability as STB, FailureType as FT
from base.solver import SolverType
from query.core_completer import CoreCompleter
from utils.local_utils import test_stability
from utils.query_utils import Mutation, emit_mutant_query
from utils.system_utils import *
from base.defs import MARIPOSA


class MutCoreBuilder:
    def __init__(
        self,
        input_query,
        output_query,
        solver,
        timeout,
        ids_available,
        restarts,
        keep_quantified=False,
    ):
        log_check(
            os.path.exists(input_query), f"input query {input_query} does not exist"
        )
        log_check(
            solver.stype == SolverType.Z3, f"only z3 solver is supported, got {solver}"
        )
        self.solver = solver

        name_hash = get_name_hash(input_query)
        self.input_query = input_query
        self.lbl_query = f"gen/{name_hash}/lbl.smt2"
        self.lbl_mut_query = f"gen/{name_hash}/lbl.mut.smt2"
        self.core_log = f"gen/{name_hash}/z3-core.log"
        self.timeout = timeout
        self.output_query = output_query
        self.clear_temp_files()
        self.ids_available = ids_available
        self.restarts = restarts
        self.keep_quantified = keep_quantified

        self.__create_label_query()

    def run(self):
        for i in range(self.restarts):
            remove_file(self.lbl_mut_query)
            remove_file(self.core_log)

            s = random.randint(0, 0xFFFFFFFFFFFFFFFF)
            emit_mutant_query(self.lbl_query, self.lbl_mut_query, Mutation.RENAME, s)

            with open(self.lbl_mut_query, "a") as f:
                f.write("(get-unsat-core)\n")

            success = self.__run_solver(seed=s)

            if success:
                log_info(f"core iteration {i}, successfully used mutant seed: {s}")
                self.__create_core_query(seed=s)
                # self.clear_temp_files()
                return True
            else:
                log_info(f"core iteration {i}, failed to use mutant seed: {s}")

        self.clear_temp_files()
        return False

    def clear_temp_files(self):
        remove_file(self.lbl_query)
        remove_file(self.lbl_mut_query)
        remove_file(self.core_log)

    def __create_label_query(self):
        remove_file(self.lbl_query)

        args = [
            MARIPOSA,
            "-i",
            self.input_query,
            "-o",
            self.lbl_query,
            "--action=label-core",
        ]

        if not self.ids_available:
            args.append("--reassign-ids")

        subprocess_run(args, check=True)

        # we do not expect labeling to fail
        log_check(os.path.exists(self.lbl_query), f"failed to create {self.lbl_query}")

    def __run_solver(self, seed):
        cf = open(self.core_log, "w+")
        start = time.time()
        args = self.solver.get_basic_command(self.lbl_mut_query, self.timeout, seed)
        subprocess.run(args, stdout=cf)
        cf.close()
        elapsed = time.time() - start
        cf = open(self.core_log, "r")
        lines = cf.readlines()
        cf.close()
        log_info(f"elapsed: {elapsed} seconds")

        if len(lines) == 0 or "unsat\n" not in lines:
            os.remove(self.core_log)
            return False
        return True

    def __create_core_query(self, seed):
        args = [
            MARIPOSA,
            "-i",
            self.lbl_query,
            "--action=reduce-core",
            f"--core-log-path={self.core_log}",
            f"-o",
            self.output_query,
        ]

        if self.keep_quantified:
            args.append("--core-keep-quantified")

        subprocess_run(args, check=True, debug=True)

        log_check(
            os.path.exists(self.output_query),
            f"failed to create core query {self.output_query}",
        )

        with open(self.output_query, "a") as f:
            f.write(f"(set-info :comment seed_{seed})\n")


class CompleteCoreBuilder(MutCoreBuilder):
    def __init__(
        self,
        input_query,
        output_query,
        solver,
        timeout,
        ids_available,
        restarts,
        keep_quantified=False,
    ):
        super().__init__(
            input_query,
            output_query,
            solver,
            timeout,
            ids_available,
            restarts,
            keep_quantified,
        )
        log_info("building core...")
        log_check(self.run(), "failed to create core query")
        log_info("testing stability...")
        ss, ft = test_stability(output_query, "debug")
        shutil.move(output_query, self.lbl_query)
        log_info("core query is {}, with failure type: {}".format(ss, ft))

        if ss == STB.UNSOLVABLE:
            if ft != FT.UNKNOWN:
                os.remove(self.lbl_query)
                exit_with("core does not seem unsolvable due to incompleteness")

            log_info("try completing core...")
            cc = CoreCompleter(
                input_query, self.lbl_query, output_query, solver, timeout
            )
            if not cc.run():
                cc.clear_temp_files()
                # keep the core query in case we need to debug?
                exit_with("failed to complete core")

            os.remove(self.lbl_query)
        else:
            shutil.move(self.lbl_query, output_query)
