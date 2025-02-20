import multiprocessing
import random
from typing import Dict

from debugger.debugger import (
    DbgMode,
    SingletonDebugger,
    get_debugger,
)
from debugger.strainer import StrainerStatus
from utils.analysis_utils import Categorizer, fmt_percent
from utils.system_utils import log_check, log_info


class BenchViewer:
    def __init__(self, queries, mode: DbgMode, auto_then_keep=DbgMode.AUTO):
        if auto_then_keep != DbgMode.AUTO:
            log_check(
                mode == DbgMode.AUTO,
                "auto_then_keep should only be given with auto mode first!",
            )

        self.status = Categorizer()

        self.__name_hashes = dict()
        self.__debuggers: Dict[str, SingletonDebugger] = dict()
        args = [(q, mode) for q in queries]
        random.shuffle(args)
        pool = multiprocessing.Pool(8)
        debuggers = pool.starmap(get_debugger, args)
        pool.close()
        self.modes = Categorizer()

        if auto_then_keep != DbgMode.AUTO:
            debuggers = [r for r in debuggers if r.mode == auto_then_keep]
            log_info(f"filtered by mode: {auto_then_keep} {len(debuggers)}")

        for r in debuggers:
            self.__debuggers[r.given_query_path] = r
            self.__name_hashes[r.name_hash] = r.given_query_path
            self.modes.add_item(r.mode, r.given_query_path)
            self.status.add_item(r.status, r.given_query_path)

        self.status.finalize()
        self.modes.finalize()

        self.fixable = set()
        self.unfixable = set()

        for q in self.status[StrainerStatus.FINISHED]:
            r = self.__debuggers[q]
            num_fixes = len(r.report.stabilized)
            if num_fixes > 0:
                self.fixable.add(q)
            else:
                self.unfixable.add(q)

    def collect_garbage(self):
        pool = multiprocessing.Pool(8)
        pool.map(SingletonDebugger.collect_garbage, self.__debuggers.values())

    def __getitem__(self, key) -> SingletonDebugger:
        if key in self.__name_hashes:
            key = self.__name_hashes[key]
        return self.__debuggers[key]

    def __iter__(self):
        return iter(self.__debuggers)

    def items(self):
        return self.__debuggers.items()

    def keys(self):
        return self.__debuggers.keys()

    def print_fixed(self):
        fixable_count = len(self.fixable)
        finished_count = len(self.status[StrainerStatus.FINISHED].items)
        print("fixable ratio (finished):", fixable_count, "/", finished_count)

    def get_sync_dirs(self):
        targets = []
        for q in self.fixable:
            targets += self[q].get_sync_dirs()
        return targets
