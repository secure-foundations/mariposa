import multiprocessing
import random
from typing import Dict

from debugger.debugger_base import BaseDebugger
from debugger.factory import (
    DbgMode,
    get_debugger,
)
from debugger.options import DebugOptions
from debugger.strainer import DebugStatus
from utils.analysis_utils import Categorizer
from utils.system_utils import log_check, log_info
from utils.cache_utils import *
from copy import deepcopy


class BenchViewer:
    def __init__(self, queries, options: DebugOptions, auto_then_keep=DbgMode.AUTO):
        if auto_then_keep != DbgMode.AUTO:
            log_check(
                options.mode == DbgMode.AUTO,
                "auto_then_keep should only be given with auto mode first!",
            )

        # we cannot build with Pool anyways ...
        options.build_proof = False

        self.status = Categorizer()
        self.__name_hashes = dict()
        self.__debuggers: Dict[str, BaseDebugger] = dict()
        args = [(q, deepcopy(options)) for q in queries]
        random.shuffle(args)
        pool = multiprocessing.Pool(8)
        debuggers = pool.starmap(get_debugger, args)
        pool.close()
        self.modes = Categorizer()

        if auto_then_keep != DbgMode.AUTO:
            debuggers = [r for r in debuggers if r.mode == auto_then_keep]
            log_info(
                f"filtered by mode: {auto_then_keep}, debuggers left: {len(debuggers)}/{len(queries)}"
            )

        for r in debuggers:
            self.__debuggers[r.given_query_path] = r
            self.__name_hashes[r.name_hash] = r.given_query_path
            self.modes.add_item(r.mode, r.given_query_path)
            self.status.add_item(r.status, r.given_query_path)

        self.status.finalize()
        self.modes.finalize()

    def collect_garbage(self):
        pool = multiprocessing.Pool(8)
        pool.map(BaseDebugger.collect_garbage, self.__debuggers.values())
        pool.close()

    def __getitem__(self, key) -> BaseDebugger:
        if key in self.__name_hashes:
            key = self.__name_hashes[key]
        return self.__debuggers[key]

    def __iter__(self):
        return iter(self.__debuggers)

    def items(self):
        return self.__debuggers.items()

    def keys(self):
        return self.__debuggers.keys()

    def get_finished(self):
        assert self.status[DebugStatus.FINISHED_RAW].items == set()
        return (
            self.status[DebugStatus.FIX_FOUND].items
            | self.status[DebugStatus.FIX_NOT_FOUND].items
        )

    def get_sync_dirs(self):
        targets = []
        for q in (
            self.status[DebugStatus.FINISHED_RAW].items
            | self.status[DebugStatus.FIX_FOUND].items
            | self.status[DebugStatus.FIX_NOT_FOUND].items
        ):
            targets += self[q].get_sync_dirs()
        return targets

    def break_down_modes(self):
        return self.modes.analyze_migration(self.status)

    def build_query_stats(self, clear=False):
        pool = multiprocessing.Pool(8)
        args = [(dbg, clear) for dbg in self.__debuggers.values()]
        pool.starmap(BaseDebugger.build_query_stats, args)
        pool.close()

if __name__ == "__main__":
    pass
