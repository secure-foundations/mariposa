import multiprocessing
from typing import Dict

from debugger.debugger import (
    DbgMode,
    Debugger,
    FastFailDebugger,
    DoubletonDebugger,
    TimeoutDebugger,
)
from debugger.strainer import StrainerStatus
from utils.analysis_utils import Categorizer, fmt_percent


class BenchViewer:
    def __init__(self, queries, mode: DbgMode):
        self.status = Categorizer()

        self.__name_hashes = dict()
        self.__reviewers: Dict[str, Debugger] = dict()
        pool = multiprocessing.Pool(8)

        if mode == DbgMode.SINGLETON:
            reviewers = pool.map(Debugger, queries)
        elif mode == DbgMode.DOUBLETON:
            reviewers = pool.map(DoubletonDebugger, queries)
        elif mode == DbgMode.FAST_FAIL:
            reviewers = pool.map(FastFailDebugger, queries)
        elif mode == DbgMode.TIMEOUT:
            reviewers = pool.map(TimeoutDebugger, queries)
        else:
            assert False

        for r in reviewers:
            self.__reviewers[r.given_query_path] = r
            self.__name_hashes[r.name_hash] = r.given_query_path
            self.status.add_item(r.status, r.given_query_path)

        self.status.finalize()

        self.fixable = set()
        self.unfixable = set()

        for q in self.status[StrainerStatus.FINISHED]:
            r = self.__reviewers[q]
            num_fixes = len(r.report.stabilized)
            if num_fixes > 0:
                self.fixable.add(q)
            else:
                self.unfixable.add(q)

    def __getitem__(self, key) -> Debugger:
        if key in self.__name_hashes:
            key = self.__name_hashes[key]
        return self.__reviewers[key]

    def __iter__(self):
        return iter(self.__reviewers)

    def items(self):
        return self.__reviewers.items()

    def keys(self):
        return self.__reviewers.keys()

    def print_stats(self):
        fixable_count = len(self.fixable)
        finished_count = len(self.status[StrainerStatus.FINISHED])
        print(
            "fixable ratio (finished):",
            fixable_count,
            "/",
            finished_count,
            f"({fmt_percent(fixable_count, finished_count, 1)})",
        )
