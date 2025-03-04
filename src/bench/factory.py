from debugger.factory import DbgMode
from debugger.options import DebugOptions
from debugger.strainer import DebugStatus
from bench.consts import *
from bench.viewer import BenchViewer


def get_mariposa_viewer() -> BenchViewer:
    options = DebugOptions()
    options.is_verus = False
    return BenchViewer(UNSTABLE_MARIPOSA, options)


def get_verus_viewer() -> BenchViewer:
    options = DebugOptions()
    options.is_verus = True
    return BenchViewer(UNSTABLE_VERUS, options)


def get_combined_viewer() -> BenchViewer:
    queries = list(UNSTABLE_MARIPOSA) + list(UNSTABLE_VERUS)
    return BenchViewer(queries, DebugOptions())
