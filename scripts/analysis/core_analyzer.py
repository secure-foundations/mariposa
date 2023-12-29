from tabulate import tabulate
from typing import Dict
from tqdm import tqdm
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

from configure.project import PM, ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer
from analysis.categorizer import Categorizer, Stability
from utils.shake_utils import parse_shake_log, key_set, count_asserts, shake_partial
from utils.analyze_utils import CategorizedItems, get_cdf_pts
from utils.smt2_utils import *
from utils.cache_utils import *

CORE_BUILD_RULES = """
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-label-assert

rule create-mini-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-reduce-assert --core-file-path $core

rule format
    command = ./target/release/mariposa -i $in -o $out

rule shake
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --shake-log-path $log

rule shake-special
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --shake-log-path $log --shake-max-symbol-frequency 25

rule strip
    command = ./target/release/mariposa -i $in -o $out -m remove-unused

rule shake-partial
    command = python3 scripts/run_shake.py $out $in $log
"""

# rule create-core
#     command = python3 scripts/unsat_core_search.py create-core $in $out

# rule complete-mini-query
#     command = python3 scripts/unsat_core_search.py complete $in $hint $out > $out.log

# rule reduce-query
#     command = python3 scripts/unsat_core_search.py reduce $in $out > $out.log

# rule iterate-reduce-query
#     command = python3 scripts/unsat_core_search.py reduce $in $in > $out

# rule check-subset
#     command = python3 scripts/diff_smt.py subset-check $in $sub && touch $out

class ShakeStats:
    def __init__(self, orig_asserts, shke_asserts, shke_max_depth):
        self.orig_asserts = orig_asserts
        self.shke_asserts = shke_asserts
        self.shke_max_depth = shke_max_depth

        self.unified_asserts = np.nan
        self.unified_max_depth = np.nan
        self.missed_asserts = np.nan

class CoreQueryStatus:
    def __init__(self, qrs, sss):
        oqr = qrs[PType.ORIG]
        self.name_hash = get_name_hash(oqr.query_path)
        self.base_name = oqr.base_name

        self.qrs = qrs
        self.sss = sss

        # self.inst_path = f"gen/{self.name_hash}.inst.smt2"
        # self.fmt_path = f"cache/fmt/{self.name_hash}.fmt.smt2"
        self.shk_log_path = f"cache/shk/{self.name_hash}.shk"
        self.shk_stat_name = f"shk/{self.name_hash}.stat"

    def get_stability(self, typ):
        return self.sss[typ]

    def get_path(self, typ):
        if typ == PType.SHKF:
            return self.shk_full_path
        return self.qrs[typ].query_path

    def get_unified_query_path(self):
        css = self.get_stability(PType.CORE)

        if css is not None and css != Stability.UNSOLVABLE:
            return self.qrs[PType.CORE].query_path

        eqr = self.qrs[PType.EXTD]

        if eqr is not None:
            return self.qrs[PType.EXTD].query_path

        return None

    def get_unified_stability(self):
        css = self.get_stability(PType.CORE)

        if css is not None and css != Stability.UNSOLVABLE:
            return css

        return self.get_stability(PType.EXTD)

    def get_shake_stats(self, clear=False) -> ShakeStats:
        if has_cache(self.shk_stat_name) and not clear:
            return load_cache(self.shk_stat_name)

        stamps = parse_shake_log(self.shk_log_path)
        core = key_set(get_asserts(self.get_unified_query_path()))
        max_core_depth = 0
        core_miss = 0
        for c in core:
            if c not in stamps:
                core_miss += 1
            else:
                max_core_depth = max(max_core_depth, stamps[c])
        orig_asserts = count_asserts(self.get_path(PType.ORIG))
        stats = ShakeStats(orig_asserts, len(stamps), max(stamps.values()))

        if len(core) != 0:
            stats.unified_asserts = len(core)
            stats.unified_max_depth = max_core_depth
            stats.missed_asserts = core_miss

        save_cache(self.shk_stat_name, stats)
        return stats

    def ninja_fmt_query(self):
        return f"build {self.fmt_path}: format {self.get_path(PType.ORIG)}"

    def ninja_shk_query(self):
        return f"""build {self.shk_full_path}: shake {self.get_path(PType.ORIG)}
    log = {self.shk_log_path}
"""

    def ninja_shk_partial(self):
        log_path = self.shk_partial_path.replace(".smt2", ".shkp_log")
        return f"""build {log_path}: shake-partial {self.shk_full_path}
    log = {self.shk_log_path}
"""

    def partial_shake(self):
        log_path = self.shk_partial_path.replace(".smt2", ".shkp_log")
        # oracle = self.get_shake_stats().unified_max_depth
        # if np.isnan(oracle):
        #     oracle = fallback
        shake_partial(log_path, self.shk_full_path, self.shk_log_path)

class GroupCoreAnalyzer(GroupAnalyzer):
    def __init__(self, name, ana):
        gp = PM.load_project_group(name)
        super().__init__(gp, ana)
        self.core = self.load_stability_status(gp, PType.CORE)
        self.extd = self.load_stability_status(gp, PType.EXTD)
        self.shko = self.load_stability_status(gp, PType.SHKO)

        assert self.core.base_names() - self.orig.base_names() == set()
        assert self.extd.base_names() - self.orig.base_names() == set()

        self.qrs: Dict[str, CoreQueryStatus] = dict()

        for base_name in self.orig.base_names():
            oqr = self.orig[base_name]
            oss = self.orig.get_stability(base_name)

            cqr = self.core[base_name] if base_name in self.core else None
            css = self.core.get_stability(base_name)

            eqr = self.extd[base_name] if base_name in self.extd else None
            ess = self.extd.get_stability(base_name)

            _qrs = {PType.ORIG: oqr, 
                   PType.CORE: cqr, 
                   PType.EXTD: eqr}

            _sss = {PType.ORIG: oss,
                   PType.CORE: css, 
                   PType.EXTD: ess}

            cqs = CoreQueryStatus(_qrs, _sss)
            cqs.shk_full_path = f"data/projects/{self.group_name}/{PType.SHKF.value}/{base_name}"
            cqs.shk_partial_path = f"data/projects/{self.group_name}/{PType.SHKP.value}/{base_name}"
            self.qrs[base_name] = cqs

    def get_shake_stats(self, clear=False):
        cache_name = f"shk_sum/{self.group_name}.df"

        if has_cache(cache_name) and not clear:
            df = load_cache(cache_name)
            return df

        data = np.empty((len(self.qrs), 6))

        columns = ["orig_asserts", 
                   "shke_asserts", 
                   "shke_max_depth", 
                   "unified_asserts", 
                   "unified_max_depth", 
                   "missed_asserts"]
        index = []

        print(f"[INFO] loading shake stats for {self.group_name}")

        for i, qr in enumerate(tqdm(self.qrs.values())):
            st = qr.get_shake_stats(clear)
            data[i] = [st.orig_asserts, 
                       st.shke_asserts, 
                       st.shke_max_depth, 
                       st.unified_asserts, 
                       st.unified_max_depth, 
                       st.missed_asserts]
            index.append(qr.base_name)
        df = pd.DataFrame(data, index=index, columns=columns)
        save_cache(f"shk_sum/{self.group_name}.df", df)
        return df

    def print_status(self):
        print(f"core stability status for {self.group_name}")
        self.orig.print_stability_status()

        print("")
        unified = Stability.empty_map()
        
        for base_name, cqs in self.qrs.items():
            ss = cqs.get_unified_stability()
            if ss != None:
                unified[ss].add(base_name)
                
        unified = CategorizedItems(unified)
        
        table = [["category", "count", "percentage"]]

        for cat, cs in unified.items():
            table.append([cat, cs.count, cs.percent])

        table.append(["total", unified.total, 100])

        print(tabulate(table, headers="firstrow", tablefmt="github", floatfmt=".2f"))

    # def print_shake_completeness(self):
    #     df = self.get_shake_stats()
    #     no_cores = df.loc[np.isnan(df['missed_asserts'])].shape[0]
    #     rdf = df.loc[df['missed_asserts'] > 0]
    #     print(rdf)

    def emit_build(self):
        f = open(f"scripts/ninja/core.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")
        for cqs in self.qrs.values():
            f.write(cqs.ninja_shk_query())
            f.write("\n")
        f.close()

        f = open(f"scripts/ninja/shkp.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")
        for cqs in self.qrs.values():
            f.write(cqs.ninja_shk_partial())
            f.write("\n")
        f.close()

CORE_PROJECTS = ["d_komodo", "d_lvbkv", "d_fvbkv", "fs_dice", "fs_vwasm"]

def stat_context_retention(pname):
    if has_cache(f"ctx_ret/{pname}.df"):
        return load_cache(f"ctx_ret/{pname}.df")

    g = GroupCoreAnalyzer(pname, ana=Categorizer("default"))
    df = g.get_shake_stats()
    ratio = df.unified_asserts / df.orig_asserts * 100
    xs, ys = get_cdf_pts(ratio)
    end_idx = np.argwhere(~np.isnan(xs)).max()
    x_end, y_end = xs[end_idx], ys[end_idx]
    assert y_end >=0 and y_end <= 100
    assert x_end >= 0 and x_end <= 100
    save_cache(f"ctx_ret/{pname}.df", (xs, ys, x_end, y_end))
    return xs, ys, x_end, y_end

# def stat_shake_depth(pname):

def plot_context_retention():
    fig, ax = plt.subplots()

    for pname in CORE_PROJECTS:
        xs, ys, x_end, y_end = stat_context_retention(pname)
        p = plt.plot(xs, ys, label=pname)
        plt.plot(x_end, y_end, marker="o", color=p[0].get_color())

    # fig.suptitle("assertion counts in queries")
    plt.ylabel("cumulative percentage of queries")
    plt.xlabel("percentage of assertions (log scale) retained in unsat core (adjusted)")
    plt.title("Unsat Core (Adjusted) Context Retention")
    plt.legend()
    plt.xscale("log")
    plt.xlim(0.001, 100)
    plt.ylim(0, 100)
    plt.xticks([0.001, 0.01, 0.1, 1.0, 10, 100], ["0.001%", "0.01%", "0.1%", "1%", "10%", "100%"])
    plt.savefig("fig/context/retention_core.png", dpi=200)
    plt.close()

def plot_shake_max_depth():
    fig, ax = plt.subplots(len(CORE_PROJECTS), 1, squeeze=False)
    fig.set_figheight(7.5 * len(CORE_PROJECTS))
    fig.set_figwidth(7.5 )

    for i, pname in enumerate(CORE_PROJECTS):
        sp = ax[i][0]
        g = GroupCoreAnalyzer(pname, ana=Categorizer("default"))
        df = g.get_shake_stats()
        xs, ys = get_cdf_pts(df.unified_max_depth)
        end_idx = np.argwhere(~np.isnan(xs)).max()
        x_end, y_end = xs[end_idx], ys[end_idx]

        p = sp.plot(xs, ys, label=pname + "_core", linestyle="dashed")
        color = p[0].get_color()
        sp.plot(x_end, y_end, marker="o", color=color)

        xs, ys = get_cdf_pts(df.shke_max_depth)
        sp.plot(xs, ys, label=pname + "_full", color=color)
        x_max = xs.max()
        end_idx = np.argwhere(~np.isnan(xs)).max()
        x_end, y_end = xs[end_idx], ys[end_idx]
        sp.plot(x_end, y_end, marker="o", color=color)

        sp.set_ylabel("cumulative percentage of queries")
        sp.set_xlabel("assertion maximum shake depth")
        sp.set_ylim(0, 100)
        sp.set_xlim(left=0, right=x_max)
        sp.set_xticks(np.arange(0, x_max+1, 1))
        sp.grid(True)
        sp.legend()
        sp.set_title(f"Assertion Max Shake Depth {pname}")

    plt.savefig("fig/context/shake_max_depth.png", dpi=200)
    plt.close()

def analyze_unsat_core():
    # plot_context_retention()
    plot_shake_max_depth()
