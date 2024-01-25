from typing import Dict
from tqdm import tqdm
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

from execute.exp_result import QueryExpResult
from configure.project import PM, ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer
from analysis.categorizer import Categorizer, Stability
from utils.sys_utils import san_check
from utils.shake_utils import parse_shake_log, key_set, count_asserts, load_shake_prelim, emit_shake_partial, SHAKE_DEPTH_MAGIC
from utils.analyze_utils import CategorizedItems, get_cdf_pts, tex_double_column, tex_fmt_percent
from utils.smt2_utils import *
from utils.cache_utils import *

CORE_BUILD_RULES = """
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-label-assert

rule create-mini-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-reduce-assert --core-file-path $core

rule format
    command = ./target/release/mariposa -i $in -o $out

rule z3-dump-core
    command = ./solvers/z3-4.12.2 $in -T:150 > $out

rule shake
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --shake-log-path $log

rule shake-special
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --shake-log-path $log --shake-max-symbol-frequency 25

rule strip
    command = ./target/release/mariposa -i $in -o $out -m remove-unused

rule shake-partial
    command = python3 scripts/run_shake.py partial $out $in $full $log

rule z3-trace
    command = ./solvers/z3-4.12.2 $in -T:150 trace=true trace_file_name=$out
    
rule instantiate
    command = ./target/release/mariposa -i $in --trace-log $log -o $out
"""

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
    def __init__(self, group_path, qrs, sss):
        self.group_path = group_path
        oqr = qrs[PType.ORIG]
        self.name_hash = get_name_hash(oqr.query_path)
        self.base_name = oqr.base_name

        self.qrs: Dict[PType, QueryExpResult] = qrs
        self.sss = sss

        self.inst_path = f"gen/{self.name_hash}.inst.smt2"
        self._core_path = f"gen/{self.name_hash}.core"

        # self.fmt_path = f"cache/fmt/{self.name_hash}.fmt.smt2"
        self.shk_log_path = f"cache/shk/{self.name_hash}.shk"
        self.shk_stat_name = f"shk/{self.name_hash}.stat"
        self.shkp_log_path = self.get_path(PType.SHKP).replace(".smt2", ".shkp_log")
        self.trace_path = f"cache/trace/{self.name_hash}.trace"

    def __lt__(self, other):
        return self.base_name.__lt__(other.base_name)

    def print_status(self, typ):
        if self.qrs[typ] is not None:
            self.qrs[typ].print_status()
        else:
            print(f"[INFO] no {typ} result found for {self.base_name}")
            san_check(not os.path.exists(self.get_path(typ)), "query file found but no result")

    def get_stability(self, typ):
        return self.sss[typ]

    def get_path(self, typ):
        path = f"{self.group_path}/{typ.value}/{self.base_name}"
        if typ in self.qrs and self.qrs[typ] is not None:
            assert path == self.qrs[typ].query_path
        return path

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

    def read_shake_partial_log(self):
        data = load_shake_prelim(self.shkp_log_path)
        oss = self.get_stability(PType.ORIG)

        if len(data) == 0:
            # do nothing if no depth succeeded
            return "???", oss.value

        chosen_depth = min(data.keys())

        if chosen_depth == SHAKE_DEPTH_MAGIC:
            # do nothing if the original query is the only left
            return "skip", oss.value

        return "shake", oss.value

    def generate_shake_partial(self):
        if self.get_stability(PType.ORIG) != Stability.STABLE:
            return
        sst = self.get_shake_stats()
        chosen = sst.unified_max_depth
        if np.isnan(sst.unified_max_depth):
            data = load_shake_prelim(self.shkp_log_path)
            fast_depth = 8
            fast_time = 1e10
            for i, v in data.items():
                if v < fast_time:
                    fast_depth = i
                    fast_time = v
            chosen = fast_depth
    
        # data = load_shake_prelim(self.shkp_log_path)

        # if len(data) == 0:
        #     # do nothing if no depth succeeded
        #     return

        # chosen_depth = min(data.keys())

        # if chosen_depth == SHAKE_DEPTH_MAGIC:
        #     # do nothing if the original query is the only one left
        #     return

        emit_shake_partial(self.get_path(PType.SHKP), 
                           self.get_path(PType.SHKF), 
                           self.shk_log_path, 
                           chosen)

    def ninja_fmt_query(self):
        return f"build {self.fmt_path}: format {self.get_path(PType.ORIG)}"

    def ninja_create_core(self):
        return f"""build {self.inst_path}: instrument-query {self.get_path(PType.ORIG)}

build {self._core_path}: z3-dump-core {self.inst_path}

build {self.get_path(PType.CORE)}: create-mini-query {self.inst_path} | {self._core_path}
    core = {self._core_path}
"""

    def ninja_create_trace(self):
        if self.get_unified_query_path() is None:
            return ""
        if self.get_unified_stability() != Stability.UNSTABLE:
            return ""

        return f"""build {self.trace_path}: z3-trace {self.get_unified_query_path()} 

build {self.get_path(PType.QF)}: instantiate {self.get_unified_query_path()} | {self.trace_path}
    log = {self.trace_path}
"""

    def ninja_shk_query(self):
        return f"""build {self.get_path(PType.SHKF)}: shake {self.get_path(PType.ORIG)}
    log = {self.shk_log_path}
"""

    def ninja_shk_query_special(self):
        return f"""build {self.get_path(PType.SHKF)}: shake-special {self.get_path(PType.ORIG)}
    log = {self.shk_log_path}
"""

    def ninja_shk_partial(self):
        return f"""build {self.shkp_log_path}: shake-partial {self.get_path(PType.ORIG)}
    full = {self.get_path(PType.SHKF)}
    log = {self.shk_log_path}
"""

    def shake_oracle(self):
        sst = self.get_shake_stats()
        chosen = sst.unified_max_depth

        if np.isnan(sst.unified_max_depth):
            return
        # data = load_shake_prelim(self.shkp_log_path)
        # fast_depth = 8
        # fast_time = 1e10
        # for i, v in data.items():
        #     if v < fast_time:
        #         fast_depth = i
        #         fast_time = v
        # chosen = fast_depth
        # print(data)
        # print(f"[INFO] {qr.base_name} no unified max depth, chosen {chosen}")

        emit_shake_partial(self.get_path(PType.SHKO), 
                           self.get_path(PType.SHKF), 
                           self.shk_log_path, 
                           chosen)

def maybe_add_query_result(_qrs, _sss, base_name, other, typ):
    if base_name in other:
        _qrs[typ] = other[base_name]
        _sss[typ] = other.get_stability(base_name)
    else:
        _qrs[typ] = None
        _sss[typ] = None

class GroupCoreAnalyzer(GroupAnalyzer):
    def __init__(self, group_name, ana):
        super().__init__(group_name, ana)
        self.core = self.load_stability_status(PType.CORE)
        self.extd = self.load_stability_status(PType.EXTD)
        self.shko = self.load_stability_status(PType.SHKO)
        # self.shkp = self.load_stability_status(PType.SHKP)

        # for sub in [self.core, self.extd, self.shkp]:
        for sub in [self.core, self.extd]:
            if sub is None: continue
            assert sub.base_names() - self.orig.base_names() == set()

        self.qrs: Dict[str, CoreQueryStatus] = dict()

        assert len(self.orig.base_names()) != 0

        for base_name in self.orig.base_names():
            _qrs = dict()
            _sss = dict()

            maybe_add_query_result(_qrs, _sss, base_name, self.orig, PType.ORIG)
            maybe_add_query_result(_qrs, _sss, base_name, self.core, PType.CORE)
            maybe_add_query_result(_qrs, _sss, base_name, self.extd, PType.EXTD)
            maybe_add_query_result(_qrs, _sss, base_name, self.shko, PType.SHKO)
            # maybe_add_query_result(_qrs, _sss, base_name, self.shkp, PType.SHKP)

            cqs = CoreQueryStatus(self.group_path, _qrs, _sss)
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

    def get_unified_stability_status(self):
        unified = CategorizedItems()

        for base_name, cqs in self.qrs.items():
            ss = cqs.get_unified_stability()
            # if cqs.get_stability(PType.ORIG) == Stability.UNSOLVABLE:
            #     continue
            if ss is not None:
                unified.add_item(ss, base_name)
            else:
                unified.add_item(cqs.get_stability(PType.ORIG), base_name)

        missing = self.orig.base_names() - unified.tally
        for base_name in missing:
            unified.add_item("missing", base_name)
            assert False
        unified.finalize()
        return unified

    def print_status(self):
        print(f"[INFO] {self.group_name} original vs. core")
        print(f"[INFO] analyzer {self.ana.name}")

        original = self.orig.get_stability_status()
        unified = self.get_unified_stability_status()
        
        original.print_compare_status(unified, 
                                    # cats=[Stability.STABLE, Stability.UNSTABLE],
                                    skip_empty=True,
                                    this_name="adjusted", that_name="unified")

        migration = original.get_migration_status(unified)
        data = dict()
        tally = [""]
        cats = [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]
        for c in cats:
            print(f"[INFO] adjusted {c} mitigation")
            # migration[c].print_status()
            tally += [migration[c].total, ""]
            row = []
            for c2 in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
               row += [migration[c][c2]]
                # print(f"[INFO] {c} -> {c2} {migration[c][c2].percent}")
            data[c] = row
        df = pd.DataFrame(data, index=["stable", "unstable", "unsolvable"])
        # df = df.transpose()
        table = []
        from tabulate import tabulate
        for cat in cats:
            r = df.loc[cat]
            row = [str(cat)]
            for i in r:
                row += [i.count, tex_fmt_percent(i.percent)]
            table.append(row)
        header = ["category", "stable", "", "unstable", "", "unsolvable", ""]
        table = [tally] + table
        print(tabulate(table, headers=header, tablefmt="latex_raw"))

    def analyze_oracle(self):
        adjusted = CategorizedItems()
        for base_name, qr in self.qrs.items():
            st = qr.get_stability(PType.SHKO)
            if st is None:
                st = qr.get_stability(PType.ORIG)
            adjusted.add_item(st, base_name)
        adjusted.finalize()
        scores = get_stability_scores(self.orig.get_stability_status(), adjusted)
        print(scores)

    def generate_shake_partial(self):
        for cqs in self.qrs.values():
            cqs.generate_shake_partial()

    def analyze_partial(self):
        oqrs = self.orig.get_stability_status()
        sqrs = self.shkp.get_stability_status()
        oqrs.print_compare_status(sqrs, 
            cats=[Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE],
            skip_empty=True,
            this_name="original", that_name="partial")

        migration = oqrs.get_migration_status(sqrs)
        for c in migration:
            print(f"[INFO] original {c} mitigation")
            migration[c].print_status()

    def print_shake_completeness(self):
        # ocats = self.orig.get_stability_status()
        # for q in ocats[Stability.UNSTABLE]:
        missed = 0
        counts = 0
        for qr in tqdm(self.qrs.values()):
            counts = counts + 1
            st = qr.get_shake_stats()
            missed_asserts = st.missed_asserts
            if missed_asserts != 0 and not np.isnan(missed_asserts):
                missed += 1
        print(f"[INFO] {missed} / {counts} queries missed")

    def generate_shake_oracle(self):
        for qr in self.qrs.values():
            qr.shake_oracle()

    def plot_shake_max_depth(self, sp):
        df = self.get_shake_stats()
        pname = self.group_name
        color = "black"
        # color = PROJECT_COLORS[pname]

        xs, ys = get_cdf_pts(df.shke_max_depth)
        sp.plot(xs, ys, label="Original Query", color=color)
        x_max = xs.max()
        # end_idx = np.argwhere(~np.isnan(xs)).max()
        # x_end, y_end = xs[end_idx], ys[end_idx]
        # sp.plot(x_end, y_end, marker="o", color=color)
        
        xs, ys = get_cdf_pts(df.unified_max_depth)
        sp.plot(xs, ys, label="Core Query", linestyle="dashed", color=color)

        end_idx = np.argwhere(~np.isnan(xs)).max()
        x_end, y_end = xs[end_idx], ys[end_idx]
        sp.plot(x_end, y_end, marker="o", fillstyle='none', color=color, markersize=4)

        # offset = ys[np.argmax(xs > 0)]
        # sp.plot(0, offset, marker="o", color=color, markersize=4)
        # sp.text(0.24, offset-1, "%.2f" % offset + "\%", horizontalalignment='left', verticalalignment='top')
        
        xs, ys = get_cdf_pts(df.shke_max_depth - df.unified_max_depth)
        sp.plot(xs, ys,  label="Reducible Difference", color=color, linestyle="dotted")
        end_idx = np.argwhere(~np.isnan(xs)).max()

        xs[np.isnan(xs)] = np.inf
        print(np.percentile(xs, 10))

        x_end, y_end = xs[end_idx], ys[end_idx]
        sp.plot(x_end, y_end, marker="o", fillstyle='none', color=color, markersize=4)

        sp.set_ylabel("Cumulative Percentage (\%) of Queries")
        sp.set_xlabel("Query Maximum Shake Depth")
        sp.set_ylim(0, 100)
        sp.set_xlim(left=0, right=x_max)
        sp.set_xticks(np.arange(0, x_max+1, 1))
        sp.grid(True)
        sp.legend()

    def emit_build(self):
        import random
        qrs = list(self.qrs.values())
        random.shuffle(qrs)
        
        f = open(f"scripts/ninja/core.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")

        for cqs in qrs:
            f.write(cqs.ninja_create_core())
            f.write("\n")
        f.close()

        f = open(f"scripts/ninja/inst.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")

        for cqs in qrs:
            f.write(cqs.ninja_create_trace())
            f.write("\n")
        f.close()

        f = open(f"scripts/ninja/shkf.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")

        for cqs in qrs:
            if self.group_name == "fs_dice":
                f.write(cqs.ninja_shk_query_special())
            else:
                f.write(cqs.ninja_shk_query())
            f.write("\n")
        f.close()

        f = open(f"scripts/ninja/shkp.{self.group_name}.build.ninja", "w")
        f.write(CORE_BUILD_RULES)
        f.write("\n")
        for cqs in qrs:
            f.write(cqs.ninja_shk_partial())
            f.write("\n")
        f.close()

CORE_PROJECTS = ["d_komodo", "d_lvbkv", "d_fvbkv", "fs_dice", "fs_vwasm"]
CORE_PROJECTS_VERUS = ["v_ironfleet", "v_mimalloc", "v_noderep", "v_pagetable", "v_pmemlog"]

PROJECT_LABELS = {
    "d_komodo": r"Komodo$_{D}$",
    "s_komodo": r"Komodo$_S$",
    "d_fvbkv": r"VeriBetrKV$_{D}$",
    "d_lvbkv": r"VeriBetrKV$_{L}$",
    "fs_dice": r"DICE$^\star_F$",
    "fs_vwasm": r"vWasm$_F$",
    "v_ironfleet": r"IronFleet$_V$",
    "v_mimalloc": r"Mimalloc$_V$",
    "v_noderep": r"NodeRep$_V$",
    "v_pagetable": r"PageTable$_V$",
    "v_pmemlog": r"PMemLog$_V$",
    "total": "Total",
} 

PROJECT_COLORS = {
    "d_komodo": "#FFAA33",
    "d_fvbkv": "#800080",
    "d_lvbkv": "#808000",
    "fs_vwasm": "#708090",
    "fs_dice":  "#FF4500",
    "v_ironfleet": "#4682B4",
    "v_mimalloc": "#800000",
    "v_noderep": "#DAA520",
    "v_pagetable": "#191970",
    "v_pmemlog": "#008B8B",
}

plt.rcParams['text.usetex'] = True
plt.rcParams["font.family"] = "serif"
plt.rcParams["font.size"] = 14

def stat_context_retention(pname):
    # if has_cache(f"ctx_ret/{pname}.df"):
    #     return load_cache(f"ctx_ret/{pname}.df")
    g = GroupCoreAnalyzer(pname, ana=Categorizer("60sec"))
    df = g.get_shake_stats()
    ratio = df.unified_asserts / df.orig_asserts * 100
    ratio[np.isnan(ratio)] = 100
    xs, ys = get_cdf_pts(ratio)
    # end_idx = np.argwhere(~np.isnan(xs)).max()
    end_idx = len(xs) - 1
    x_end, y_end = xs[end_idx], ys[end_idx]
    assert y_end >=0 and y_end <= 100
    assert x_end >= 0 and x_end <= 100
    save_cache(f"ctx_ret/{pname}.df", (xs, ys, x_end, y_end))
    return xs, ys, x_end, y_end

def plot_context_retention(projects, ana):
    fig, ax = plt.subplots(1, 1, squeeze=False)
    fig.set_size_inches(5, 5)

    sp = ax[0][0]

    for pname in projects:
        g = GroupCoreAnalyzer(pname, ana)
        color = PROJECT_COLORS[pname]
        df = g.get_shake_stats()
        df.orig_asserts
        xs, ys = get_cdf_pts(df.orig_asserts)
        sp.plot(xs, ys, label=PROJECT_LABELS[pname], color=color, linewidth=1.5)
        
        med = np.percentile(xs, 50)
        sp.plot(med, 50, marker="o", color=color, markersize=4)

        if pname in {"fs_dice", "fs_vwasm", "d_komodo", "v_mimalloc"}:
            lbl = f'{int(med):,}'
            sp.text(med*1.1, 50, s=lbl, horizontalalignment='left', verticalalignment='top')
        if pname in {"v_pmemlog"}:
            lbl = f'{int(med):,}'
            sp.text(med*0.9, 50, s=lbl, horizontalalignment='right', verticalalignment='top')

    sp.set_xlim(1e1, 1e5)
    sp.set_ylim(0, 100)
    sp.set_yticks([0, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100])
    sp.set_xscale("log")

    sp.legend()
    sp.grid(True)
    sp.set_xlabel("Orginal Query Assertion Count (log scale)")
    sp.set_ylabel("Cumulative Percentage (\%) of Queries")
    plt.tight_layout()

    if projects == CORE_PROJECTS:
        plt.savefig("fig/context/original_ctx_size.pdf")
    else:
        assert projects == CORE_PROJECTS_VERUS
        plt.savefig("fig/context/original_ctx_size_verus.pdf")

    plt.close()

    fig, ax = plt.subplots(1, 1, squeeze=False)
    fig.set_size_inches(5, 5)

    sp = ax[0][0]

    for pname in projects:
        xs, ys, x_end, y_end = stat_context_retention(pname)
        color = PROJECT_COLORS[pname]
        sp.plot(xs, ys, label=PROJECT_LABELS[pname], color=color, linewidth=1.5)
        # sp.plot(x_end*1.05, y_end, marker="o", fillstyle='none', color=color, markersize=4)
        # xs[np.isnan(xs)] = np.inf

        st, ed = np.percentile(xs, 50), np.percentile(xs, 90)
        print(100 - st, pname)
        # print(f"%.2f %.2f %s" % (st, ed, pname))
        sp.plot(st, 50, color=color, marker="o",  markersize=4)
        # sp.plot(ed, 90, color=color=color, marker="o",  markersize=4)

        if pname in {"fs_dice", "fs_vwasm", "d_komodo", "v_pmemlog"}:
            lbl = "%.2f" % (st) + "\%"
            sp.text(st*1.1, 50, s=lbl, horizontalalignment='left', verticalalignment='top')
        if pname in {"v_mimalloc"}:
            lbl = "%.2f" % (st) + "\%"
            sp.text(st*0.9, 50, s=lbl, horizontalalignment='right', verticalalignment='top')

    sp.set_xlim(0.01, 100)
    sp.set_ylim(0, 100)
    sp.set_xticks([0.01, 0.1, 1, 10, 100])
    sp.set_yticks([0, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100])
    sp.set_xscale("log")
    sp.legend()
    sp.grid(True)
    sp.set_xlabel("Relevance Ratio (log scale)")

    plt.tight_layout()

    if projects == CORE_PROJECTS:
        plt.savefig("fig/context/retention_core.pdf")
    else:
        assert projects == CORE_PROJECTS_VERUS
        plt.savefig("fig/context/retention_core_verus.pdf")

    plt.close()

def tabulate_stability_change(data):
    print(r"\toprule")

    row = [""]
    for p in data:
        row.append(tex_double_column(PROJECT_LABELS[p]))
    print(" & ".join(row) + r"\\")

    row = [""]
    for p in data:
        count = f'{data[p]["total"]:,}'
        row.append(tex_double_column(count))
    print(" & ".join(row) + r"\\")

    sep = ""
    for i in range(1, len(data)+1):
        sep += "\cmidrule(r){%d-%d}"% (i*2, i*2 + 1)
    print(sep)

    for (s, c) in zip([Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE],
        ["Stable Ratio (\%)", "Unstable Ratio (\%)", "Unsolvable Ratio (\%)"]):
        row = [c]
        for pname in data:
            o, c = data[pname][s]
            row += [tex_fmt_percent(o), tex_fmt_percent(c - o, signed=True)]
        print(" & ".join(row) + r"\\")

    print(sep)

    row = ["$P1$"]
    for p in data:
        score = "%.1f" % (data[p]["p1"])
        row.append(tex_double_column(score))
    print(" & ".join(row) + r"\\")

    row = ["$P2$"]
    for p in data:
        score = "%.1f" % (data[p]["p2"])
        row.append(tex_double_column(score))
    print(" & ".join(row) + r"\\")
    print(r"\bottomrule")

def get_stability_scores(prev: CategorizedItems, curr: CategorizedItems):
    assert prev.tally == curr.tally
    p1 = len(prev[Stability.STABLE].items & curr[Stability.STABLE].items) / len(prev[Stability.STABLE].items) * 100
    p2 = len(prev[Stability.UNSTABLE].items & curr[Stability.STABLE].items) / len(prev[Stability.UNSTABLE].items) * 100

    scores = {"p1": p1, "p2": p2}

    for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
        scores[cat.value] = (prev[cat].percent, curr[cat].percent)

    scores["total"] = prev.total
    return scores

def tabulate_core_stability_change_projects(ana):
    data = dict()
    orig_total = CategorizedItems()
    unified_total = CategorizedItems()
    
    for pname in CORE_PROJECTS:
        g = GroupCoreAnalyzer(pname, ana=ana)
        original = g.orig.get_stability_status()
        unified = g.get_unified_stability_status()
        data[pname] = get_stability_scores(original, unified)

        for cat in [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE]:
            for base_name in original[cat]:
                orig_total.add_item(cat, pname + base_name)
            for base_name in unified[cat]:
                unified_total.add_item(cat, pname + base_name)

    orig_total.finalize()
    unified_total.finalize()
    data["total"] = get_stability_scores(orig_total, unified_total)

    tabulate_stability_change(data)

def plot_shake_max_depth_overall(ana):
    fig, ax = plt.subplots(1, 1, squeeze=False)
    fig.set_size_inches(5, 5)

    sp0 = ax[0][0]
    colors = []

    if has_cache("shake_max_depth") and False:
        all_data = load_cache("shake_max_depth")
    else:
        all_data = []
        for pname in CORE_PROJECTS:
            g = GroupCoreAnalyzer(pname, ana=ana)
            color = PROJECT_COLORS[pname]
            df = g.get_shake_stats()
            all_data.append(df.shke_max_depth)
            xs = df.unified_max_depth
            adjust = xs[~np.isnan(xs)]
            all_data.append(adjust)        
        save_cache("shake_max_depth", all_data)

    hatches = []
    labels = []
    for pname in CORE_PROJECTS:
        color = PROJECT_COLORS[pname]
        colors += [color, color]
        hatches += ["", "///"]
        labels += [PROJECT_LABELS[pname], ""]

    bp = sp0.boxplot(all_data, showfliers=True, patch_artist=True,
                flierprops=dict(markersize=2, marker='.'),
                medianprops=dict(color="black"))

    # import matplotlib.patches as mpatches
    # patch = mpatches.PathPatch(path, facecolor='r', alpha=0.5)

    b0, b1 = bp["boxes"][0], bp["boxes"][1]
    b0.set_facecolor("white")
    b1.set_facecolor("white")
    b1.set_hatch("///")

    sp0.legend([b0, b1,], ['Original Query', 'Core Query'])

    for i, box in enumerate(bp["boxes"]):
        color = colors[i]
        hatch = hatches[i]
        box.set_facecolor(color)
        box.set_edgecolor('black')
        box.set_hatch(hatch)
        # box.set_linewidth(1.5)

    sp0.set_yticks(np.arange(0, 21, 1), ["%d" % (i) if i % 2 == 0 else "" for i in range(0, 21, 1)])
    
    # for i in range(0, len(bp["boxes"]), 2):
    #     sp0.plot([i+1.5, i+1.5], [0, 20], linestyle="dashed", color="black")

    sp0.vlines(np.arange(1.5, len(CORE_PROJECTS)*2+1, 2), 0-1, 0.2-1, color="black")
    sp0.set_xticks(np.arange(1.5, len(CORE_PROJECTS)*2+1, 1), labels, 
                   ha="center")

    sp0.set_ylim(-1, 21)
    sp0.grid(axis='y')
    
    plt.tick_params(
    axis='x',          # changes apply to the x-axis
    which='both',      # both major and minor ticks are affected
    bottom=False,      # ticks along the bottom edge are off
    top=False,         # ticks along the top edge are off
    ) 
    
    sp0.set_ylabel("Maximum Shake Depth")
    plt.tight_layout()
    
    plt.savefig("fig/context/shake_max_depth.png", dpi=200)
    plt.close()

def plot_shake_max_depth_project(pname):
    g = GroupCoreAnalyzer(pname, ana=Categorizer("60sec"))
    fig, ax = plt.subplots(1, 1, squeeze=False)
    fig.set_size_inches(5, 5)
    sp = ax[0][0]
    g.plot_shake_max_depth(sp)
    plt.tight_layout()  
    plt.savefig(f"fig/context/shake_max_depth_{pname}.png", dpi=200)

# def analyze_oracle():
#     row = []
#     total = 0
#     total_sb = 0    

#     for pname in CORE_PROJECTS:
#         g = GroupCoreAnalyzer(pname, ana=Categorizer("60sec"))
#         original = g.orig.get_stability_status()
#         cats = g.shko.get_stability_status()
#         # print(pname)
#         rt = cats[Stability.STABLE].percent
#         us = len(original[Stability.UNSTABLE])
#         sb = len(original[Stability.UNSTABLE].items & cats[Stability.STABLE].items)
        
#         total += us
#         total_sb += sb
#         row += ["%.1f" % rt]
#     print(total_sb, total)
#     print(row)
#     # g.generate_shake_oracle()

def analyze_unsat_core():
    ana = Categorizer("60sec")
    # plot_context_retention(CORE_PROJECTS, ana)
    # plot_shake_max_depth() 
    # tabulate_core_stability_change_projects(ana)
    # plot_shake_max_depth_overall()
    # plot_shake_max_depth_project("d_lvbkv")

    g = GroupCoreAnalyzer("fs_dice", ana=ana)
    # g.generate_shake_oracle()
    # g.print_shake_completeness()
    g.analyze_oracle()
    # g.plot_shake_max_depth(sp)
    # g.emit_build()
    return

    for pname in CORE_PROJECTS:
        g = GroupCoreAnalyzer(pname, ana=ana)
        g.generate_shake_oracle()
        # g.print_status()
        # g.read_shake_partial_log()
        # g.generate_shake_partial()
        # g.analyze_partial()
        # g.emit_build()
