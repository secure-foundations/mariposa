from ast import Dict
import multiprocessing
import os
from analysis.core_analyzer import CoreAnalyzer
from base.factory import FACT
from base.project import KnownExt, ProjectGroup, ProjectType as PT
from proj_wizard import NINJA_BUILD_RULES
from base.query_analyzer import QueryAnalyzer, Stability as STB, FailureType as UR
from base.exper_analyzer import ExperAnalyzer
from utils.analysis_utils import *
from utils.cache_utils import *
from utils.query_utils import count_asserts, is_assertion_subset, key_set
from utils.system_utils import print_banner
from utils.shake_utils import *
import numpy as np
from tqdm import tqdm
import filecmp


def check_incomplete(oracle_path, depths):
    print(oracle_path)
    for line in open(oracle_path, "r"):
        if not line.startswith("(assert"):
            continue
        m = re.search(CID_PATTERN, line)
        assert m
        cid = str(m.group(1))
        if np.isnan(depths[cid]):
            print(line, end="")
    print("..")


def valid_max(scores):
    return max([s for s in scores if not np.isnan(s)])


class ShakeStats:
    def __init__(
        self,
        qid,
        shake_log_path,
        oracle_query_path,
    ):
        self.qid = qid
        scores = parse_shake_log(shake_log_path)

        self.max_base_depth = valid_max(scores.values())
        self.base_counts = len(scores)

        last_layer = set()

        for cid, score in scores.items():
            if np.isnan(score):
                last_layer.add(cid)

        self.default_count = self.base_counts - len(last_layer)

        if oracle_query_path is not None:
            core_cids = load_query_cids(oracle_query_path)
            core_scores = [scores[cid] for cid in core_cids.keys()]
            self.default_missing_count = len(
                last_layer.intersection(key_set(core_cids))
            )
            assert (np.nan in core_scores) == (self.default_missing_count != 0)
            self.max_core_depth = valid_max(core_scores)
            self.core_count = len(core_scores)

            self.oracle_count = 0
            for cid, score in scores.items():
                if score <= self.max_core_depth:
                    self.oracle_count += 1
        else:
            self.max_core_depth = np.nan
            self.core_count = np.nan
            self.oracle_count = np.nan
            self.default_missing_count = np.nan

    def as_list(self):
        return [
            self.qid,
            self.max_base_depth,
            self.base_counts,
            self.default_count,
            self.max_core_depth,
            self.core_count,
            self.oracle_count,
            self.default_missing_count,
        ]

def _get_shake_stats(args):
    qid, shake_log_path, oracle_query_path = args
    return ShakeStats(qid, shake_log_path, oracle_query_path).as_list()

class ShakeAnalyzer(CoreAnalyzer):
    def __init__(self, group: ProjectGroup, ana: QueryAnalyzer):
        super().__init__(group, ana)
        # self.build_shake_stats()
        # self.shake = FACT.load_default_analysis(self.p_shake)
        # self.create_shake_queries()
        # self.check_shake_perf()

    def build_shake_stats(self, freq=100):
        args = []
        shkn = self.group.get_project(PT.from_str("shkn.z3"))

        for qid, qcs in self.qids.items():
            if freq == 0:
                shake_log = shkn.get_path(qid, KnownExt.SHK_LOG)
            else:
                if freq != 100:
                    qid = f"{qid}.{freq}"
                shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)
            oracle_query_path = None
            if qcs.core_is_enabled():
                oracle_query_path = qcs.patch_path # + ".fixed"
            args += [(qid, shake_log, oracle_query_path)]

        pool = multiprocessing.Pool(6)
        stats = zip(*pool.map(_get_shake_stats, args))

        df = pd.DataFrame(stats).T

        df.columns = [
            "qid",
            "max_base_depth",
            "base_counts",
            "default_count",
            "max_core_depth",
            "core_count",
            "oracle_count",
            "default_missing_count",
        ]
        
        return df

    def debug_shake(self, freq=100):
        maybe = 0
        rrs = []
        df = self.build_shake_stats(freq)
        for qid in self.base_adj[STB.UNSTABLE].items:
            qcs = self.qids[qid]
            if freq == 0:
                shake_log = self.group.get_project(PT.from_str("shkn.z3")).get_path(qid, KnownExt.SHK_LOG)
            elif freq != 100:
                qid = f"{qid}.{freq}"
                shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)
            else:
                shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)

            df_row = df[df["qid"] == qid].iloc[0]

            oracle = df_row.max_core_depth

            if qcs.patch_path == qcs.base_path:
                oracle = int(df_row.max_base_depth / 3)
                # print("no core:", qid)
                # continue

            if df_row["default_missing_count"] != 0:
                print(f"cp {qcs.base_path} data/projs/{self.group.gid}.special/shko.z3/{qid}.smt2")
                continue

            rrs += [df_row.oracle_count / df_row.core_count]
            maybe += 1
            print(f"./src/query_wizard.py create-shake -i {qcs.base_path} --input-log {shake_log} --max-score {oracle} -o data/projs/{self.group.gid}.special/shko.z3/{qid}.smt2")

            # print(
            #     "./src/query_wizard.py debug-shake",
            #     "-i %s --core-query-path %s --input-log-path %s"
            #     % (qcs.base_path, qcs.patch_path + ".fixed", shake_log),
            # )

def load_shake_stats(gid, freq):
    cache_name = f"shake_stats_{gid}"

    if freq == 0:
        cache_name += "_naive"
    elif freq != 100:
        cache_name += f"_{freq}"

    if has_cache(cache_name):
        return load_cache(cache_name)
    
    df = ShakeAnalyzer(FACT.get_group(gid)).build_shake_stats(freq)
    save_cache(cache_name, df)

    return df

    # def check_shake_perf(self):
    #     for qid, qcs in self.qids.items():
    #         shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)
    #         # rc, tt = self.shake[qid].get_original_status()
    #         # shake_path = self.p_shake.get_path(qid)

    #         print("base:", qcs.base)
    #         print("patch:", qcs.patch)

    #         if qid not in self.shake:
    #             print("shko: TOS!!")
    #         else:
    #             print("shko:", self.shake[qid].stability)
    #             self.shake[qid].print_status(5)
    #             self.core[qid].print_status(5)

    #         print(
    #             "./src/query_wizard.py debug-shake",
    #             "-i %s --core-query-path %s --input-log-path %s"
    #             % (qcs.base_path, qcs.patch_path, shake_log),
    #         )

    #         print("")

    # def create_shake_queries(self):
    #     cats = Categorizer()

    #     for qid, qcs in self.qids.items():
    #         shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)
    #         shake_path = self.p_shake.get_path(qid)

    #         scores = parse_shake_log(shake_log)

    #         max_base_score = valid_max(scores.values())
    #         oracle = valid_max([int(max_base_score / 3.1), 1])
    #         if qcs.core_is_enabled():
    #             core_cids = load_query_cids(qcs.patch_path + ".fixed")
    #             core_scores = [scores[cid] for cid in core_cids.keys()]
    #             if np.nan in core_scores:
    #                 # print("./src/query_wizard.py debug-shake", "-i %s --core-query-path %s --input-log-path %s" % (qcs.base_path, qcs.patch_path, shake_log))
    #                 cats.add_item("shake (maybe) incomplete", qid)
    #             oracle = valid_max(core_scores)
    #         else:
    #             print("no core:", qid)
    #             cats.add_item("no core", qid)
    #         create_shake_query(qcs.base_path, shake_path, scores, oracle)

    #     cats.finalize()
    #     cats.print_status()

    # def get_shake_depth(self):
    #     cache_name = f"{self.group.gid}_shake_depth"
    #     if has_cache(cache_name):
    #         return load_cache(cache_name)
    #     depths = {}
    #     for qid, qcs in tqdm(self.qids.items()):
    #         shake_log = self.base.get_path(qid, KnownExt.SHK_LOG)
    #         # shake_path = self.p_shake.get_path(qid)
    #         scores = parse_shake_log(shake_log)
    #         if qcs.patch_path == qcs.base_path:
    #             max_core = np.nan
    #             comp = np.nan
    #         else:
    #             core_path = qcs.patch_path + ".fixed"
    #             core_cids = load_query_cids(core_path)
    #             core_scores = [scores[cid] for cid in core_cids.keys()]
    #             max_core = valid_max(core_scores)
    #             comp = 0 if np.nan in core_scores else 1
    #         max_base = valid_max(scores.values())
    #         depths[qid] = (max_core, max_base, comp)
    #     save_cache(cache_name, depths)
    #     return depths

    # def get_shake_naive_depth(self):
    #     cache_name = f"{self.group.gid}_naive_shake_depth"
    #     if has_cache(cache_name):
    #         return load_cache(cache_name)
    #     depths = {}
    #     shkn = self.group.get_project(PT.from_str("shkn.z3"))

    #     for qid, qcs in tqdm(self.qids.items()):
    #         shake_log = shkn.get_path(qid, KnownExt.SHK_LOG)
    #         # shake_path = self.p_shake.get_path(qid)
    #         scores = parse_shake_log(shake_log)
    #         if qcs.patch_path == qcs.base_path:
    #             max_core = np.nan
    #             comp = np.nan
    #         else:
    #             core_path = qcs.patch_path + ".fixed"
    #             core_cids = load_query_cids(core_path)
    #             core_scores = [scores[cid] for cid in core_cids.keys()]
    #             max_core = valid_max(core_scores)
    #             comp = 0 if np.nan in core_scores else 1
    #         max_base = valid_max(scores.values())
    #         depths[qid] = (max_core, max_base, comp)
    #     save_cache(cache_name, depths)
    #     return depths
