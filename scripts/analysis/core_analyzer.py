from tabulate import tabulate

from configure.project import ProjectType as PType
from analysis.basic_analyzer import ExpAnalyzer, GroupAnalyzer
from execute.exp_part import ExpPart
from analysis.categorizer import Categorizer, Stability
from utils.analyze_utils import CategorizedItems
from utils.smt2_utils import *

class CoreQueryStatus:
    def __init__(self, qrs, sss):
        oqr = qrs[PType.ORIG]
        self.name_hash = get_name_hash(oqr.query_path)
        self.base_name = oqr.base_name

        self.qrs = qrs
        self.sss = sss

        # self.inst_path = f"gen/{self.name_hash}.inst.smt2"
        # self.fmt_path = f"gen/{self.name_hash}.fmt.smt2"
        # self.shke_log_path = f"gen/{self.name_hash}.shk.log"
        # self.shke_stat_name = f"{self.name_hash}.shk.stat"

    def get_stability(self, typ):
        return self.sss[typ]

    def get_path(self, typ):
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
    
    def get_assert_counts(self):
        opath = self.get_path(PType.ORIG)
        count_asserts(opath)
        upath = self.get_unified_query_path()
        count_asserts(upath)
        return (opath, upath)

class GroupCoreAnalyzer(GroupAnalyzer):
    def __init__(self, gp):
        super().__init__(gp)
        self.core = self.load_stability_status(gp, PType.CORE)
        self.extd = self.load_stability_status(gp, PType.EXTD)

        assert self.core.base_names() - self.orig.base_names() == set()
        assert self.extd.base_names() - self.orig.base_names() == set()

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

            self.qrs[base_name] = CoreQueryStatus(_qrs, _sss)

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
