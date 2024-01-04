from configure.project import ProjectType as PType
from analysis.basic_analyzer import GroupAnalyzer, ExpAnalyzer
from analysis.categorizer import Stability, Categorizer
from utils.analyze_utils import print_sets_diff
from utils.cache_utils import *
from tabulate import tabulate

class RevalAnalyzer(GroupAnalyzer):
    def __init__(self, group_name, ana):
        super().__init__(group_name, ana)
        self.revl: ExpAnalyzer = self.load_stability_status(PType.REVL)
        # print_sets_diff(self.orig.base_names(), self.blot.base_names(), "orig", "blot")
        self.duplicated = self.load_duplicated_queries()

    def load_duplicated_queries(self):
        from tqdm import tqdm
        cache_path = f"dircmp/opaque_{self.group_name}"

        duplicated = load_cache(cache_path)
        if not duplicated:
            duplicated = set()
            for q in tqdm(self.orig.base_names() & self.revl.base_names()):
                orig_path = f"{self.group_path}/{PType.ORIG.value}/{q}"
                revl_path = f"{self.group_path}/{PType.REVL.value}/{q}"
                if open(orig_path).read() == open(revl_path).read():
                    duplicated.add(q)
            save_cache(cache_path, duplicated)
        return duplicated

    def print_status(self):
        print(f"[INFO] {self.group_name} original vs. reveal")
        print(f"[INFO] excluded {len(self.duplicated)} duplicated queries")
        ocasts = self.orig.get_stability_status()
        ocasts = ocasts.filter_out(self.duplicated)
        rcasts = self.revl.get_stability_status()
        rcasts = rcasts.filter_out(self.duplicated)
        ocasts.print_compare_status(rcasts, skip_empty=True,
                                    cats=[Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE], 
                                    this_name="original", that_name="reveal")

OPAQUE_PROJECTS = ["d_lvbkv"]

def analyze_reveal():
    ana = Categorizer("60sec")
    for pname in OPAQUE_PROJECTS:
        g = RevalAnalyzer(pname, ana)
        g.print_status()
        print("")
