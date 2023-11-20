from basic_utils import *
from diff_smt import *
from configer import *
from db_utils import *
from cache_utils import *

UNSAT_CORE_PROJECTS_NAMES = {
    "d_komodo": ("d_komodo_uc", "d_komodo_uc_ext", "d_komodo_shake", "d_komodo_uc_strip"),
    "d_fvbkv": ("d_fvbkv_uc", "d_fvbkv_uc_ext", "d_fvbkv_shake"),
    "d_lvbkv": ("d_lvbkv_uc", "d_lvbkv_uc_ext", "d_lvbkv_shake"),
    "fs_dice": ("fs_dice_uc", "fs_dice_uc_ext", "fs_dice_shake", "fs_dice_uc_strip"),
    "fs_vwasm": ("fs_vwasm_uc", "fs_vwasm_uc_ext", "fs_vwasm_shake"),
}

CONFIG = Configer()
BASELINE = CONFIG.load_known_experiment("baseline")
PLAIN_UC = CONFIG.load_known_experiment("min_asserts")
REWRITE = CONFIG.load_known_experiment("rewrite")
Z3_4_12_2 = CONFIG.load_known_solver("z3_4_12_2")

BUILD_RULES = """
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-label-assert

rule create-core
    command = python3 scripts/unsat_core_search.py create-core $in $out

rule create-mini-query
    command = ./target/release/mariposa -i $in -o $out -m unsat-core-reduce-assert --core-file-path $core

rule complete-mini-query
    command = python3 scripts/unsat_core_search.py complete $in $hint $out > $out.log

rule reduce-query
    command = python3 scripts/unsat_core_search.py reduce $in $out > $out.log

rule iterate-reduce-query
    command = python3 scripts/unsat_core_search.py reduce $in $in > $out

rule check-subset
    command = python3 scripts/diff_smt.py subset-check $in $sub && touch $out

rule format
    command = ./target/release/mariposa -i $in -o $out

rule shake
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --command-score-path $log

rule shake-special
    command = ./target/release/mariposa -i $in -o $out -m tree-shake --command-score-path $log --shake-max-symbol-frequency 25

rule strip
    command = ./target/release/mariposa -i $in -o $out -m remove-unused
"""

def stem_file_paths(items):
    new_items = {}
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
    return new_items

def load_proj_stability(proj, exp):
    expected = set([os.path.basename(q) for q in proj.list_queries()])

    cat_cache_name = f"{proj.name}_{exp.name}_cats"
    if cache_exists(cat_cache_name):
        items = cache_load(cat_cache_name)
        tally = set.union(*items.values())
    else:
        ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")
        rows = load_sum_table(proj, Z3_4_12_2, exp)

        if rows is None:
            # do not cache this
            return dict(), expected

        items = ANA.categorize_queries(rows, tally=True)
        items = stem_file_paths(items)
        tally = items.pop(Stability.TALLY)

        # it might be ok that some experiments are missing
        # not the other way around though
        # for i in expected - tally:
        #     print(f"[WARNING] {i} is missing in {proj.name}")
        assert tally.issubset(expected)
        cache_save(items, cat_cache_name)

    if tally != expected:
        print(f"[WARNING] tally mismatch in {proj.name}, maybe run fix missing?")

    return items, tally

def find_category(query, items):
    for cat in items:
        if query in items[cat]:
            return cat
    return None

def print_basic_stats(items):
    tally = 0
    rows = [["category", "count", "percent"]]
    for cat in items:
        cat_count = len(items[cat])
        tally += cat_count
        if cat_count > 0:
            rows.append([cat.name, cat_count])
    for row in rows:
        if len(row) == 2:
            row.append(rd_percent_str(row[1], tally))
    rows.append(["total", tally, "100.00%"])
    print(tabulate(rows, headers="firstrow")) 

class MissingTypes(str, Enum):
    ORIG_EXP = "original file present but experiment missing"
    MINI_FILE = "mini file missing"
    MINI_EXP = "mini file present but experiment missing"
    MINI_EXP_UNSOLVABLE = "mini file present but unsolvable"
    EXTENDED_FILE = "extended file missing"
    EXTENDED_EXP = "extended file present but experiment missing"
    
class QueryCoreManager:
    def __init__(self, orig_path, orig_status, mini_status, extd_status, proj=None):
        assert os.path.exists(orig_path)
        if proj is None:
            for proj in UNSAT_CORE_PROJECTS.values():
                if proj.contains_query(orig_path):
                    self.proj = proj
                    break
        self.proj = proj
        assert self.proj is not None
        assert proj.contains_query(orig_path)

        self.orig_path = orig_path
        self.base = os.path.basename(orig_path)
        self.name_hash = get_name_hash(orig_path)
        self.core_path = f"gen/{self.name_hash}.core"
        self.inst_path = f"gen/{self.name_hash}.inst.smt2"
        self.fmt_path = f"gen/{self.name_hash}.fmt.smt2"
        self.shke_log_path = f"gen/{self.name_hash}.shk.log"
        self.shke_stat_name = f"{self.name_hash}.shk.stat"

        self.mini_path = self.proj.mini.clean_dir + "/" + self.base
        self.extd_path = self.proj.extd.clean_dir + "/" + self.base
        self.shke_path = self.proj.shke.clean_dir + "/" + self.base

        if proj.strp is not None:
            self.strp_path = self.proj.strp.clean_dir + "/" + self.base

        self.mini_exists = os.path.exists(self.mini_path)
        self.extd_exists = os.path.exists(self.extd_path)
        self.shke_exists = os.path.exists(self.shke_path)

        self.orig_status = orig_status
        self.mini_status = mini_status
        self.extd_status = extd_status

        self.mini_check_path = f"gen/{self.name_hash}.mini.check"
        self.extd_check_path = f"gen/{self.name_hash}.extd.check"

    def get_missing_types(self):
        missing = set()
        if self.orig_status == None:
            missing.add(MissingTypes.ORIG_EXP)
        if not self.mini_exists:
            missing.add(MissingTypes.MINI_FILE)
        if self.mini_exists and self.mini_status == None:
            missing.add(MissingTypes.MINI_EXP)
        if self.mini_exists and self.mini_status == Stability.UNSOLVABLE:
            missing.add(MissingTypes.MINI_EXP_UNSOLVABLE)
        if not self.extd_exists:
            missing.add(MissingTypes.EXTENDED_FILE)
        if self.extd_exists and self.extd_status == None:
            missing.add(MissingTypes.EXTENDED_EXP)
        return missing

    # this can be tried on any query
    def emit_create_mini(self):
        return f"""
build {self.inst_path}: instrument-query {self.orig_path}
build {self.core_path}: create-core {self.inst_path}
build {self.mini_path}: create-mini-query {self.inst_path} | {self.core_path}
    core = {self.core_path}"""

    # this should be used when the original query is solvable
    # but the mini query is unsolvable (i.e. the mini query is incomplete)
    def emit_complete_mini(self):
        missing_types = self.get_missing_types()

        if MissingTypes.ORIG_EXP in missing_types:
            print("[ERROR] original query has no experiment", self.base)
            exit(1)
            
        if MissingTypes.MINI_FILE in missing_types:
            print("[WARN] mini query file missing", self.base)
            return ""

        if MissingTypes.MINI_EXP in missing_types:
            print("[ERROR] mini query has no experiment", self.base)
            exit(1)

        if MissingTypes.MINI_EXP_UNSOLVABLE in missing_types:
            return f"""
build {self.extd_path}: complete-mini-query {self.orig_path} | {self.mini_path}
    hint = {self.mini_path}"""
        return ""

    def emit_expensive_sanity_check(self):
        # the original query should always have stability info
        assert self.orig_status != None

        res = ""

        # if we have a mini query, we should have its stability info
        if self.mini_exists:
            # check that a the mini is a subset of the original
            res += f"""
build {self.mini_check_path}: check-subset {self.fmt_path} | {self.mini_path} 
    sub = {self.mini_path}"""

        if self.extd_exists:
            # check that the exted query is also a subset of the original
            res += f"""
build {self.extd_check_path}: check-subset {self.fmt_path} | {self.extd_path}
    sub = {self.extd_path}"""

        if res != "":
            # check that the exted query is also a subset of the original
            res += f"""
build {self.fmt_path}: format {self.orig_path}"""

        return res

    def emit_shake(self):
        return f"""
build {self.shke_path}: shake {self.orig_path}
    log = {self.shke_log_path}"""

    def emit_strip(self):
        input_path = self.mini_path
        if self.should_unify():
            input_path = self.extd_path
        if not os.path.exists(input_path):
            return ""

        return f"""
build {self.strp_path}: strip {input_path}"""

    def reduce_from_mini(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.mini_path} {self.extd_path}"

    def reduce_from_orig(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.orig_path} {self.extd_path}"
    
    def reduce_from_extd(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.extd_path} {self.extd_path}"
    
    def should_unify(self):
        return self.mini_status in {Stability.UNSOLVABLE, None} and self.extd_exists
    
    def get_unify_path(self):
        if self.should_unify():
            return self.extd_path
        if self.mini_exists:
            return self.mini_path
        return None

    def get_shake_stats(self, unify=True, clear_cache=False):
        if cache_exists(self.shke_stat_name) and not clear_cache:
            data = cache_load(self.shke_stat_name)
        else:
            stamps = parse_stamps(self.shke_log_path)
            orig_asserts = get_asserts(self.orig_path)
            o_depths = [stamps[i] for i in orig_asserts if i in stamps]
            o_misses = len([i for i in orig_asserts if i not in stamps])

            if self.mini_exists:
                mini_asserts = get_asserts(self.mini_path)
                m_depths = [stamps[i] for i in mini_asserts if i in stamps]
                m_misses = len([i for i in mini_asserts if i not in stamps])
            else:
                m_depths = [np.inf]
                m_misses = np.inf

            if self.extd_exists:
                extd_asserts = get_asserts(self.extd_path)
                e_depths = [stamps[i] for i in extd_asserts if i in stamps]
                e_misses = len([i for i in extd_asserts if i not in stamps])
            else:
                e_depths = [np.inf]
                e_misses = np.inf

            # self.get_debug_cmds()

            data = [np.mean(o_depths), max(o_depths), o_misses,
                np.mean(m_depths), max(m_depths), m_misses,
                np.mean(e_depths), max(e_depths), e_misses]
            cache_save(data, self.shke_stat_name)

        if unify and self.should_unify():
            data[3:6] = data[6:]

        return data

    def shake_from_oracle(self, dir, fallback):
        stats = self.get_shake_stats()
        max_depth = fallback if stats[4] == np.inf else stats[4]
        output_path = dir + "/" + self.base
        shake_from_log(self.orig_path, self.shke_log_path, output_path, max_depth)

    def get_shake_assert_count(self, max_depth=np.inf):
        stamps = parse_stamps(self.shke_log_path)
        assert(len(stamps) != 0)
        s_asserts = np.sum([1 for i in stamps if stamps[i] <= max_depth])
        return s_asserts

    def get_debug_cmds(self):
        print(f"cp {self.orig_path} temp/woot.smt2")
        u_path = self.get_unify_path()
        if u_path:
            print(f"cp {u_path} temp/core.smt2")
        else:
            print("rm temp/core.smt2")
        print(f"cp {self.shke_path} temp/out.smt2")
        print(f"cp {self.shke_log_path} temp/log.txt")

class ProjectCoreManager:
    def __init__(self, orig_name):
        self.name = orig_name
        c = Configer()
        sub_names = UNSAT_CORE_PROJECTS_NAMES[orig_name]
        # mini_name, extd_name, shke_name, strp_name
        self.orig = c.load_known_project(orig_name)
        self.mini = c.load_known_project(sub_names[0])
        self.extd = c.load_known_project(sub_names[1])
        self.shke = c.load_known_project(sub_names[2])
        if len(sub_names) > 3:
            self.strp = c.load_known_project(sub_names[3])
        else:
            self.strp = None

        self.orig_cats, self.orig_tally = load_proj_stability(self.orig, BASELINE)
        self.mini_cats, self.mini_tally = load_proj_stability(self.mini, PLAIN_UC)
        self.extd_cats, self.extd_tally = load_proj_stability(self.extd, PLAIN_UC)

        self.qm_index = dict()

        self.qms = []
        for orig_path in self.orig.list_queries():
            base = os.path.basename(orig_path)
            orig_status = find_category(base, self.orig_cats)
            mini_status = find_category(base, self.mini_cats)
            extd_status = find_category(base, self.extd_cats)
            qm = QueryCoreManager(orig_path, orig_status, mini_status, extd_status, self)
            self.qms.append(qm)
            self.qm_index[qm.base] = qm

    def stat_missing(self):
        print(self.name)
        for qm in self.qms:
            missing = qm.get_missing_types()
            if len(missing) > 0:
                print(qm.base)
                for m in missing:
                    print("\t", str(m.value))

    def stat_baseline(self, verbose=False):
        # cats = self.orig_cats.keys()
        # assert cats == self.mini_cats.keys()
        print_basic_stats(self.orig_cats)

        if not verbose:
            return

        for qm in self.qms:
            if qm.orig_status == Stability.UNSTABLE:
                qm.get_debug_cmds()

    def get_unstable_qms(self):
        return [qm for qm in self.qms if qm.orig_status == Stability.UNSTABLE]

    def shake_from_oracle(self):
        proj = CONFIG.load_known_project("shake_oracle_" + self.name)

        for qm in tqdm(self.get_unstable_qms()):
            # print(qm.orig_status, qm.mini_status, qm.extd_status)
            if not qm.shke_exists:
                print("[ERROR] there are queries that do not have shake files")
                exit(1)

            qm.shake_from_oracle(proj.clean_dir + "/" + qm.base, 4)

    def stat_shake_oracle(self):
        proj = CONFIG.load_known_project("shake_oracle_" + self.name)
        cats, tally = load_proj_stability(proj, REWRITE)
        if cats == dict():
            print("[ERROR] no data for shake oracle " + self.name)
            return
        print_basic_stats(cats)

    def get_assert_counts(self, unify=False):
        if unify:
            cache_path = f"assert_counts_{self.name}_unified.pkl"
        else:
            cache_path = f"assert_counts_{self.name}.pkl"

        if cache_exists(cache_path):
            data = cache_load(cache_path)
        else:
            data = []
            for qm in tqdm(self.qms):
                o_asserts = get_assert_count(qm.orig_path)
                m_asserts = get_assert_count(qm.mini_path)
                e_asserts = get_assert_count(qm.extd_path)
                if unify and qm.should_unify():
                    m_asserts = e_asserts
                data.append([o_asserts, m_asserts, e_asserts])
            data = np.array(data)
            cache_save(data, cache_path)
        return data

    def get_query_manager(self, path):
        path = os.path.basename(path)
        return self.qm_index[path]

    def contains_query(self, query):
        return query.startswith(self.orig.clean_dir)

UNSAT_CORE_PROJECTS = {
    name: ProjectCoreManager(name) for name in UNSAT_CORE_PROJECTS_NAMES
}

# def get_shake_comp_test_qms():
#     random.seed(1234)
#     qms = []
#     for p in UNSAT_CORE_PROJECTS.values():
#         qms += random.sample(p.qms, 100)
#     return qms

if __name__ == "__main__":
    pass
