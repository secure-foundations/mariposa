from basic_utils import *
from diff_smt import *
from configer import *
from db_utils import *
from unsat_core_search import run_z3
from cache_utils import *

UNSAT_CORE_PROJECTS_NAMES = {
    "d_komodo": ("d_komodo_uc", "d_komodo_uc_ext", "d_komodo_shake"),
    "d_fvbkv": ("d_fvbkv_uc", "d_fvbkv_uc_ext", "d_fvbkv_shake"),
    "d_lvbkv": ("d_lvbkv_uc", "d_lvbkv_uc_ext", "d_lvbkv_shake"),
    "fs_dice": ("fs_dice_uc", "fs_dice_uc_ext", "fs_dice_shake"),
    "fs_vwasm": ("fs_vwasm_uc", "fs_vwasm_uc_ext", "fs_vwasm_shake"),
}

CONFIG = Configer()
BASELINE = CONFIG.load_known_experiment("baseline")
PLAIN_UC = CONFIG.load_known_experiment("min_asserts")
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
    command = ./target/release/mariposa -i $in -o $out -m tree-shake > $log
"""

def stem_file_paths(items):
    new_items = {}
    for cat in Stability:
        new_items[cat] = set()
        for query in items[cat]:
            new_items[cat].add(query.split("/")[-1])
    return new_items

def load_proj_stability(proj, exp):
    ANA = Analyzer(.05, 60, .05, .95, 0.8, "cutoff")
    rows = load_sum_table(proj, Z3_4_12_2, exp)
    expected = set([os.path.basename(q) for q in proj.list_queries()])

    if rows is None:
        return dict(), expected

    items = ANA.categorize_queries(rows, tally=True)
    items = stem_file_paths(items)
    tally = items.pop(Stability.TALLY)
    # it might be ok that some experiments are missing
    # not the other way around though
    assert tally.issubset(expected)

    if tally != expected:
        print(f"[WARNING] tally mismatch in {proj.name}, maybe run fix missing?")

    return items, tally

def find_category(query, items):
    for cat in items:
        if query in items[cat]:
            return cat
    return None

def percent(a, b):
    return round(a * 100 / b, 2)

def parse_stamps(filename):
    cmds0 = dict()
    for line in open(filename):
        line = line.split("|||")
        stamp = int(line[0].strip())
        line = line[1].replace(" ", "").strip().strip()
        cmds0[line] = stamp
    return cmds0

class QueryCoreManager:
    def __init__(self, orig_path, orig_status, mini_status, proj=None):
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

        self.mini_exists = os.path.exists(self.mini_path)
        self.extd_exists = os.path.exists(self.extd_path)

        self.orig_status = orig_status
        self.mini_status = mini_status
        
        self.mini_check_path = f"gen/{self.name_hash}.mini.check"
        self.extd_check_path = f"gen/{self.name_hash}.extd.check"

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
        return f"""
build {self.extd_path}: complete-mini-query {self.orig_path} | {self.mini_path}
    hint = {self.mini_path}"""

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
        if os.path.exists(self.shke_log_path):
            return ""
        return f"""
build {self.shke_path}: shake {self.orig_path}
    log = {self.shke_log_path}"""

    def get_core_missing_reason(self):
        assert not self.mini_exists
        if self.orig_status == Stability.UNSOLVABLE:
            return "orig_unsolvable"
        return "core_export_failed"

    def get_extd_missing_reason(self):
        if not self.mini_exists:
            return self.get_core_missing_reason()

    def reduce_from_mini(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.mini_path} {self.extd_path}"

    def reduce_from_orig(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.orig_path} {self.extd_path}"
    
    def reduce_from_extd(self):
        return f"python3 scripts/unsat_core_search.py reduce {self.extd_path} {self.extd_path}"
    
    def get_shake_stats(self):
        if cache_exists(self.shke_stat_name):
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
            print(self.extd_path)
            print(self.mini_path)

            data = [np.mean(o_depths), max(o_depths), o_misses,
            np.mean(m_depths), max(m_depths), m_misses,
            np.mean(e_depths), max(e_depths), e_misses]
            cache_save(data, self.shke_stat_name)
            # print(round(np.mean(o_depths), 2), max(o_depths), o_misses)
            # print(round(np.mean(m_depths), 2), max(m_depths), m_misses)
            # print(round(np.mean(e_depths), 2), max(e_depths), e_misses)
        return data

class MissingTypes(str, Enum):
    ORIG_EXPERIMENT_MISSING = "original file present but experiment missing"
    MINI_EXPERIMENT_MISSING = "mini file present but experiment missing"
    MINI_FILE_MISSING = "mini file missing"
    MINI_EXPERIMENT_UNSOLVABLE = "mini file present but unsolvable"
    EXTENDED_FILE_MISSING = "extended file missing"

class ProjectCoreManager:
    def __init__(self, orig_name):
        self.name = orig_name
        c = Configer()
        (mini_name, extd_name, shke_name) = UNSAT_CORE_PROJECTS_NAMES[orig_name]
        self.orig = c.load_known_project(orig_name)
        self.mini = c.load_known_project(mini_name)
        self.extd = c.load_known_project(extd_name)
        self.shke = c.load_known_project(shke_name)
        orig_items, self.orig_tally = load_proj_stability(self.orig, BASELINE)
        mini_items, self.mini_tally = load_proj_stability(self.mini, PLAIN_UC)

        self.qms = []
        for orig_path in self.orig.list_queries():
            base = os.path.basename(orig_path)
            orig_status = find_category(base, orig_items)
            mini_status = find_category(base, mini_items)
            qm = QueryCoreManager(orig_path, orig_status, mini_status, self)
            self.qms.append(qm)

    def emit_check_rules(self):
        assert self.mini_tally.issubset(self.orig_tally)
        content = []
        for qm in tqdm(self.qms):
            checks = qm.emit_sanity_check()
            if checks != "":
                content.append(checks)
        return content

    def emit_shake_rules(self):
        content = []
        for qm in self.qms:
            content.append(qm.emit_shake())
        return content
    
    def emit_mini_rules(self):
        content = []
        for qm in self.qms:
            content.append(qm.emit_create_mini())
        return content

    def emit_fix_missing(self):
        missing = {k: set() for k in MissingTypes}
        extended = set()
        for qm in self.qms:
            if qm.orig_status == None:
                missing[MissingTypes.ORIG_EXPERIMENT_MISSING].add(qm)
            if qm.mini_exists and qm.mini_status == None:
                missing[MissingTypes.MINI_EXPERIMENT_MISSING].add(qm)
            if qm.mini_exists and qm.mini_status == Stability.UNSOLVABLE:
                missing[MissingTypes.MINI_EXPERIMENT_UNSOLVABLE].add(qm)
            if not qm.mini_exists:
                missing[MissingTypes.MINI_FILE_MISSING].add(qm)
            if not qm.extd_exists:
                missing[MissingTypes.EXTENDED_FILE_MISSING].add(qm)
            else:
                extended.add(qm)

        assert missing[MissingTypes.ORIG_EXPERIMENT_MISSING] == set()

        # for qm in missing[MissingTypes.MINI_EXPERIMENT_MISSING]:
        #     print(f"python3 scripts/main.py update -e {PLAIN_UC.name} -p {self.mini.name} -s {Z3_4_12_2} -q {qm.mini_path}")

        # for qm in missing[MissingTypes.MINI_FILE_MISSING]:
        #     print(qm.emit_create_mini())

        for qm in missing[MissingTypes.EXTENDED_FILE_MISSING]:
            if qm.mini_status == Stability.STABLE:
                pass
            else:
                pass
                # print(qm.orig_status, qm.mini_status)            

        print(f"total: {len(self.orig_tally)}")
        for k in missing:
            print(f"{k}: {len(missing[k])}")

    def get_stats(self):
        print(f"# {self.name}")
        # orig_unsolvable = set()
        cats = [Stability.STABLE, Stability.UNSTABLE, Stability.UNSOLVABLE, None]
        orig_cats = {cat: 0 for cat in cats}
        mini_cats = {cat: 0 for cat in cats}

        ptable = []
        patched = 0

        for qm in self.qms:
            if qm.orig_status not in orig_cats:
                orig_cats[qm.orig_status] = 0
            orig_cats[qm.orig_status] += 1
            if qm.mini_status not in mini_cats:
                mini_cats[qm.mini_status] = 0
            mini_cats[qm.mini_status] += 1
            if qm.mini_status == Stability.UNSOLVABLE \
                and qm.extd_exists:
                patched +=1

        for cat in cats:
            oc = orig_cats[cat]
            mc = mini_cats[cat]
            ptable.append([cat, oc, percent(oc, len(self.orig_tally)), mc, percent(mc, len(self.orig_tally))])
            
        print(tabulate(ptable, headers=["", "orig", "", "mini", ""]))
        print(f"patched {patched} / { mini_cats[Stability.UNSOLVABLE]}")
        print("")

    def get_patched_diff_stats(self):
        cache_path = f"patched_diff_stats_{self.name}.pkl"
        if cache_exists(cache_path):
            data = cache_load(cache_path)
        else:
            data = []
            for qm in tqdm(self.qms):
                if qm.extd_exists and qm.mini_exists:
                    e_asserts = key_set(get_asserts(qm.extd_path))
                    m_asserts = key_set(get_asserts(qm.mini_path))
                    common = len(e_asserts & m_asserts)
                    added = len(e_asserts - m_asserts)
                    subed = len(m_asserts - e_asserts)
                    data.append([len(m_asserts), len(e_asserts), common, added, subed])
            data = np.array(data)
            cache_save(data, cache_path)
        # print(data[:,3] - data[:,4])
        return data

    def get_shake_stats(self):
        for qm in tqdm(self.qms):
            qm.get_shake_stats()

    def contains_query(self, query):
        return query.startswith(self.orig.clean_dir)

UNSAT_CORE_PROJECTS = {
    name: ProjectCoreManager(name) for name in UNSAT_CORE_PROJECTS_NAMES
}

if __name__ == "__main__":
    # p = UNSAT_CORE_PROJECTS["d_komodo"]
    contents = []

    for p in UNSAT_CORE_PROJECTS.values():
        # p.get_stats()
        contents += p.emit_shake_rules()
        # contents += p.emit_check_rules()
        # contents += p.emit_mini_rules()
        # p.emit_fix_missing()
        # p.get_shake_stats()

    random.shuffle(contents)
    print(BUILD_RULES)
    for i in contents:
        print(i)
