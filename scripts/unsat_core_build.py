from basic_utils import *
from diff_smt import *
from configer import *
from db_utils import *
from unsat_core_search import run_z3
from cache_utils import *
from copy import deepcopy

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

        self.mini_exists = os.path.exists(self.mini_path)
        self.extd_exists = os.path.exists(self.extd_path)

        self.orig_status = orig_status
        self.mini_status = mini_status
        self.extd_status = extd_status

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
    
    def should_unify(self):
        return self.mini_status in {Stability.UNSOLVABLE, None} and self.extd_exists
    
    def get_shake_stats(self, unify=False):
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
                print(e_misses)

            data = [np.mean(o_depths), max(o_depths), o_misses,
                np.mean(m_depths), max(m_depths), m_misses,
                np.mean(e_depths), max(e_depths), e_misses]
            cache_save(data, self.shke_stat_name)

        if unify and self.should_unify():
            data[3:6] = data[6:]

        return data

    # probably not the best ...
    def shake_from_log(self, max_depth=np.inf):
        stamps = parse_stamps(self.shke_log_path)
        assert(len(stamps) != 0)
        # orig_asserts = get_asserts(self.orig_path)
        # stats = self.get_shake_stats()

        out_file = open("data/shake_unstable_fs_dice/" + self.base, "w+")
        
        for line in open(self.orig_path):
            if line.startswith("(assert "):
                nline = line.replace(" ", "").strip()
                if nline not in stamps or stamps[nline] > max_depth:
                    continue
            out_file.write(line)
        out_file.close()

    # def get_oracle_max_depth(self):
    #     return stats[4] == np.inf

    def get_shake_assert_count(self, max_depth=np.inf):
        stamps = parse_stamps(self.shke_log_path)
        assert(len(stamps) != 0)
        s_asserts = np.sum([1 for i in stamps if stamps[i] <= max_depth])
        return s_asserts

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
        self.orig_cats, self.orig_tally = load_proj_stability(self.orig, BASELINE)
        self.mini_cats, self.mini_tally = load_proj_stability(self.mini, PLAIN_UC)
        self.extd_cats, self.extd_tally = load_proj_stability(self.extd, PLAIN_UC)

        self.qms = []
        for orig_path in self.orig.list_queries():
            base = os.path.basename(orig_path)
            orig_status = find_category(base, self.orig_cats)
            mini_status = find_category(base, self.mini_cats)
            extd_status = find_category(base, self.extd_cats)
            qm = QueryCoreManager(orig_path, orig_status, mini_status, extd_status, self)
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
        # for cat in cats:
        #     oc = len(self.orig_cats[cat])
        #     mc = len(self.mini_cats[cat])
        #     ec = len(self.extd_cats[cat])

        #     ptable.append([cat, 
        #         oc, percent(oc, len(self.orig_tally)), 
        #         mc, percent(mc, len(self.orig_tally)),
        #         ec, percent(ec, len(self.orig_tally))])

        # keep = self.orig_tally - self.orig_cats[Stability.UNSOLVABLE]

        # unified = deepcopy(self.mini_cats)
        # changed = set()
        # for i in unified[Stability.UNSOLVABLE]:
        #     new_cat = find_category(i, self.extd_cats)
        #     if new_cat != None:
        #         changed.add(i)
        #         unified[new_cat].add(i)

        # unified[Stability.UNSOLVABLE] -= changed

        # for cat in cats:
        #     oc = len(self.orig_cats[cat] & keep)
        #     mc = len(self.mini_cats[cat] & keep)
        #     ec = len(unified[cat] & keep)
        #     ptable.append([cat, 
        #         oc, percent(oc, len(keep)), 
        #         mc, percent(mc, len(keep)),
        #         ec, percent(ec, len(keep))])

        # print(tabulate(ptable, headers=["", "orig", "", "mini", "", "extd", ""]))
        # print("")        

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

    def contains_query(self, query):
        return query.startswith(self.orig.clean_dir)

UNSAT_CORE_PROJECTS = {
    name: ProjectCoreManager(name) for name in UNSAT_CORE_PROJECTS_NAMES
}

if __name__ == "__main__":
    p = UNSAT_CORE_PROJECTS["fs_dice"]
    unstables = list()
    for qm in p.qms:
        if qm.orig_status == Stability.UNSTABLE:
            stats = qm.get_shake_stats()
            # print(qm.orig_status, qm.mini_status, qm.extd_status, stats[4])
            # assuming we have an oracle 
            qm.shake_from_log(5 if stats[4] == np.inf else stats[4])
            # unstables.append(qm)
            # print(qm.orig_status, qm.mini_status, qm.extd_status)
            # print("; core max: ", stats[4])
            # print("; core miss: ", stats[5])
            # print("; shake: ", s_asserts, "/", o_asserts)

    # random.seed(time.time())
    # qm = random.choice(unstables)
    # print(qm.orig_status, qm.mini_status, qm.extd_status)
    # print(qm.orig_path)

    # for p in UNSAT_CORE_PROJECTS.values():
        # contents += p.emit_shake_rules()
        # contents += p.emit_check_rules()
        # contents += p.emit_mini_rules()
        # p.emit_fix_missing()
        # pass

    # random.shuffle(contents)
    # print(BUILD_RULES)
    # for i in contents:
    #     print(i)
