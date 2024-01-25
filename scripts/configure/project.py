import os, random, enum, re
from utils.cache_utils import load_cache, has_cache, save_cache
from tqdm import tqdm
from utils.smt2_utils import *
from utils.sys_utils import *
from tabulate import tabulate

class ProjectType(str, enum.Enum):
    ORIG = "original"
    CORE = "unsat_core"
    EXTD = "unsat_core_ext"
    SHKF = "shake_full"
    SHKO = "shake_oracle"
    SHKP = "shake_partial"
    BLOT = "bloat"
    REVL = "reveal"
    INST = "inst"
    INSN = "inst_nl"
    INSR = "inst_rc"
    QF = "qf"
    NLE = "nle"

    ORIG_CVC = "original_cvc"
    BLOT_CVC = "bloat_cvc"
    INST_CVC = "inst_cvc"

    @classmethod
    def from_str(cls, s):
        for k in cls:
            if k.value == s:
                return k
        return None

    def __str__(self):
        return super().__str__()

    @classmethod
    def has(cls, item):
        return cls.from_str(item) in cls.__members__.values()

class Partition:
    def __init__(self, id, num):
        self.id = id
        self.num = num

    def __str__(self):
        if self.is_whole():
            return ""
        return f"{self.id}_of_{self.num}"
    
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return self.id == other.id and self.num == other.num

    def is_whole(self):
        assert self.id <= self.num
        assert self.id > 0
        return self.num == 1 

    @classmethod
    def from_str(cls, s):
        if s == "":
            return Partition(1, 1)

        pattern = re.compile(r"(\d+)/(\d+)")
        match = re.match(pattern, s)

        if match:
            id, num = match.group(1), match.group(2)
        else:
            [id, num] = s.split("_of_")
        return Partition(int(id), int(num))

def partition(a, n):
    k, m = divmod(len(a), n)
    return [a[i*k+min(i, m):(i+1)*k+min(i+1, m)] for i in range(n)]

class Project:
    def __init__(self, full_name, root_dir):
        self.full_name = full_name
        self.root_dir = root_dir

    def __lt__(self, other):
        return self.full_name < other.full_name

    def list_queries(self, part=Partition(1, 1)):
        queries = list_smt2_files(self.root_dir)
        # sort then shuffle (original is ordered by the os.walk)
        queries = sorted(queries)
        # some fixed random seed will do
        random.seed(984352732132123)
        random.shuffle(queries)
        partitions = partition(queries, part.num)
        return partitions[part.id - 1]
    
    @staticmethod
    def single_mode_project(query_path):
        san_check(query_path.endswith(".smt2"),
                        '[ERROR] query must end with ".smt2"')
        query_path = query_path.replace(".smt2", "")
        query_id = scrub(os.path.basename(query_path))
        root_dir = "gen/" + query_id
        return Project("single_" + query_id, root_dir)

    def get_assert_counts(self, update=False):
        cache_path = f"asserts/{self.full_name}"
        if has_cache(cache_path) and not update:
            counts = load_cache(cache_path)
        else:
            print(f"[INFO] loading assert counts for {self.full_name}")
            counts = dict()
            for query_path in tqdm(self.list_queries()):
                base_name = os.path.basename(query_path)
                counts[base_name] = count_asserts(query_path)
            save_cache(cache_path, counts)
        return counts

class ProjectGroup:
    def __init__(self, name, root_dir):
        self.group_name = name
        self.root_dir = root_dir
        self.projects = dict()
        self._load_projects()

    def __lt__(self, other):
        return self.group_name < other.group_name

    def _load_projects(self):
        for proj_dir in os.listdir(self.root_dir):
            if not ProjectType.has(proj_dir):
                print(f"[WARN] unknown sub project {proj_dir} for project {self.group_name}")
                continue
            sub_dir = os.path.join(self.root_dir, proj_dir)
            assert os.path.isdir(sub_dir)
            sub_name = f"{self.group_name}_{proj_dir}"
            self.projects[ProjectType(proj_dir)] = Project(sub_name, sub_dir)
        # assert "original" in self.projects

class ProjectManager:
    def __init__(self):
        self.groups = dict()
        self.all_projects = dict()

        for group_root in os.listdir("data/projects/"):
            p = ProjectGroup(group_root, "data/projects/" + group_root)
            self.groups[group_root] = p

        for pg in self.groups.values():
            for proj in pg.projects.values():
                self.all_projects[proj.full_name] = proj

    def load_project(self, proj_name, proj_typ, enable_dummy=False):
        proj_name = proj_name + "_" + proj_typ.value
        if proj_name not in self.all_projects:
            if enable_dummy:
                print(f"[WARN] no project {proj_name}, using _empty project!")
                return Project(proj_name, "data/projects/_empty")
            exit_with(f"[ERROR] no project {proj_name}")
        return self.all_projects[proj_name]

    def print_available_projects(self):
        print("available projects:")
        types = [tp.value for tp in ProjectType]
        table = [[""] + types]
        for pg in sorted(self.groups.values()):
            row = [pg.group_name]
            for tp in ProjectType:
                if tp in pg.projects:
                    row.append(len(pg.projects[tp.value].list_queries()))
                else:
                    row.append("-")
            table.append(row)
        print(tabulate(table, headers="firstrow", tablefmt="github"))

PM = ProjectManager()