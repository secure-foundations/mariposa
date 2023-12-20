import os, random, enum, re
from utils.sys_utils import *
from tabulate import tabulate

class ProjectType(str, enum.Enum):
    ORIGINAL = "original"
    UNSAT_CORE = "unsat_core"
    UNSAT_CORE_EXT = "unsat_core_ext"
    SHAKE_FULL = "shake_full"
    SHAKE_ORACLE = "shake_oracle"
    BLOAT = "bloat"
    REVEAL = "reveal"

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
                print(f"[WARNING] unknown sub project {proj_dir} for project {self.name}")
            sub_dir = os.path.join(self.root_dir, proj_dir)
            assert os.path.isdir(sub_dir)
            sub_name = f"{self.group_name}_{proj_dir}"
            self.projects[proj_dir] = Project(sub_name, sub_dir)
        # assert "original" in self.projects

    def get_projects(self):
        return list(self.projects.keys())

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

    def load_project(self, proj_name):
        if proj_name not in self.all_projects:
            proj_name += "_original"
        san_check(proj_name in self.all_projects, f"[ERROR] no project {proj_name}")
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
