import os, random, enum, re
from utils.system_utils import *
from base.solver import SolverType
from base.defs import DB_ROOT, GEN_ROOT, LOG_ROOT, PROJ_ROOT

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

class _ProjectType(enum.Enum):
    BASE = "base" # baseline
    CORE = "core" # unsat core
    EXTD = "extd" # unsat core extension
    SHKF = "shkf" # shake full
    SHKO = "shko" # shake oracle
    SHKP = "shkp" # shake partial
    INST = "inst" # instantiated

    def __str__(self):
        return self.value
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        return self.value == other.value

class ProjectType:
    def __init__(self, qtyp: _ProjectType, styp: SolverType):
        self.qtyp = qtyp
        self.styp = styp

    def __str__(self):
        return f"{self.qtyp.value}.{self.styp.value}"

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return str(self) == str(other)

    @staticmethod
    def from_str(s):
        try:
            q, s = s.split(".")
            return ProjectType(_ProjectType(q), SolverType(s))
        except:
            return None

    def base_to_core(self):
        log_check(self.qtyp == _ProjectType.BASE,
                        "currently only a base project can be converted to core project")
        log_check(self.styp == SolverType.Z3, 
                  "currently only z3-sourced project can be converted to core project")
        return ProjectType(_ProjectType.CORE, self.styp)

    def z3_to_cvc5(self):
        log_check(self.styp == SolverType.Z3,
                  "currently only z3-sourced project can be converted to cvc5 project")
        return ProjectType(self.qtyp, SolverType.CVC5)

def full_proj_name(name, ptyp):
    return name + "." + str(ptyp)

class Project:
    def __init__(self, name, ptyp: ProjectType=ProjectType.from_str("base.z3"), part=Partition(1, 1)):
        self.group_name = name
        self.full_name = full_proj_name(name, ptyp)
        self.ptype = ptyp
        self.sub_root = os.path.join(PROJ_ROOT, name, str(ptyp))
        self.part = part

    def __lt__(self, other):
        return self.full_name < other.full_name
    
    def __eq__(self, other):
        return self.full_name == other.full_name and \
            self.part == other.part

    def get_db_dir(self):
        log_check(self.sub_root.startswith(PROJ_ROOT), 
                  f"invalid sub_root {self.sub_root}")
        return self.sub_root.replace(PROJ_ROOT, DB_ROOT)
    
    # def get_log_dir(self):
    #     san_check(self.sub_root.startswith(PROJ_ROOT), 
    #         f"invalid sub_root {self.sub_root}")
    #     return self.sub_root.replace(PROJ_ROOT, LOG_ROOT)

    def get_gen_dir(self):
        log_check(self.sub_root.startswith(PROJ_ROOT), 
                  f"invalid sub_root {self.sub_root}")
        return self.sub_root.replace(PROJ_ROOT, GEN_ROOT)

    def set_partition(self, part):
        self.part = part

    def list_queries(self):
        queries = list_smt2_files(self.sub_root)
        # sort then shuffle (original is ordered by the os.walk)
        queries = sorted(queries)
        # some fixed random seed will do
        random.seed(984352732132123)
        random.shuffle(queries)
        partitions = partition(queries, self.part.num)
        return partitions[self.part.id - 1]

    @staticmethod
    def single_mode_project(query_path):
        log_check(query_path.endswith(".smt2"),
                        'query must end with ".smt2"')
        query_path = query_path.replace(".smt2", "")
        query_id = scrub(os.path.basename(query_path))
        p = Project("single_" + query_id)
        p.sub_root = "gen/" + query_id
        return p

    def is_whole(self):
        return self.part.is_whole()

class ProjectGroup:
    def __init__(self, name, groot):
        self.group_name = name
        self.groot = groot
        self.projects = dict()
        self.__init_sub_projs()

    def __lt__(self, other):
        return self.group_name < other.group_name

    def __init_sub_projs(self):
        for proj_dir in os.listdir(self.groot):
            sub_proj = ProjectType.from_str(proj_dir)
            sub_dir = os.path.join(self.groot, proj_dir)
            if not sub_proj:
                log_warn(f"unknown sub project under the directory {sub_dir}")
                continue

            if not os.path.isdir(sub_dir):
                log_error(f"sub project {sub_dir} is not a directory")

            sub_proj = Project(self.group_name, sub_proj)
            self.projects[sub_proj.full_name] = sub_proj
            
    def get_project(self, ptyp: ProjectType):
        return self.projects.get(full_proj_name(self.group_name, ptyp))
    
    def list_projects(self):
        return list(sorted(self.projects.values()))

class ProjectManager:
    def __init__(self):
        self.groups = dict()
        self.all_projects = dict()

        for groot in os.listdir(PROJ_ROOT):
            p = ProjectGroup(groot, PROJ_ROOT + groot)
            self.groups[groot] = p

    def get_project(self, group_name, ptyp: ProjectType, enable_dummy=False):
        group = self.groups.get(group_name)
        log_check(group, f"no such project group {group_name}")
        proj = group.get_project(ptyp)
        log_check(proj, f"no such sub-project {ptyp} under {group_name}")
        return proj
    
    def get_project_by_path(self, path) -> Project:
        log_check(path.startswith(PROJ_ROOT), f"invalid path {path}")
        items = os.path.normpath(path).split(os.sep)[-2:]
        log_check(len(items) == 2, f"invalid project path {path}")
        ptype = ProjectType.from_str(items[1])
        log_check(ptype, f"invalid project type {items[1]}")
        return self.get_project(items[0], ptype)

    def get_core_project(self, proj: Project, build=False) -> Project:
        core_ptype = proj.ptype.base_to_core()
        if not build:
            return self.get_project(proj.group_name, core_ptype)
        return Project(proj.group_name, core_ptype)

    def get_cvc5_counterpart(self, proj: Project, build=False) -> Project:
        cvc5_ptype = proj.ptype.z3_to_cvc5()
        if not build:
            return self.get_project(proj.group_name, cvc5_ptype)
        return Project(proj.group_name, cvc5_ptype)

    def list_projects(self):
        print("available projects:")
        for pg in sorted(self.groups.values()):
            print(f"  {pg.group_name}")
            for proj in pg.list_projects():
                print(f"    {proj.ptyp}")

PM = ProjectManager()