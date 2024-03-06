import os, random, enum, re
from utils.system_utils import *
from base.solver import SolverType
from base.defs import *

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
    def __init__(self, qtyp: _ProjectType, stype: SolverType):
        self.qtype = qtyp
        self.stype = stype

    def __str__(self):
        return f"{self.qtype.value}.{self.stype.value}"

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
        
    def switch_solver(self, stype: SolverType):
        return ProjectType(self.qtype, stype)
    
    def switch_query(self, qtype: _ProjectType):
        return ProjectType(qtype, self.stype)

def full_proj_name(name, ptyp):
    return name + "." + str(ptyp)

# class QueryFileMapper:
#     def __init__(self, base_query_path):
#         self.group_root = 
#         self.ext = ext

class Project:
    def __init__(self, name, ptyp: ProjectType=ProjectType.from_str("base.z3"), part=Partition(1, 1)):
        self.group_name = name
        self.full_name = full_proj_name(name, ptyp)
        self.ptype = ptyp
        self.sub_root = os.path.join(PROJ_ROOT, name, str(ptyp))
        self.part = part
        self.single_mode = False

    def __lt__(self, other):
        return self.full_name < other.full_name
    
    def __eq__(self, other):
        return self.full_name == other.full_name and \
            self.part == other.part

    def get_db_dir(self):
        if self.single_mode: return SINGLE_PROJ_ROOT
        log_check(self.sub_root.startswith(PROJ_ROOT), 
                  f"invalid sub_root {self.sub_root}")
        return self.sub_root.replace(PROJ_ROOT, DB_ROOT)

    def get_log_dir(self):
        log_check(self.sub_root.startswith(PROJ_ROOT), 
            f"invalid sub_root {self.sub_root}")
        return self.sub_root.replace(PROJ_ROOT, LOG_ROOT)

    def get_gen_dir(self):
        if self.single_mode: return SINGLE_MUT_ROOT
        log_check(self.sub_root.startswith(PROJ_ROOT), 
                  f"invalid sub_root {self.sub_root}")
        return self.sub_root.replace(PROJ_ROOT, GEN_ROOT)

    def get_alt_dir(self, ptype: ProjectType):
        log_check(self.sub_root.startswith(PROJ_ROOT), 
                  f"invalid sub_root {self.sub_root}")
        return os.path.join(self.sub_root, str(ptype))

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

    def __list_query_paths(self):
        for path in self.list_queries():
            # log_check(q.endswith(".smt2"), f"invalid query {q}")
            yield (path, os.path.basename(path))

    def is_whole(self):
        return self.part.is_whole()

    def map_to_lfscs(self):
        mapping = dict()
        self.log_dir = self.get_log_dir()
        for (path, name) in self.__list_query_paths():
            out_name = name.replace(".smt2", ".lfsc")
            mapping[path] = os.path.join(self.log_dir, "lfsc", out_name)
        return mapping

    def map_to_cores(self):
        mapping = dict()
        alt_dir = self.get_alt_dir(
            self.ptype.switch_type(_ProjectType.CORE))
        for (_, q) in self.__list_query_paths():
            mapping[q] = os.path.join(alt_dir, q)
        return mapping

    def map_to_cvc5(self):
        mapping = dict()
        alt_dir = self.get_alt_dir(
            self.ptype.switch_solver(SolverType.CVC5))
        for (_, q) in self.__list_query_paths():
            mapping[q] = os.path.join(alt_dir, q)
        return mapping

# class QueryFileMapper:
#     def __init__(self, query_path):
#         self.query_map = dict()

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
    
    def get_projects(self):
        for p in sorted(self.projects.values()):
            yield p

