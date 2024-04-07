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

class KnownExt(enum.Enum):
    LFSC = "lfsc"
    LFSC_CHK = "lfsc-chk"
    VERI = "veri"
    SMT2 = "smt2"
    CVC5_INST = "cvc5-inst" # cvc5 instantiations at unsat
    Z3_TRACE = "z3-trace"
    SHK_LOG = "shk-log"

    def __str__(self):
        return self.value

class _ProjectType(enum.Enum):
    BASE = "base" # baseline
    CORE = "core" # unsat core
    EXTD = "extd" # unsat core extension
    SHKF = "shkf" # shake full
    SHKO = "shko" # shake oracle
    SHKP = "shkp" # shake partial
    INTD = "intd" # instantiated
    PINS = "pins" # pre-inst
    WOCO = "woco" # wombo combo
    TEMP = "temp" # temp

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

    def switch_solver(self):
        if self.stype == SolverType.Z3:
            stype = SolverType.CVC5
        else:
            log_check(self.stype == SolverType.CVC5, 
                      f"unexpected solver type {self.stype}")
            stype = SolverType.Z3
        return ProjectType(self.qtype, stype)
    
    def switch_query(self, qtype: _ProjectType):
        return ProjectType(qtype, self.stype)

def full_proj_name(name, ptyp):
    return name + "." + str(ptyp)

# the base name identifies a query within a project (no extension!)
def get_qid(query_path):
    base = os.path.basename(query_path)
    base = base.split(".")
    _ = KnownExt(base[-1])
    return ".".join(base[:-1])

class Project:
    DEFAULT_PTYPE = ProjectType(_ProjectType.BASE, SolverType.Z3)

    def __init__(self, gid, 
                 ptyp: ProjectType=DEFAULT_PTYPE, 
                 part=Partition(1, 1),
                 single_mode=False, build=False):

        self.gid = gid
        self.full_name = full_proj_name(gid, ptyp)
        self.ptype = ptyp
        self.part = part
        self.single_mode = single_mode

        self.__init_dirs(gid)
        self._qids = set()

        if not build:
            for q in self.list_queries():
                self._qids.add(get_qid(q))

    def __init_dirs(self, gid):
        if self.single_mode:
            self._sub_root = SINGLE_PROJ_ROOT
        else:
            self._sub_root = os.path.join(PROJ_ROOT, gid, str(self.ptype))
            log_check(self._sub_root.startswith(PROJ_ROOT),
                  f"invalid sub_root {self._sub_root}")

        if self.single_mode: 
            self._db_dir = SINGLE_PROJ_ROOT
            self._gen_dir = SINGLE_MUT_ROOT
        else:
            self._db_dir = self._sub_root.replace(PROJ_ROOT, DB_ROOT)
            self._gen_dir = self.sub_root.replace(PROJ_ROOT, GEN_ROOT)
            self._log_dir = self.sub_root.replace(PROJ_ROOT, LOG_ROOT)

    def reload(self):
        log_check(self.single_mode, "reload is only for single mode")
        self._qids = set()
        for q in self.list_queries():
            self._qids.add(get_qid(q))

    @property
    def sub_root(self):
        return self._sub_root

    @property
    def qids(self):
        return self._qids

    def __lt__(self, other):
        return self.full_name < other.full_name
    
    def __eq__(self, other):
        return self.full_name == other.full_name and \
            self.part == other.part

    def get_log_dir(self, ltype: KnownExt):
        return os.path.join(self._log_dir, ltype.value)

    def get_gen_dir(self, eid):
        log_check(is_simple_id(eid), 
                  "unexpected characters in the experiment id")
        return os.path.join(self._gen_dir, eid)

    def get_db_path(self, eid):
        log_check(is_simple_id(eid), 
                  "unexpected characters in the experiment id")
        return os.path.join(self._db_dir, eid + ".db")

    def get_alt_dir(self, ptype: ProjectType):
        return self.sub_root.replace(str(self.ptype), str(ptype))

    def set_partition(self, part):
        self.part = part

    def list_queries(self):
        queries = list_smt2_files(self.sub_root)
        # sort then shuffle (original is ordered by the os.walk)
        queries = sorted(queries)
        random.seed(984352732132123)
        random.shuffle(queries)
        partitions = partition(queries, self.part.num)
        return partitions[self.part.id - 1]

    # def __list_query_paths(self):
    #     for path in self.list_queries():
    #         # log_check(q.endswith(".smt2"), f"invalid query {q}")
    #         yield (path, os.path.basename(path))

    def is_whole(self):
        return self.part.is_whole()

    def get_ext_path(self, qname, ext=KnownExt.SMT2):
        # log_check(qname in self.qids, f"invalid query {qname}")
        if ext == KnownExt.SMT2:
            return os.path.join(self.sub_root, f"{qname}.smt2")
        return os.path.join(self.get_log_dir(ext), f"{qname}.{ext.value}")

    # def map_to_cores(self):
    #     mapping = dict()
    #     alt_dir = self.get_alt_dir(
    #         self.ptype.switch_type(_ProjectType.CORE))
    #     for (_, q) in self.__list_query_paths():
    #         mapping[q] = os.path.join(alt_dir, q)
    #     return mapping

    # def map_to_cvc5(self):
    #     mapping = dict()
    #     alt_dir = self.get_alt_dir(
    #         self.ptype.switch_solver(SolverType.CVC5))
    #     for (_, q) in self.__list_query_paths():
    #         mapping[q] = os.path.join(alt_dir, q)
    #     return mapping

    def get_build_meta_path(self, ext: KnownExt):
        log_check(ext != KnownExt.SMT2, 
                  ".smt2 file should have no build meta")
        return os.path.join(NINJA_REPORTS_DIR, 
                            f"{self.full_name}.{ext}.pkl")

class ProjectGroup:
    def __init__(self, name, groot):
        self.gid = name
        self.groot = groot
        self.projects = dict()
        self.__init_sub_projs()
        # self.report_dir = os.path.join(REPORT_ROOT, self.gid)
        # create_dir(self.report_dir)

    def __lt__(self, other):
        return self.gid < other.gid
    
    def __init_sub_projs(self):
        for proj_dir in os.listdir(self.groot):
            sub_proj = ProjectType.from_str(proj_dir)
            sub_dir = os.path.join(self.groot, proj_dir)
            if not sub_proj:
                log_warn(f"unknown sub project under the directory {sub_dir}")
                continue

            if not os.path.isdir(sub_dir):
                log_error(f"sub project {sub_dir} is not a directory")

            sub_proj = Project(self.gid, sub_proj)
            self.projects[sub_proj.full_name] = sub_proj

    def get_project(self, ptype: ProjectType, build=False) -> Project:
        fn = full_proj_name(self.gid, ptype)
        if not build:
            log_check(fn in self.projects, f"no such project {fn} under {self.gid}")
        else:
            self.projects[fn] = Project(self.gid, ptype, build=True)
        return self.projects[fn]
    
    def get_projects(self):
        for p in sorted(self.projects.values()):
            yield p

    def save_qids(self, name, qids):
        path = os.path.join(self.report_dir, name + ".qids")
        out_file = open(path, "w")
        for q in qids:
            out_file.write(f"{q}\n")
        out_file.close()

    def load_qids(self, name):
        path = os.path.join(self.report_dir, name + ".qids")
        in_file = open(path, "r")
        qids = set()
        for line in in_file:
            qids.add(line.strip())
        in_file.close()
        return qids
