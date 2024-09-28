import binascii
from typing import Dict, Set
from z3 import *
from base.defs import MARIPOSA
from debugger.query_loader import QueryLoader, SkolemFinder
from debugger.z3_utils import collapse_sexpr, hack_contains_qid, hack_quantifier_removal
from proof_reader import QunatInstInfo
from utils.system_utils import log_info, log_warn, subprocess_run


def add_qids_to_query(query_path):
    args = [
        MARIPOSA,
        "-i",
        query_path,
        "--action=add-qids",
        "-o",
        query_path,
    ]
    subprocess_run(args, check=True, debug=True)


class QueryWriter(QueryLoader):
    def __init__(self, in_file_path):
        super().__init__(in_file_path)
        self.in_file_path = in_file_path
        # this is a lazy way to avoid name clashes
        self.__fun_prefix = "fn_" + binascii.hexlify(os.urandom(4)).decode("utf-8") + "_"
        self.__fun_cache = dict()
        self.__fun_defs = []

    def skolemize_qids(self, target_ids: Set[str], out_file_path: str):
        target_asserts = set()
        for qid in target_ids:
            if qid not in self.quants:
                log_warn(f"skolem target {qid} not found")
                continue
            assertion = self.quants[qid].assertion
            # if assertion is None:
            #     log_check(f"skolem target {qid} has no assertion")
            #     continue
            target_asserts.add(assertion)
        commands = []

        for assertion in target_asserts:
            asserts, decls = self.skolemize_assertion(assertion)
            commands = commands + decls + asserts

        out_file = open(out_file_path, "w+")

        for line in open(self.in_file_path, "r"):
            removed = set()
            skip = False
            for qid in target_ids:
                if hack_contains_qid(line, qid):
                    removed.add(qid)
                    log_info(f"skipping the following assertion:")
                    print(line, end="")
                    skip = True
            target_ids -= removed

            if line == "(check-sat)\n":
                for command in commands:
                    out_file.write(command + "\n")
            if not skip:
                out_file.write(line)
        out_file.close()

        add_qids_to_query(out_file_path)

    def skolemize_assertion(self, exp):
        g = Goal()
        g.add(exp)
        t = Tactic("snf")
        res = t(g)
        assert len(res) == 1
        res = res[0]
        asserts, decls = [], []
        for r in res:
            skf = SkolemFinder()
            skf.find_sk_fun(r)
            asserts.append("(assert " + collapse_sexpr(r.sexpr()) + ")")
            for decl in skf.funs.values():
                decls.append(decl)
        return asserts, decls

    def erase_qids(self, remove_ids: Set[str], out_file_path: str):
        out_file = open(out_file_path, "w+")

        for line in open(self.in_file_path, "r"):
            removed = set()
            for qid in remove_ids:
                if hack_contains_qid(line, qid):
                    line = hack_quantifier_removal(line, qid)
                    removed.add(qid)
                    log_info(f"erasing qid: {qid}")
            remove_ids -= removed

            out_file.write(line)
        out_file.close()

    def get_fresh_name(self):
        return self.__fun_prefix + str(len(self.__fun_defs))
    
    def add_fun(self, body, sort: Sort):
        if body in self.__fun_cache:
            return self.__fun_cache[body]
        name = self.get_fresh_name()
        func = f"(define-fun {name} () {sort} {body})"
        self.__fun_defs.append(func)
        self.__fun_cache[body] = name
        return name

    def instantiate_qids(self, target_ids: Dict[str, QunatInstInfo], out_file_path: str):
        # target_asserts = set()
        commands = []
        for qid, qi in target_ids.items():
            commands += self.instantiate_qid(qi)
        commands = self.__fun_defs + commands

        out_file = open(out_file_path, "w+")
        for line in open(self.in_file_path, "r"):
            if line == "(check-sat)\n":
                for command in commands:
                    out_file.write(command + "\n")            
            out_file.write(line)
        out_file.close()
        add_qids_to_query(out_file_path)

    def instantiate_qid(self, qi: QunatInstInfo):
        qid = qi.qid

        if qid not in self.quants:
            log_warn(f"instantiation target {qid} not found")
            return
        
        quant = self.quants[qid]

        if len(qi.errors) > 0:
            log_warn(f"skipping instantiation target {qid} due to errors:")
            # for bindings in qi.bindings:
            #     for i, b in bindings.items():
            #         print(i, b)
            print("\t".join([str(e) for e in qi.errors]))
            return     

        commands = []
        vars = quant.get_vars()
        
        for bindings in qi.bindings:
            subs = dict()
            for i, b in bindings.items():
                name = self.add_fun(b, vars[i][1])
                subs[i] = name
            commands.append(quant.rewrite_as_let(subs))
                # print(vars[i][0], name)
        return commands

