import binascii, random
import multiprocessing
import os, sys
from typing import Dict
from base.defs import DEBUG_ROOT, MARIPOSA
from utils.query_utils import Mutation, emit_mutant_query, parse_trace
from utils.system_utils import log_check, log_info, log_warn, subprocess_run
from tabulate import tabulate
from query.instantiater import Instantiater

CORE_TRIALS = 10
CORE_TIME_LIMIT_SEC = 60
TRACE_TIME_LIMIT_SEC = 10
TRACE_TRIALS = 10
PROC_COUNT = 4
QID_TABLE_LIMIT = 30

def parse_solver_output(output):
    if "unsat" in output:
        return "unsat"
    elif "sat" in output:
        return "sat"
    elif "timeout" in output:
        return "timeout"
    elif "unknown" in output:
        return "unknown"
    return "error"

def _build_trace(args):
    mut_path, trace_path, seeds = args

    solver_args = [
        "./bin/z3-4.13.0",
        f"-t:{TRACE_TIME_LIMIT_SEC*1000}",
        mut_path,
        "trace=true",
        f"trace_file_name={trace_path}",
    ]

    if seeds is not None:
        solver_args += [f"sat.random_seed={seeds}", f"smt.random_seed={seeds}"]

    stdout, stderr, elapsed = subprocess_run(solver_args, check=True, debug=False)
    res = parse_solver_output(stdout)
    final_trace_path = f"{trace_path}.{elapsed}.{res}"
    os.system(f"mv {trace_path} {final_trace_path}")
    log_info(f"[build-trace] {final_trace_path}")

def _build_inst(args):
    mut_path, seed = args
    ins = Instantiater(mut_path, seed)
    if ins.process():
        log_info(f"[build-inst] success {mut_path}")
        return ins.inst_freq
    log_warn(f"[build-inst] failed {mut_path}")
    return None

class TraceInfo:
    def __init__(self, trace_path):
        self.trace_path = trace_path
        base = os.path.basename(trace_path)
        items = base.split(".")
        self.mutation = items[0]
        self.seed = int(items[1])
        self.time = int(items[2])
        self.rcode = items[3]

    def __str__(self):
        return self.trace_path

    def get_qids(self, query_path):
        return parse_trace(query_path, self.trace_path)

class Debugger3:
    def __init__(self, query_path, clear):
        base_name = os.path.basename(query_path)
        # name_hash = get_name_hash(query_path)
        self.sub_root = f"{DEBUG_ROOT}{base_name}"
        self.orig_path = f"{self.sub_root}/orig.smt2"
        # self.pins_path = f"{self.sub_root}/pins.smt2"

        self.trace_dir = f"{self.sub_root}/traces"
        self.temp_dir = f"{self.sub_root}/temp"

        if not os.path.exists(self.sub_root):
            os.makedirs(self.sub_root)

        # if not os.path.exists(self.temp_dir):
        #     os.makedirs(self.temp_dir)

        if not os.path.exists(self.orig_path):
            os.system(f"cp {query_path} {self.orig_path}")

        self.init_traces(clear)

    def build_traces(self):
        pool = multiprocessing.Pool(PROC_COUNT)
        args = []

        for mut in [Mutation.SHUFFLE, Mutation.RENAME, Mutation.RESEED]:
            for _ in range(TRACE_TRIALS):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                mut_path = f"{self.temp_dir}/{mut}.{s}.smt2"
                trace_path = f"{self.trace_dir}/{mut}.{s}"

                if mut != Mutation.RESEED:
                    emit_mutant_query(self.orig_path, mut_path, mut, s)
                    s = None
                else:
                    mut_path = self.orig_path

                args.append((mut_path, trace_path, s))

        random.shuffle(args)
        pool.map(_build_trace, args)
        pool.close()
        pool.join()

    def init_traces(self, clear):
        if clear:
            os.system(f"rm -rf {self.trace_dir}")

        if not os.path.exists(self.trace_dir):
            os.makedirs(self.trace_dir)
            self.build_traces()

        self.traces: Dict[str, TraceInfo] = dict()

        for trace in os.listdir(self.trace_dir):
            trace_path = f"{self.trace_dir}/{trace}"
            tio = TraceInfo(trace_path)
            self.traces[trace_path] = tio

        log_check(len(self.traces) != 0, f"no traces found: {self.trace_dir}")
        return self.traces

    def print_traces(self):
        table = []
        for _, v in self.traces.items():
            # print(v.get_qids(self.orig_path))
            table.append([v.mutation, v.seed, v.time, v.rcode])
        log_info(f"listing {len(table)} traces:")
        print(tabulate(table, headers=["mutation", "seed", "time", "result"]))

    def find_proof(self):
        pool = multiprocessing.Pool(PROC_COUNT)

        args = []
        for mut in [Mutation.SHUFFLE, Mutation.RESEED]:
            for _ in range(TRACE_TRIALS):
                s = int(binascii.hexlify(os.urandom(8)), 16)
                mut_path = f"{self.temp_dir}/{mut}.{s}.smt2"
                if mut != Mutation.RESEED:
                    emit_mutant_query(self.orig_path, mut_path, mut, s)
                    s = None
                else:
                    mut_path = self.orig_path
                args.append((mut_path, s))

        random.shuffle(args)

        res = []

        while len(args) > 0:
            batch, args = args[:PROC_COUNT], args[PROC_COUNT:]
            res = pool.map(_build_inst, batch)
            res = [r for r in res if r is not None]
            if len(res) > 0:
                break
        
        log_check(len(res) != 0, "no proof found")
        self.proofs = res

        pool.close()
        pool.join()

    def debug_trace(self, proof):
        for _, v in self.traces.items():
            if v.rcode == "unsat":
                continue

            table = []
            explored = v.get_qids(self.orig_path)
            # print(explored)
            for qid in explored:
                table += [(qid, explored[qid], proof[qid] if qid in proof else 0)]

            print(tabulate(table, headers=["QID", "Trace Count", "Proof Count"]))
            break

if __name__ == "__main__":
    debugger = Debugger3(sys.argv[1], False)
    debugger.print_traces()
    # debugger.find_proof()
    pf = {'user_lib__page_organization__PageOrg__State__merge_with_after_ll_inv_valid_unused_297': 1, 'user_lib__page_organization__PageOrg__State__good_range0_173': 1, 'user_lib__page_organization__PageOrg__State__attached_ranges_174': 1, 'internal_lib__page_organization__PageOrg__State_unbox_axiom_definition': 2, 'internal_lib!page_organization.PageOrg.impl&__4.invariant.?_definition': 1, 'prelude_fuel_defaults': 41, 'internal_lib!page_organization.PageOrg.impl&__4.attached_ranges.?_definition': 1, 'user_lib__page_organization__PageOrg__State__public_invariant_148': 1, 'internal_lib!page_organization.PageOrg.impl&__4.public_invariant.?_definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.merge_with_after_strong.?_definition': 1, 'internal_lib__tokens__SegmentId_box_axiom_definition': 3, 'internal_tuple__4./tuple__4/0_accessor_definition': 1, 'internal_crate__tuple__4_box_axiom_definition': 1, 'prelude_unbox_box_int': 43, 'internal_tuple__4./tuple__4/1_accessor_definition': 1, 'internal_tuple__4./tuple__4/2_accessor_definition': 1, 'prelude_nat_clip': 11, 'internal_lib!tokens.PageId./PageId_constructor_definition': 4, 'internal_lib!page_organization.Popped./VeryUnready/0_invariant_definition': 1, 'internal_lib!page_organization.PageOrg.State./State/popped_invariant_definition': 1, 'internal_lib__tokens__PageId_box_axiom_definition': 8, 'internal_lib!tokens.PageId./PageId/segment_id_accessor_definition': 6, 'internal_lib!page_organization.PageOrg.impl&__4.attached_ranges_segment.?_definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.attached_rec0.?_definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.good_range0.?_definition': 1, 'prelude_unbox_int': 2, 'internal_core!option.Option./Some/0_invariant_definition': 9, 'internal_lib!page_organization.PageData./PageData/count_invariant_definition': 4, 'internal_vstd!map.impl&__0.index.?_pre_post_definition': 8, 'internal_vstd__map__Map<lib!tokens.PageId./lib!page_organization.PageData.>_has_type_always_definition': 3, 'internal_lib!page_organization.PageOrg.State./State/pages_accessor_definition': 2, 'internal_core!option.Option./Some/0_accessor_definition': 15, 'internal_lib!tokens.PageId./PageId/idx_accessor_definition': 8, 'prelude_add': 23, 'user_lib__page_organization__PageOrg__State__data_for_unused_header_162': 3, 'internal_lib!page_organization.PageOrg.impl&__4.data_for_unused_header.?_definition': 1, 'user_lib__page_organization__PageOrg__State__count_off0_150': 5, 'internal_lib!page_organization.PageOrg.impl&__4.count_off0.?_definition': 1, 'internal_lib!page_organization.is_unused_header.?_definition': 2, 'internal_core__option__Option_box_axiom_definition': 57, 'internal_lib__page_organization__PageOrg__State_box_axiom_definition': 1, 'internal_lib__page_organization__Popped_box_axiom_definition': 1, 'internal_lib__page_organization__PageData_box_axiom_definition': 6, 'internal_req__lib!page_organization.PageOrg.impl&__4.unused_is_in_sbin._definition': 1, 'internal_req__lib!page_organization.PageOrg.impl&__4.lemma_range_not_used._definition': 1, 'prelude_sub': 29, 'prelude_box_unbox_int': 17, 'prelude_has_type_int': 21, 'internal_vstd__seq__Seq<lib!tokens.PageId.>_unbox_axiom_definition': 5, 'internal_vstd!seq.Seq.subrange.?_pre_post_definition': 2, 'internal_tuple__2./tuple__2/1_invariant_definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.get_list_idx.?_pre_post_definition': 1, 'internal_vstd__seq__Seq<vstd!seq.Seq<lib!tokens.PageId.>.>_has_type_always_definition': 1, 'internal_lib!page_organization.PageOrg.State./State/unused_lists_accessor_definition': 1, 'internal_tuple__2./tuple__2/1_accessor_definition': 1, 'internal_vstd!seq.Seq.index.?_pre_post_definition': 18, 'user_vstd__map__axiom_map_insert_domain_72': 12, 'internal_vstd__map__Map<lib!tokens.PageId./lib!page_organization.PageData.>_box_axiom_definition': 1, 'internal_vstd__map__Map<lib!tokens.PageId./lib!page_organization.PageData.>_unbox_axiom_definition': 12, 'internal_vstd!seq_lib.impl&__0.remove.?_pre_post_definition': 1, 'internal_vstd!seq_lib.impl&__0.remove.?_definition': 1, 'user_vstd__seq__axiom_seq_subrange_len_64': 2, 'internal_ens__lib!page_organization.PageOrg.impl&__4.unused_is_in_sbin._definition': 1, 'prelude_box_unbox_nat': 1, 'internal_lib!page_organization.PageOrg.impl&__4.valid_unused_page.?_definition': 1, 'internal_lib__tokens__PageId_unbox_axiom_definition': 13, 'internal_lib!page_organization.DlistEntry./DlistEntry/next_invariant_definition': 2, 'internal_lib!page_organization.PageData./PageData/dlist_entry_invariant_definition': 3, 'internal_lib__page_organization__DlistEntry_box_axiom_definition': 6, 'user_lib__page_organization__valid_ll_163': 4, 'user_lib__page_organization__PageOrg__State__ll_inv_valid_unused_164': 2, 'internal_lib!page_organization.PageOrg.impl&__4.ll_inv_valid_unused.?_definition': 2, 'internal_lib!page_organization.PageOrg.impl&__4.ll_basics.?_definition': 1, 'internal_lib!page_organization.valid_ll.?_definition': 5, 'internal_lib!page_organization.valid_ll_i.?_definition': 10, 'internal_lib!page_organization.get_next.?_definition': 7, 'user_vstd__set__axiom_set_insert_different_86': 18, 'internal_vstd!map.impl&__0.dom.?_pre_post_definition': 7, 'internal_vstd__seq__Seq<vstd!seq.Seq<lib!tokens.PageId.>.>_unbox_axiom_definition': 1, 'internal_vstd!seq.Seq.update.?_pre_post_definition': 2, 'user_vstd__seq__axiom_seq_update_same_56': 3, 'internal_vstd!map.impl&__0.insert.?_pre_post_definition': 12, 'user_lib__page_organization__PageOrg__State__inv_very_unready_159': 1, 'internal_lib!page_organization.PageOrg.impl&__4.inv_very_unready.?_definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.popped_basics.?_definition': 1, 'internal_lib!page_organization.PageData./PageData/dlist_entry_accessor_definition': 15, 'internal_lib!page_organization.PageData./PageData/count_accessor_definition': 11, 'internal_lib!page_organization.PageData./PageData/offset_accessor_definition': 2, 'prelude_unbox_box_bool': 2, 'internal_lib!page_organization.PageData./PageData/is_used_accessor_definition': 1, 'internal_lib!page_organization.PageData./PageData/full_accessor_definition': 1, 'internal_lib!page_organization.PageData./PageData/page_header_kind_accessor_definition': 1, 'internal_lib__page_organization__PageData_unbox_axiom_definition': 3, 'user_vstd__set__axiom_set_insert_same_85': 3, 'internal_lib!page_organization.DlistEntry./DlistEntry/prev_invariant_definition': 2, 'internal_lib!page_organization.get_prev.?_definition': 7, 'internal_crate__tuple__2_box_axiom_definition': 2, 'user_vstd__map__axiom_map_insert_same_73': 4, 'user_lib__page_organization__PageOrg__State__good_range_unused_172': 4, 'internal_ens__lib!page_organization.PageOrg.impl&__4.lemma_range_not_used._definition': 1, 'internal_lib!page_organization.PageOrg.impl&__4.good_range_unused.?_definition': 1, 'user_vstd__map__axiom_map_insert_different_74': 25, 'internal_lib!page_organization.DlistEntry./DlistEntry/prev_accessor_definition': 4, 'internal_lib__page_organization__DlistEntry_unbox_axiom_definition': 2, 'user_vstd__seq__axiom_seq_subrange_index_65': 15, 'user_vstd__seq__axiom_seq_add_index1_67': 5, 'internal_lib!bin_sizes.smallest_sbin_fitting_size.?_definition': 3, 'user_vstd__seq__axiom_seq_add_len_66': 1, 'internal_lib!page_organization.DlistEntry./DlistEntry/next_accessor_definition': 6, 'user_vstd__seq__axiom_seq_add_index2_68': 6, 'internal_lib!page_organization.PageData./PageData_constructor_definition': 2, 'internal_core!option.Option./Some_constructor_definition': 2, 'internal_lib!page_organization.DlistEntry./DlistEntry_constructor_definition': 2, 'internal_lib!page_organization.PageData./PageData/offset_invariant_definition': 1, 'internal_lib!page_organization.PageData./PageData/full_invariant_definition': 2, 'internal_lib!page_organization.PageData./PageData/page_header_kind_invariant_definition': 2, 'user_lib__page_organization__PageOrg__State__ll_inv_valid_unused2_166': 9, 'user_lib__page_organization__PageOrg__State__ll_inv_valid_unused2_167': 2, 'internal_lib!page_organization.PageOrg.impl&__4.ll_inv_valid_unused2.?_definition': 1, 'internal_req__lib!page_organization.PageOrg.impl&__4.ll_unused_distinct._definition': 9, 'prelude_ext_eq': 1, 'internal_lib!page_organization.DlistHeader./DlistHeader/last_invariant_definition': 1, 'internal_vstd__seq__Seq<lib!page_organization.DlistHeader.>_has_type_always_definition': 1, 'internal_lib!page_organization.PageOrg.State./State/unused_dlist_headers_accessor_definition': 1, 'user_vstd__seq_lib__impl&%0__add_empty_right_120': 1, 'internal_lib!page_organization.DlistHeader./DlistHeader/last_accessor_definition': 3, 'internal_vstd__seq__Seq<lib!page_organization.DlistHeader.>_unbox_axiom_definition': 2, 'internal_lib!page_organization.DlistHeader./DlistHeader_constructor_definition': 3, 'internal_lib!page_organization.DlistHeader./DlistHeader/first_invariant_definition': 1, 'internal_lib!page_organization.DlistHeader./DlistHeader/first_accessor_definition': 3, 'internal_lib__page_organization__DlistHeader_box_axiom_definition': 1, 'user_vstd__seq_lib__impl&%0__add_empty_left_119': 1, 'internal_vstd!seq.Seq.len.?_pre_post_definition': 2, 'internal_lib__page_organization__DlistHeader_unbox_axiom_definition': 2, 'user_lib__page_organization__PageOrg__State__merge_with_after_ll_inv_valid_unused_295': 2, 'user_vstd__seq__axiom_seq_update_different_57': 3, 'user_lib__page_organization__PageOrg__State__merge_with_after_ll_inv_valid_unused_296': 1, 'internal_vstd!set.impl&__0.insert.?_pre_post_definition': 1, 'internal_ens__lib!page_organization.PageOrg.impl&__4.ll_unused_distinct._definition': 12, 'internal_vstd__seq__Seq<lib!tokens.PageId.>_has_type_always_definition': 1, 'internal_vstd__seq__Seq<lib!tokens.PageId.>_box_axiom_definition': 1, 'user_vstd__seq__axiom_seq_update_len_55': 1, 'prelude_u_clip': 2, 'prelude_u_inv': 1, 'prelude_div_unsigned_in_bounds': 1, 'prelude_eucdiv': 1, 'internal_lib!page_organization.PageOrg.impl&__4.popped_for_seg.?_definition': 2, 'internal_lib__tokens__SegmentId_unbox_axiom_definition': 1, 'internal_lib!tokens.PageId./PageId/segment_id_invariant_definition': 1}
    debugger.debug_trace(pf)
    # debugger.debug_trace(debugger.proofs[0])

