#!/usr/bin/env python3

import os, sys
from z3 import set_param
from base.solver import RCode
from debugger.trace_analyzer import EditAction
from debugger3 import Debugger3
from proof_builder import QunatInstInfo
from query_editor import BasicQueryWriter
from random import sample

from utils.system_utils import log_info, subprocess_run

ITER = "dbg/iters"


def copy_to_iter_dir(src_path):
    items = src_path.split("/")
    assert items[2] == "edits"
    base = items[1]
    assert base.endswith(".smt2")
    new_name = f"{base[:-5]}.{items[3]}"
    new_path = f"{ITER}/{new_name}"
    # print(new_path)
    if not os.path.exists(ITER):
        os.mkdir(ITER)
    subprocess_run(["cp", src_path, new_path])
    log_info(f"[iter] copied to {new_path}")
    return new_path


def test0():
    q = "data/projs/v_systems/base.z3/ironsht--delegation_map_v.35.smt2"
    dbg = Debugger3(q, False, False)
    dbg.save_report()
    dbg.try_random_edits()
    dbg.save_edit_report()


def unstable1():
    q = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.try_random_edits()
    # dbg.try_ranked_edits()

    edit_ids = {
        "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
    }
    # time to unsat: 0.03
    # dbg/noderep--spec__cyclicbuffer.3.smt2/edits/v1.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          49         12          0  0.06 / 0.03          0.09
    # rename           61          0          0  0.03 /  --           0
    # reseed           61          0          0  0.04 /  --           0

    dbg.do_edits(edit_ids)

    dbg.save_edit_report()


def unstable2():
    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  7.64 / 10.00         1.42
    # rename            0          0         61  --  / 10.00          0
    # reseed           23          0         38  8.40 / 10.00         0.99

    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.clear_edits()
    # dbg.try_random_edits()
    dbg.try_ranked_edits()

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2/edits/v9.smt2
    # rcode: unsat
    # time: 3.08
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  6.07 / 10.00         1.54
    # rename           61          0          0  5.21 /  --           0.12
    # reseed           60          0          1  6.01 / 10.00         1.39
    edits = {
        "internal_lib!page_organization.PageData./PageData/dlist_entry_accessor_definition": EditAction.INSTANTIATE
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def unstable3():
    q = "data/projs/v_systems/base.z3/mimalloc--commit_segment.1.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    dbg.try_ranked_edits()
    dbg.save_edit_report()


def unstable4():
    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg.69.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          44          0         17  7.27 / 10.00         1.76
    # rename            0          0         61  --  / 10.00          0
    # reseed           16          0         45  7.71 / 10.00         1.12

    dbg = Debugger3(q, False, True)
    # dbg.save_report()
    # dbg.clear_edits()
    dbg.try_aggressive_edits()
    # dbg.try_ranked_edits()
    # dbg.try_random_edits()

    # edit_path = 'dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v11.smt2'
    # rcode: unsat
    # time: 1.88
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  5.78 / 10.00         1.61
    # rename           61          0          0  3.11 /  --           0.04
    # reseed           61          0          0  4.01 /  --           0.56
    edits = {
        "internal_lib!page_organization.PageData./PageData/dlist_entry_accessor_definition": EditAction.INSTANTIATE
    }
    dbg.do_edits(edits)

    # --------------------------------------------------------------------------------
    # path = 'dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v2.smt2'
    # rcode: unsat
    # time: 2.44
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  3.65 /  --           1.13
    # rename           61          0          0  4.00 /  --           0.06
    # reseed           61          0          0  4.52 /  --           0.65
    edits = {"prelude_u_clip": EditAction.ERASE}
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # path = 'dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v1.smt2'
    # rcode: unsat
    # time: 2.78
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  4.45 / 10.00         1.42
    # rename           61          0          0  4.89 /  --           0.09
    # reseed           61          0          0  4.60 /  --           0.44
    edits = {
        "internal_lib!page_organization.PageOrg.impl&__4.good_range0.?_definition": EditAction.INSTANTIATE
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def unstable5():
    q = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.5.smt2"
    pass


def unstable6():
    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__merge_with_before_ll_inv_valid_unused.smt2"
    dbg = Debugger3(q, False, False)
    dbg.save_report()
    dbg.try_ranked_edits()
    dbg.save_edit_report()


def unstable7():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          38          0         23  8.68 / 10.00         0.93
    # rename           61          0          0  8.25 /  --           0.21
    # reseed           61          0          0  8.39 /  --           0.49

    dbg = Debugger3(q, False, True)
    # dbg.clear_edits()
    # dbg.save_report()
    dbg.try_random_edits()
    # dbg.try_ranked_edits()

    # --------------------------------------------------------------------------------
    # edit path: dbg/mimalloc--segment__span_queue_delete.smt2/edits/v1.smt2
    # time to unsat: 3.81
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  8.07 /  --           0.73
    # rename           61          0          0  6.18 /  --           0.13
    # reseed           61          0          0  6.37 /  --           0.27
    edits = {
        "prelude_unbox_box_int": EditAction.INSTANTIATE,
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # edit path: dbg/mimalloc--segment__span_queue_delete.smt2/edits/v3.smt2
    # time to unsat: 8.14
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           0          0         61  --  / 10.00             0
    # rename            0          0         61  --  / 10.00             0
    # reseed            0          0         61  --  / 10.00             0
    edits = {
        "internal_lib!types.impl&__21.wf_main.?_definition": EditAction.INSTANTIATE,
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def unsolvable1():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  8.96 / 10.00         0.64
    # rename            0          0         61  --  / 10.00          0
    # reseed            0          0         61  --  / 10.00          0

    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_ranked_edits()

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/v4.smt2
    # rcode: unsat
    # time: 4.64
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          31          0         30  7.53 / 10.00         1.71
    # rename           61          0          0  8.47 /  --           0.14
    # reseed           61          0          0  8.23 /  --           0.46
    edits = {
        "internal_lib!types.PagePtr./PagePtr/page_id_invariant_definition": EditAction.INSTANTIATE,
        "internal_lib!tokens.ThreadState./ThreadState/heap_accessor_definition": EditAction.ERASE,
        "internal_lib!types.SegmentsTld./SegmentsTld/peak_count_accessor_definition": EditAction.ERASE,
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def unsolvable3():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.try_random_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--queues__page_queue_push_back.smt2/edits/v58.smt2
    # rcode: unsat
    # time: 3.45
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  6.20 / 10.00         0.93
    # rename           61          0          0  6.32 /  --           0.15
    # reseed           61          0          0  6.40 /  --           0.05
    edits = {
        "internal_lib!page_organization.PageOrg.impl&__4.valid_used_page.?_definition": EditAction.INSTANTIATE,
        "internal_lib!atomic_ghost_modified.AtomicU64./AtomicU64/atomic_inv_accessor_definition": EditAction.ERASE,
        "internal_vstd__ptr__PointsToData_unbox_axiom_definition": EditAction.ERASE,
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def demo_unsolvable_5():
    q = "data/projs/v_systems/base.z3/mimalloc--segment.1.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           5          0         56  9.61 / 10.00         0.12
    # rename            1          0         60  10.00 / 10.00        0
    # reseed            5          0         56  9.35 / 10.00         0.21

    dbg = Debugger3(q, False, True)
    # dbg.clear_edits()
    dbg.save_report()
    # dbg.try_aggressive_edits()
    dbg.try_random_edits()

    # dbg.try_ranked_edits(start = {
    #     'internal_vstd!map.impl&__0.dom.?_pre_post_definition': EditAction.INSTANTIATE
    # })

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment.1.smt2/edits/v18.smt2
    # rcode: unsat
    # time: 4.15
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           4          0         57  8.82 / 10.00         0.34
    # rename           61          0          0  7.77 /  --           0.13
    # reseed           49          0         12  8.12 / 10.00         0.81
    # edits = {
    #     'internal_vstd!map.impl&__0.dom.?_pre_post_definition': EditAction.INSTANTIATE
    # }
    # dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


def unsolvable6():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_remove.smt2"
    dbg = Debugger3(q, False, True)
    # dbg.save_report()
    # dbg.clear_edits()
    dbg.try_random_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--queues__page_queue_remove.smt2/edits/v27.smt2
    # rcode: unsat
    # time: 3.89
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          59          0          2  8.34 / 10.00         0.74
    # rename           61          0          0  7.31 /  --           0.09
    # reseed           61          0          0  7.58 /  --           0.47
    edits = {
        "internal_lib__thread__ThreadId_unbox_axiom_definition": EditAction.ERASE,
        "prelude_fuel_defaults": EditAction.INSTANTIATE,
        "internal_ens__core!num.impl&__11.wrapping_sub._definition": EditAction.INSTANTIATE,
    }
    dbg.do_edits(edits)
    # --------------------------------------------------------------------------------

    dbg.save_edit_report()


if __name__ == "__main__":
    set_param(proof=True)
    eval(sys.argv[1] + "()")
