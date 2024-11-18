#!/usr/bin/env python3

import os, sys
from z3 import set_param
from base.solver import RCode
from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3
from proof_builder import QunatInstInfo
from query_editor import BasicQueryWriter
from random import sample
from demos.unstable7 import unstable7

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

    dbg.try_random_edits()


def unstable1():
    # this is an example where z3 gives up too early

    q = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
    dbg = Debugger3(q)

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

    dbg.test_edit(edit_ids)


def unstable2():
    # this is an example which is easy to fix

    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  7.64 / 10.00         1.42
    # rename            0          0         61  --  / 10.00          0
    # reseed           23          0         38  8.40 / 10.00         0.99

    dbg = Debugger3(q)

    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_ranked_edits()

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2/edits/v2.smt2
    # rcode: unsat
    # time: 1.86

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  3.63 /  --           1.01
    # rename           61          0          0  3.17 /  --           0.05
    # reseed           61          0          0  3.36 /  --           0.22

    edits = {"prelude_u_clip": EditAction.ERASE}
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------

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
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--page_organization__PageOrg__impl__4__take_page_from_unused_queue_ll_inv_valid_unused.smt2/edits/v1.smt2
    # rcode: unsat
    # time: 3.69

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  4.16 /  --           1.1
    # rename           61          0          0  6.23 /  --           0.14
    # reseed           61          0          0  4.38 /  --           1.04

    edits = {
        "internal_lib!page_organization.PageOrg.impl&__4.good_range0.?_definition": EditAction.ERASE
    }
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------


def unstable3():
    # FIXME: this report makes no sense

    q = "data/projs/v_systems/base.z3/mimalloc--commit_segment.1.smt2"
    dbg = Debugger3(q, False, True)

    dbg.print_status()
    dbg.try_ranked_edits()


def unstable4():
    # this is an easy example

    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg.69.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          44          0         17  7.27 / 10.00         1.76
    # rename            0          0         61  --  / 10.00          0
    # reseed           16          0         45  7.71 / 10.00         1.12

    dbg = Debugger3(q)
    # dbg.save_report()
    # dbg.clear_edits()
    dbg.try_aggressive_edit()
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
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------

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
    dbg.test_edit(edits)
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
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------


def unstable5():
    q = "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.5.smt2"
    pass


def unstable6():
    # FIXME: fail to build proof

    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg__impl__4__merge_with_before_ll_inv_valid_unused.smt2"
    dbg = Debugger3(q, True, False)

    dbg.try_ranked_edits()



def unsolvable1():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  8.96 / 10.00         0.64
    # rename            0          0         61  --  / 10.00          0
    # reseed            0          0         61  --  / 10.00          0

    dbg = Debugger3(q)
    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_aggressive_edits()

    # --------------------------------------------------------------------------------
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  8.03 /  --           0.65
    # rename           61          0          0  8.50 /  --           0.18
    # reseed           61          0          0  8.49 /  --           0.12

    edits = {
        "internal_lib!page_organization.valid_ll.?_definition": EditAction.INSTANTIATE,
    }
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------

    edits = {
        "internal_lib!page_organization.PageOrg.impl&__4.free_to_unused_queue_strong.?_definition": EditAction.INSTANTIATE,
    }
    dbg.test_edit(edits)

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/v1.smt2
    # rcode: unsat
    # time: 4.68

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  7.63 /  --           0.82
    # rename           61          0          0  8.40 /  --           0.13
    # reseed           61          0          0  8.37 /  --           0.18

    edits = {
        "internal_lib!page_organization.valid_ll.?_definition": EditAction.INSTANTIATE,
        "internal_vstd__seq__Seq<lib!types.PageQueue.>_box_axiom_definition": EditAction.ERASE,
    }
    dbg.test_edit(edits)
    # --------------------------------------------------------------------------------

    for ei in dbg.get_passing_edits()[:20]:
        print(ei.time, ei.path, ei.edit)


def unsolvable3():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2"
    dbg = Debugger3(q)

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_all_single_edits()

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--queues__page_queue_push_back.smt2/edits/v1.smt2
    # rcode: unsat
    # time: 3.44

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  6.12 /  --           0.56
    # rename           61          0          0  6.35 /  --           0.12
    # reseed           61          0          0  6.43 /  --           0.07

    # edits = {
    #     "internal_lib!page_organization.PageOrg.impl&__4.valid_used_page.?_definition": EditAction.INSTANTIATE,
    # }
    # dbg.test_edit(edits)
    # --------------------------------------------------------------------------------
    # dbg.try_random_edits()


def unsolvable5():
    q = "data/projs/v_systems/base.z3/mimalloc--segment.1.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           5          0         56  9.61 / 10.00         0.12
    # rename            1          0         60  10.00 / 10.00        0
    # reseed            5          0         56  9.35 / 10.00         0.21

    dbg = Debugger3(q)
    # dbg.clear_edits()
    # dbg.try_all_single_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  7.07 /  --           1.08
    # rename           61          0          0  6.49 /  --           0.16
    # reseed           61          0          0  6.71 /  --           0.8

    edits = {
        "internal_lib!page_organization.valid_ll.?_definition": EditAction.ERASE,
        "internal_lib__types__Local_box_axiom_definition": EditAction.INSTANTIATE,
        'internal_vstd!map.impl&__0.dom.?_pre_post_definition': EditAction.INSTANTIATE,
        'internal_vstd!seq.Seq.index.?_pre_post_definition': EditAction.INSTANTIATE,
    }

    dbg.test_edit(edits)

    # dbg.try_aggressive_edits()
    # dbg.try_random_edits()

    for ei in dbg.get_passing_edits()[:20]:
        print(ei.as_report())


def unsolvable6():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_remove.smt2"
    dbg = Debugger3(q)

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_all_single_edits()

    # dbg.print_status()

    # # --------------------------------------------------------------------------------
    # # dbg/mimalloc--queues__page_queue_remove.smt2/edits/v27.smt2
    # # rcode: unsat
    # # time: 3.89

    # # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # # ----------  -------  ---------  ---------  ------------------  -----
    # # shuffle          59          0          2  8.34 / 10.00         0.74
    # # rename           61          0          0  7.31 /  --           0.09
    # # reseed           61          0          0  7.58 /  --           0.47

    # edits = {
    #     "internal_lib__thread__ThreadId_unbox_axiom_definition": EditAction.ERASE,
    #     "prelude_fuel_defaults": EditAction.INSTANTIATE,
    #     "internal_ens__core!num.impl&__11.wrapping_sub._definition": EditAction.INSTANTIATE,
    # }
    # dbg.test_edit(edits)
    # # --------------------------------------------------------------------------------
    for ei in dbg.get_passing_edits()[:20]:
        print(ei.time, ei.path, ei.edit)

def anvil1():
    q = "data/projs/anvil/base.z3/rabbitmq-log-rabbitmq_controller__proof__helper_invariants__validation__lemma_always_stateful_set_in_create_request_msg_satisfies_unchangeable.smt2"
    dbg = Debugger3(q, overwrite_reports=False)

    # dbg.test_edit({
    #     "internal_rabbitmq_controller!kubernetes_api_objects.spec.dynamic.DynamicObjectView./DynamicObjectView_constructor_definition": EditAction.INSTANTIATE,
    # })

if __name__ == "__main__":
    set_param(proof=True)
    eval(sys.argv[1] + "()")
