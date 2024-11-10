#!/usr/bin/env python3

import os
from z3 import set_param
from base.solver import RCode
from debugger.trace_analyzer import EditAction
from debugger3 import Debugger3
from proof_builder import QunatInstInfo
from query_editor import BasicQueryWriter
from random import sample

from utils.system_utils import subprocess_run

TEMP = "temp"


def test0():
    q = "data/projs/v_systems/base.z3/ironsht--delegation_map_v.35.smt2"
    dbg = Debugger3(q, False, False)
    dbg.save_report()
    dbg.try_random_edits()
    dbg.print_edit_report()


def demo0():
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

    dbg.do_specific_edits(edit_ids)

    dbg.print_edit_report()


def demo1():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.try_random_edits()
    dbg.try_ranked_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          38          0         23  8.68 / 10.00         0.93
    # rename           61          0          0  8.25 /  --           0.21
    # reseed           61          0          0  8.39 /  --           0.49

    edit_ids = {'prelude_unbox_box_int'}
    # time to unsat: 3.88
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v3.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  7.94 /  --           0.76
    # rename           61          0          0  7.43 /  --           0.14
    # reseed           61          0          0  7.52 /  --           0.42

    dbg.do_specific_edits(edit_ids)

    edit_ids = {
        "prelude_unbox_box_int",
        "internal_vstd!set.impl&__0.subset_of.?_definition",
    }

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  8.07 /  --           0.73
    # rename           61          0          0  6.18 /  --           0.13
    # reseed           61          0          0  6.37 /  --           0.27

    dbg.do_specific_edits(edit_ids)

    edit_ids = {
        "internal_lib!types.impl&__21.wf_main.?_definition",
    }

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           0          0         61  --  / 10.00             0
    # rename            0          0         61  --  / 10.00             0
    # reseed            0          0         61  --  / 10.00             0

    dbg.do_specific_edits(edit_ids)

    dbg.print_edit_report()


def demo2():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.try_random_edits()
    # dbg.try_ranked_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  8.96 / 10.00         0.64
    # rename            0          0         61  --  / 10.00          0
    # reseed            0          0         61  --  / 10.00          0

    edit_ids = {'internal_vstd__set__Set<int.>_unbox_axiom_definition'}
    # time to unsat: 4.72
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/v14.smt2


    edit_ids = {"internal_vstd!set.impl&__0.subset_of.?_definition"}

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          42          3         16  8.11 / 8.49          2.23
    # rename           61          0          0  6.63 /  --           0.13
    # reseed           61          0          0  6.69 /  --           0.16

    dbg.do_specific_edits(edit_ids)

    edit_ids = {
        "internal_vstd!set.impl&__0.subset_of.?_definition",
        "user_vstd__std_specs__bits__axiom_u64_leading_zeros_44",
    }

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          46          6          9  8.41 / 6.17          2.68
    # rename           61          0          0  6.62 /  --           0.17
    # reseed           61          0          0  6.77 /  --           0.36

    dbg.do_specific_edits(edit_ids)

    dbg.print_edit_report()


def demo3():
    q = "data/projs/v_systems/base.z3/mimalloc--segment.1.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    dbg.try_ranked_edits()
    # dbg.try_random_edits()

    edit_qids = {
        "user_vstd__set__axiom_set_ext_equal_101",
        "internal_vstd__set__Set<int.>_box_axiom_definition",
    }

    dbg.do_specific_edits(edit_qids)

    dbg.print_edit_report()


def demo4():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    # dbg.try_random_edits()
    dbg.try_ranked_edits()

    # edit_qids = {
    #     "internal_lib!page_organization.PageOrg.impl&__4.valid_used_page.?_definition",
    #     "internal_lib!atomic_ghost_modified.AtomicU64./AtomicU64/atomic_inv_accessor_definition",
    #     "internal_vstd__ptr__PointsToData_unbox_axiom_definition",
    # }

    # w.do_edits(edit_qids)
    # dbg.print_edit_report()


def demo5():
    q = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_remove.smt2"

    dbg = Debugger3(q, False, True)
    # dbg.save_report()
    dbg.try_ranked_edits()
    # dbg.do_specific_edits(
    #     [
    #         "internal_vstd!seq.Seq.index.?_pre_post_definition",
    #         "prelude_add",
    #         "internal_vstd__set__Set<int.>_has_type_always_definition",
    #     ]
    # )
    # dbg.print_edit_report()


def demo6():
    q = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg.69.smt2"
    dbg = Debugger3(q, False, True)
    # dbg.save_report()
    # dbg.try_ranked_edits()
    # dbg.try_random_edits()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          44          0         17  7.27 / 10.00         1.76
    # rename            0          0         61  --  / 10.00          0
    # reseed           16          0         45  7.71 / 10.00         1.12

    edit_ids = {"prelude_u_clip"}
    # time to unsat: 2.29
    # dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v2.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  3.65 /  --           1.13
    # rename           61          0          0  4.00 /  --           0.06
    # reseed           61          0          0  4.52 /  --           0.65
    dbg.do_specific_edits(edit_ids)

    edit_ids = {
        "internal_lib!page_organization.PageOrg.impl&__4.good_range0.?_definition"
    }
    # time to unsat: 2.91
    # dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v1.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  4.45 / 10.00         1.42
    # rename           61          0          0  4.89 /  --           0.09
    # reseed           61          0          0  4.60 /  --           0.44

    dbg.do_specific_edits(edit_ids)

    edit_ids = {
        "prelude_u_clip",
        "internal_lib!page_organization.PageOrg.impl&__4.good_range0.?_definition",
    }
    # time to unsat: 2.96
    # dbg/mimalloc--page_organization__PageOrg.69.smt2/edits/v31.smt2

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  4.14 /  --           1.38
    # rename           61          0          0  4.90 /  --           0.07
    # reseed           61          0          0  4.54 /  --           0.53

    dbg.do_specific_edits(edit_ids)

    dbg.print_edit_report()


if __name__ == "__main__":
    set_param(proof=True)
    # test0()
    # demo0()
    # demo1()
    demo2()
    # demo3()
    # demo4()
    # demo5()
    # demo6()
