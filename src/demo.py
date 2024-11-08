#!/usr/bin/env python3

import os
from z3 import set_param
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


# def demo0():
#     v = VersionManager(
#         "data/projs/v_systems/base.z3/noderep--spec__cyclicbuffer.3.smt2"
#     )

#     dbg = Debugger3(v.get_query_path(), False, True)
#     diff = dbg.get_differ()
#     v.save_report(diff.get_report())

#     w = dbg.get_editor()
#     w.skolemize_qids(
#         {
#             "user_lib__spec__cyclicbuffer__log_entry_alive_wrap_around_51",
#         }
#     )

#     w.save(v.get_next_query_path())
#     v.update_version()

#     dbg = Debugger3(v.get_query_path(), False, True)
#     diff = dbg.get_differ()
#     v.save_report(diff.get_report())

#     w = dbg.get_editor()
#     w.instantiate_qids(
#         {
#             "prelude_eucmod",
#         }
#     )
#     w.save(v.get_next_query_path())

def demo1():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"
    dbg = Debugger3(q, False, True)
    dbg.save_report()
    dbg.try_random_edits()
    dbg.print_edit_report()

    # w = dbg.get_editor()
    # w.instantiate_qids(
    #     {
    #         "prelude_unbox_box_int",
    #         "internal_vstd!set.impl&__0.subset_of.?_definition",
    #     }
    # )
    # w.erase_qids(
    #     {
    #         "prelude_u_clip",
    #     }
    # )
    # w.save(v.get_next_query_path())

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  6.28 /  --           0.3
    # rename           61          0          0  6.02 /  --           0.08
    # reseed           61          0          0  6.22 /  --           0.33

    # v.update_version()
    # w.instantiate_qids(
    #     {
    #         "internal_lib!types.impl&__21.wf_main.?_definition",
    #     }
    # )
    # w.save(v.get_next_query_path())

    # alternative timeout: 10.0s
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           0          0         61  --  / 10.00             0
    # rename            0          0         61  --  / 10.00             0
    # reseed            0          0         61  --  / 10.00             0


def demo2():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__segment_span_free.smt2"

    dbg = Debugger3(q, False, True)
    dbg.save_report()
    dbg.try_random_edits()
    dbg.print_edit_report()

#     w.instantiate_qids(
#         {
#             "internal_vstd!set.impl&__0.subset_of.?_definition",
#         }
#     )

# def demo3():
#     v = VersionManager(
#         "data/projs/v_systems/base.z3/mimalloc--segment.1.smt2",
#     )
#     dbg = Debugger3(v.get_query_path(), False, True)
#     diff = dbg.get_differ()
#     v.save_report(diff.get_report())

#     w = dbg.get_editor()
#     actions = diff.get_actions()

#     edit_qids = [
#         "user_vstd__set__axiom_set_ext_equal_101",
#         "internal_vstd__set__Set<int.>_box_axiom_definition",
#     ]
#     edit_qids = {qid: actions[qid] for qid in edit_qids}

#     w.do_edits(edit_qids)
#     w.save(v.get_next_query_path())

#     # for _ in range(30):
#     #     edit_qids = sample(actions.keys(), 3)
#     #     edit_qids = {qid: actions[qid] for qid in edit_qids}
#     #     w.do_edits(edit_qids)

#     #     w.save(v.get_next_query_path())
#     #     v.update_version()
#     #     v.run_query()


# def demo4():
#     query = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_push_back.smt2"
#     v = VersionManager(query)

#     dbg = Debugger3(v.get_query_path(), False, True)
#     diff = dbg.get_differ()
#     v.save_report(diff.get_report())

#     w = dbg.get_editor()
#     actions = diff.get_actions()

#     edit_qids = [
#         "internal_lib!page_organization.PageOrg.impl&__4.valid_used_page.?_definition",
#         "internal_lib!atomic_ghost_modified.AtomicU64./AtomicU64/atomic_inv_accessor_definition",
#         "internal_vstd__ptr__PointsToData_unbox_axiom_definition",
#     ]
#     edit_qids = {qid: actions[qid] for qid in edit_qids}

#     w.do_edits(edit_qids)
#     w.save(v.get_next_query_path())

#     # for _ in range(30):
#     #     edit_qids = sample(actions.keys(), 3)
#     #     edit_qids = {qid: actions[qid] for qid in edit_qids}
#     #     w.do_edits(edit_qids)
#     #     w.save(v.get_next_query_path())
#     #     v.update_version()


# def demo5():
#     query = "data/projs/v_systems/base.z3/mimalloc--queues__page_queue_remove.smt2"
#     v = VersionManager(query)

#     dbg = Debugger3(v.get_query_path(), False, True)
#     diff = dbg.get_differ()
#     v.save_report(diff.get_report())

#     w = dbg.get_editor()
#     actions = diff.get_actions()

#     for _ in range(30):
#         edit_qids = sample(actions.keys(), 3)
#         edit_qids = {qid: actions[qid] for qid in edit_qids}
#         w.do_edits(edit_qids)

#         w.save(v.get_next_query_path())
#         v.update_version()
#         v.run_query()


# def demo6():
#     query = "data/projs/v_systems/base.z3/mimalloc--page_organization__PageOrg.69.smt2"
#     v = VersionManager(query)
#     dbg = Debugger3(v.get_query_path(), False, True)

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
