from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unsolvable1(q):

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  8.96 / 10.00         0.64
    # rename            0          0         61  --  / 10.00          0
    # reseed            0          0         61  --  / 10.00          0

    dbg = Debugger3(q, clear_edits=False)
    # dbg.make_single_edits_project()

    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_aggressive_edits()

    # --------------------------------------------------------------------------------
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  8.03 /  --           0.65
    # rename           61          0          0  8.50 /  --           0.18
    # reseed           61          0          0  8.49 /  --           0.12

    # edits = {
    #     "internal_lib!page_organization.valid_ll.?_definition": EditAction.INSTANTIATE,
    # }
    # dbg.test_edit(edits)
    # # --------------------------------------------------------------------------------

    # edits = {
    #     "internal_lib!page_organization.PageOrg.impl&__4.free_to_unused_queue_strong.?_definition": EditAction.INSTANTIATE,
    # }
    # dbg.test_edit(edits)

    # # --------------------------------------------------------------------------------
    # # dbg/mimalloc--segment__segment_span_free.smt2/edits/v1.smt2
    # # rcode: unsat
    # # time: 4.68

    # # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # # ----------  -------  ---------  ---------  ------------------  -----
    # # shuffle          61          0          0  7.63 /  --           0.82
    # # rename           61          0          0  8.40 /  --           0.13
    # # reseed           61          0          0  8.37 /  --           0.18

    # edits = {
    #     "internal_lib!page_organization.valid_ll.?_definition": EditAction.INSTANTIATE,
    #     "internal_vstd__seq__Seq<lib!types.PageQueue.>_box_axiom_definition": EditAction.ERASE,
    # }
    # dbg.test_edit(edits)
    # # --------------------------------------------------------------------------------

    # for ei in dbg.get_passing_edits()[:20]:
    #     print(ei.time, ei.path, ei.edit)