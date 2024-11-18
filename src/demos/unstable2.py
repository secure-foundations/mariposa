from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unstable2(q):
    # this is an example which is easy to fix

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  7.64 / 10.00         1.42
    # rename            0          0         61  --  / 10.00          0
    # reseed           23          0         38  8.40 / 10.00         0.99

    dbg = Debugger3(q)

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

    for ei in dbg.get_passing_edits()[:20]:
        print(ei.as_report())
