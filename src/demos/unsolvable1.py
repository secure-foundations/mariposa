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

    hids = {
        "cecde024a96e1c70930f5bbdc2a26ee4", # TODO: non-solution
        "8a6096aa54667bcaefb0afeb4ad09a53", 
        "d916eb1e9c434023973994225f45a2e5",
    }

    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/cecde024a96e1c70930f5bbdc2a26ee4.smt2
    # rcode: unsat
    # time: 3.55


    edit = {
        'prelude_fuel_defaults': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/8a6096aa54667bcaefb0afeb4ad09a53.smt2
    # rcode: unsat
    # time: 4.43


    edit = {
        'internal_req__vstd!ptr.impl&__10.borrow._definition': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free.smt2/edits/d916eb1e9c434023973994225f45a2e5.smt2
    # rcode: unsat
    # time: 3.56


    edit = {
        'internal_ens__vstd!ptr.impl&__10.put._definition': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

