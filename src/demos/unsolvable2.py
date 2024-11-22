from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unsolvable2(q):
    dbg = Debugger3(q)

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_all_single_edits()

    # print(dbg.differ.get_report_v3())

    for hid in [
        "156ec3ef1952502aa201ecb51be9fd06",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "8ef9fde14bb20ea029e165a3d3020e22",
        "00fea64883221acfd4e314121b2c8ece",
    ]:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free_coalesce_before.smt2/edits/156ec3ef1952502aa201ecb51be9fd06.smt2
    # rcode: unsat
    # time: 3.7



    edit = {
        'internal_lib!page_organization.valid_ll.?_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free_coalesce_before.smt2/edits/cecde024a96e1c70930f5bbdc2a26ee4.smt2
    # rcode: unsat
    # time: 2.26


    edit = {
        'prelude_fuel_defaults': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free_coalesce_before.smt2/edits/8ef9fde14bb20ea029e165a3d3020e22.smt2
    # rcode: unsat
    # time: 3.74


    edit = {
        'internal_lib!page_organization.PageOrg.impl&__4.ll_inv_valid_unused.?_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__segment_span_free_coalesce_before.smt2/edits/00fea64883221acfd4e314121b2c8ece.smt2
    # rcode: unsat
    # time: 4.41


    edit = {
        'internal_lib!page_organization.PageOrg.impl&__4.ll_inv_valid_unused2.?_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

