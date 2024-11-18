
from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3

def unstable7():
    q = "data/projs/v_systems/base.z3/mimalloc--segment__span_queue_delete.smt2"

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          38          0         23  8.68 / 10.00         0.93
    # rename           61          0          0  8.25 /  --           0.21
    # reseed           61          0          0  8.39 /  --           0.49

    dbg = Debugger3(q)
    # dbg.clear_edits()
    # dbg.try_all_single_edits()
    # dbg.try_less_random_edits(size=3)
    # dbg.try_ranked_edits()

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v50.smt2
    # rcode: unsat
    # time: 5.49

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          58          0          3  7.93 / 10.00         0.91
    # rename           61          0          0  6.91 /  --           0.07
    # reseed           61          0          0  7.08 /  --           0.17

    edit = {
        'prelude_unbox_box_int': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------


    # FIXME: non-solution
    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v626.smt2
    # rcode: unsat
    # time: 5.56

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  6.99 /  --           0.4
    # rename           61          0          0  7.28 /  --           0.1
    # reseed           61          0          0  7.24 /  --           0.07

    edit = {
        'prelude_fuel_defaults': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------


    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v648.smt2
    # rcode: unsat
    # time: 5.96

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          60          0          1  7.62 / 10.00         0.44
    # rename           61          0          0  7.52 /  --           0.07
    # reseed           61          0          0  7.74 /  --           0.44

    edit = {
        'internal_lib!types.impl&__13.wf.?_definition': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------


    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v343.smt2
    # rcode: unsat
    # time: 6.29

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          58          0          3  9.11 / 10.00         0.44
    # rename           61          0          0  8.68 /  --           0.06
    # reseed           61          0          0  9.21 /  --           0.45

    edit = {
        'internal_lib!types.HeapSharedAccess./HeapSharedAccess/points_to_accessor_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v657.smt2
    # rcode: unsat
    # time: 4.8

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  9.08 /  --           0.43
    # rename           61          0          0  8.67 /  --           0.1
    # reseed           61          0          0  9.31 /  --           0.49

    edit = {
        'internal_lib__tokens__SegmentState_box_axiom_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v187.smt2
    # rcode: unsat
    # time: 6.08

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  8.43 /  --           0.28
    # rename           61          0          0  8.36 /  --           0.15
    # reseed           61          0          0  8.49 /  --           0.23

    edit = {
        'internal_lib!os_mem.impl&__0.range_os_rw.?_definition': EditAction.ERASE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------


    # --------------------------------------------------------------------------------
    # dbg/mimalloc--segment__span_queue_delete.smt2/edits/v651.smt2
    # rcode: unsat
    # time: 5.75

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          61          0          0  7.78 /  --           0.19
    # rename           61          0          0  7.25 /  --           0.11
    # reseed           61          0          0  7.48 /  --           0.21

    edit = {
        'prelude_u_inv': EditAction.INSTANTIATE
    }
    dbg.test_edit(edit)
    # --------------------------------------------------------------------------------

    # for ei in dbg.get_passing_edits()[:20]:
    #     print(ei.as_report())
