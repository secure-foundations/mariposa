from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unsolvable5(q):
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
        "internal_vstd!map.impl&__0.dom.?_pre_post_definition": EditAction.INSTANTIATE,
        "internal_vstd!seq.Seq.index.?_pre_post_definition": EditAction.INSTANTIATE,
    }

    dbg.test_edit(edits)
