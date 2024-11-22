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

    # edits = {
    #     "internal_lib!page_organization.valid_ll.?_definition": EditAction.ERASE,
    #     "internal_lib__types__Local_box_axiom_definition": EditAction.INSTANTIATE,
    #     "internal_vstd!map.impl&__0.dom.?_pre_post_definition": EditAction.INSTANTIATE,
    #     "internal_vstd!seq.Seq.index.?_pre_post_definition": EditAction.INSTANTIATE,
    # }

    # dbg.test_edit(edits)

def unsolvable5_30(q):
    dbg = Debugger3(q)

    hids = [
        "8bfcccdd7285aab9bd4586a25ea93d52",
        "b605f8f7ec29cd2341162cf406513b0f",
        "5033af319e870f908ea2a303a9b00c65",
        "b21f2d585ce56fb817a99627f150da86",
        "c59d7b4f9f210ed28aa9c494e093eec0",
        "0752aec79b3ae27d0c8feef236538083",
        "ea25836c463c6f3764ddb2d9dd862818",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "156ec3ef1952502aa201ecb51be9fd06",
        "57c9ca1ee7df620f2c2d756243766790",
        "e4c95321c851c6599777e2ce331449f9",
    ]

    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())
