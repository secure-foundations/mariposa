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
        # "8a6096aa54667bcaefb0afeb4ad09a53", # TODO: non-solution
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "d916eb1e9c434023973994225f45a2e5",
    }

    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())
