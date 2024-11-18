from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unstable4(q):
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          44          0         17  7.27 / 10.00         1.76
    # rename            0          0         61  --  / 10.00          0
    # reseed           16          0         45  7.71 / 10.00         1.12

    dbg = Debugger3(q)
    # dbg.make_single_edits_project()
    
    hids = [
        "616aa4efd392b6fa7abe747081b4cac4",
        "e69a5be35933b1fd86d2ff41a2c15fad",
        "21fc2638c622257b0f3f2ddbd0e063f8",
        "f46e50cb7e4fef1a166c05de13072562",
        "a68f3b186032f568a24c37ba401b650b",
        "737712cfcc854caa2b993c9c4f328b3a",
        "687784c3b0dc1ae55a3361e9a1ff3421",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "114f2de392422e8afbd6b2396ee1a215",
        "14c9d9646647f3244dbfcf067485b893",
        "4de132e2e4cf6f50e5e1bb17be73fd8b",
        "6cf7ec7c0ee246b71aec858053e45ea3",
        "4feca0abbe2fbe2cf7e70feb3808f206",
        "d2d624a7233e6b10d8068576821fc1b4",
    ]

    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())

    # ./src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i data/projs/mimalloc__page_organization__PageOrg_69_smt2_single_edits_filtered/base.z3

    # | category   |   count | percentage   |
    # |------------|---------|--------------|
    # | unstable   |      34 | 70.83 %      |
    # | stable     |      14 | 29.17 %      |
    # | total      |      48 | 100.00 %     |
