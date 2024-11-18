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
    
    # /src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i data/projs/mimalloc__page_organization__PageOrg_69_smt2_single_edits_filtered/base.z3

    # | category   |   count | percentage   |
    # |------------|---------|--------------|
    # | unstable   |      34 | 70.83 %      |
    # | stable     |      14 | 29.17 %      |
    # | total      |      48 | 100.00 %     |
