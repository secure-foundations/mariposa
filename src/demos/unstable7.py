
from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3

def unstable7(q):
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          38          0         23  8.68 / 10.00         0.93
    # rename           61          0          0  8.25 /  --           0.21
    # reseed           61          0          0  8.39 /  --           0.49

    dbg = Debugger3(q)

    # | category   |   count | percentage   |
    # |------------|---------|--------------|
    # | unstable   |      25 | 73.53 %      |
    # | stable     |       9 | 26.47 %      |
    # | total      |      34 | 100.00 %     |
