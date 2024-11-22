
from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3

def unstable7(q):
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          38          0         23  8.68 / 10.00         0.93
    # rename           61          0          0  8.25 /  --           0.21
    # reseed           61          0          0  8.39 /  --           0.49

    dbg = Debugger3(q)

    hids = [
        "5f4e1cfe6fc8b8b7f0189a7889c5db1d",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "277af7e1297a79ca3e6c2c3f9ed1d85e",
        "40402b63c99650b2f878b13c20156c92",
        "5bfd00d2a337c0c3b3ee8e71b8afb89a",
        "ea25836c463c6f3764ddb2d9dd862818",
        "13231273f4fa5f30833d5d9dcae90823",
        "53b4d3a10c289f47a1fbe69e0a8e8b45",
    ]
    
    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())
