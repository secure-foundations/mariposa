from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unsolvable3(q):
    dbg = Debugger3(q)

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_all_single_edits()

    # ./src/analysis_wizard.py basic -e verus_quick -s z3_4_13_0 -i data/projs/mimalloc__segment__segment_span_free_smt2_single_edits_filtered/base.z3

    for hid in [
        "31aea110cc8b02635c0b36e32ab6525b",
        "a02023e8e438808d0283121f667ff7d5",
        "7e71d6b8df68b2873510a96c541e743c",
    ]:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())
