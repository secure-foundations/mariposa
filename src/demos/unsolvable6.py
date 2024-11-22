from debugger.trace_analyzer import EditAction
from debugger.debugger3 import Debugger3


def unsolvable6(q):
    dbg = Debugger3(q, clear_edits=False)

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_random_edits()
    # dbg.try_all_single_edits()

    # dbg.print_status()

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          59          0          2  8.34 / 10.00         0.66
    # rename           61          0          0  8.03 /  --           0.2
    # reseed           61          0          0  7.77 /  --           0.53

    hids = [
        "cecde024a96e1c70930f5bbdc2a26ee4", # FIXME: non-solution
        "e70928854d2f7167d339c013d74a3852",
    ]

    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())

    # # --------------------------------------------------------------------------------
    # # dbg/mimalloc--queues__page_queue_remove.smt2/edits/v27.smt2
    # # rcode: unsat
    # # time: 3.89

    # # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # # ----------  -------  ---------  ---------  ------------------  -----
    # # shuffle          59          0          2  8.34 / 10.00         0.74
    # # rename           61          0          0  7.31 /  --           0.09
    # # reseed           61          0          0  7.58 /  --           0.47

    # edits = {
    #     "internal_lib__thread__ThreadId_unbox_axiom_definition": EditAction.ERASE,
    #     "prelude_fuel_defaults": EditAction.INSTANTIATE,
    #     "internal_ens__core!num.impl&__11.wrapping_sub._definition": EditAction.INSTANTIATE,
    # }
    # dbg.test_edit(edits)
    # # --------------------------------------------------------------------------------

def unsolvable6_34(q):
    dbg = Debugger3(q)
    # dbg.clear_edits()
    # dbg.make_single_edits_project()

    hids = [
        "6cf7ec7c0ee246b71aec858053e45ea3",
        "084393290a77576b0c0ab3eb8417081f",
        "3ec2c9e9cfc5e34ddb4b00e3281b897e",
        "e70928854d2f7167d339c013d74a3852",
        "267a842dba755c448c31b7d7670aafdb",
        "19a52949cc3eb8bc1a48cb58e98d61c5",
        "d76b04092e4780308b5db84cca51f90a",
        "ad244932e26204073792eac0793d2460",
        "129a8d1ca37402bfc1ca3d70c8f07005",
        "e8e4e0ea0ce05aae17c33073a694ed02",
        "08618956326bebdf6274a91c9488d354",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "20e24a1ddead377dc8f8ec9ef731bc71",
        "5bfd00d2a337c0c3b3ee8e71b8afb89a",
        "ca57d5de3515444b571e38b43a211dcd",
        "159f4f6fd13f6791e0e0aa3c47056384",
    ]
    
    for hid in hids:
        ei = dbg.test_edit_with_id(hid)
        print(ei.as_report())
