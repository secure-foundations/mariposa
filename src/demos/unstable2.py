def unstable2():
    # this is an example which is easy to fix

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  7.64 / 10.00         1.42
    # rename            0          0         61  --  / 10.00          0
    # reseed           23          0         38  8.40 / 10.00         0.99

    # dbg.clear_edits()
    # dbg.make_single_edits_project()

    hids = [
        "c8c0276b48013cbff3271be126250102",
        "2eaa4e7679b785205d1bf65aa347caeb",
        "69a33a04bfd4129b45b4ae4ac2ebd5db",
        "55767902edf633817b5bf27d807dd38b",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "14c9d9646647f3244dbfcf067485b893",
        "a68f3b186032f568a24c37ba401b650b",
        "616aa4efd392b6fa7abe747081b4cac4",
        "f54a5adabdb1a13fb4897ffbc8bc2325",
        "db05d58ee70c3c5ad5d92e558547e42d",
        "47d95ab7bc327ea87e010a452fbefb84",
        "f46e50cb7e4fef1a166c05de13072562",
        "c9ddded21d9bf651e16923f2aade07b8",
        "5d2ff894f9f0c527b40172bbfff1fbc3",
        "21fc2638c622257b0f3f2ddbd0e063f8",
    ]

    return hids