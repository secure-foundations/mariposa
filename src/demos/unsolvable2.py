def unsolvable2():
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_all_single_edits()
    # total = len(dbg.rank)

    return [
        "156ec3ef1952502aa201ecb51be9fd06",
        "cecde024a96e1c70930f5bbdc2a26ee4",
        "8ef9fde14bb20ea029e165a3d3020e22",
        "00fea64883221acfd4e314121b2c8ece",
    ]