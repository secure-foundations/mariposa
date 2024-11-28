def unsolvable3():
    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle           6          0         55  9.92 / 10.00         0.03
    # rename           14          0         47  9.90 / 10.00         0.05
    # reseed            2          0         59  9.86 / 10.00         0.03

    # dbg.clear_edits()
    # dbg.try_all_single_edits()

    return [
        "31aea110cc8b02635c0b36e32ab6525b",
        "a02023e8e438808d0283121f667ff7d5",
        "7e71d6b8df68b2873510a96c541e743c",
    ]
