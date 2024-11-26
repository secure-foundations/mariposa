def unsolvable1():

    # mutation      unsat    unknown    timeout  mean (pass/fail)      std
    # ----------  -------  ---------  ---------  ------------------  -----
    # shuffle          33          0         28  8.96 / 10.00         0.64
    # rename            0          0         61  --  / 10.00          0
    # reseed            0          0         61  --  / 10.00          0

    hids = {
        "cecde024a96e1c70930f5bbdc2a26ee4", # TODO: non-solution
        "8a6096aa54667bcaefb0afeb4ad09a53", 
        "d916eb1e9c434023973994225f45a2e5",
    }

    return hids