orig path: `data/projs/v_bench/base.z3/mimalloc--commit_segment.1.smt2`

core path: `data/projs/v_bench/core.z3/mimalloc--commit_segment.1.smt2`

core qid count: 42

trace path: `shuffle.376870484233043197.unknown.5104.trace`

| QID               |   Count | In Core   |
|-------------------|---------|-----------|
| mariposa_qid_0    |     262 | Y         |
| mariposa_qid_33   |     139 | Y         |
| mariposa_qid_19   |     125 | Y         |
| mariposa_qid_22   |      97 | Y         |
| mariposa_qid_36   |      85 | Y         |
| mariposa_qid_39   |      85 | Y         |
| mariposa_qid_6    |      64 | Y         |
| mariposa_qid_34   |      56 | Y         |
| mariposa_qid_38   |      48 | Y         |
| mariposa_qid_35   |      48 | Y         |
| mariposa_qid_5    |      47 | Y         |
| mariposa_qid_1219 |      44 | Y         |
| mariposa_qid_1109 |      32 | Y         |
| mariposa_qid_37   |      29 | Y         |
| mariposa_qid_40   |      29 | Y         |
| mariposa_qid_245  |      23 | Y         |
| mariposa_qid_246  |      23 | Y         |
| mariposa_qid_8    |      22 | Y         |
| mariposa_qid_1107 |      21 | Y         |
| mariposa_qid_1493 |      21 | Y         |
| mariposa_qid_2    |      21 | Y         |
| mariposa_qid_247  |      20 | Y         |
| mariposa_qid_25   |      18 | Y         |
| mariposa_qid_45   |      17 | Y         |
| mariposa_qid_4    |      17 | Y         |
| mariposa_qid_7    |      13 | N         |
| mariposa_qid_49   |      13 | N         |
| mariposa_qid_48   |      12 | N         |
| mariposa_qid_46   |      12 | N         |
| mariposa_qid_1138 |      11 | N         |
| mariposa_qid_17   |      11 | Y         |
| mariposa_qid_1455 |      11 | Y         |
| mariposa_qid_1220 |      11 | Y         |
| mariposa_qid_62   |      11 | Y         |
| mariposa_qid_1453 |      10 | Y         |
| mariposa_qid_1494 |      10 | Y         |
| mariposa_qid_824  |       9 | Y         |
| mariposa_qid_1454 |       7 | Y         |
| mariposa_qid_821  |       7 | Y         |
| mariposa_qid_826  |       6 | Y         |
| mariposa_qid_1137 |       6 | Y         |
| mariposa_qid_1192 |       4 | N         |
| mariposa_qid_1193 |       4 | N         |
| mariposa_qid_1452 |       3 | Y         |
| mariposa_qid_1106 |       2 | Y         |
| mariposa_qid_1439 |       1 | Y         |
| mariposa_qid_1078 |       1 | Y         |
| mariposa_qid_731  |       1 | N         |
| mariposa_qid_277  |       1 | N         |
| mariposa_qid_278  |       1 | N         |
| mariposa_qid_730  |       1 | N         |

removed:
```

(assert 
  (! 
    (forall 
      (
        (x Poly)
      )
      (! 
        (=> 
          (has_type x BOOL)
          (= 
            x
            (B 
              (%B x)
            )
          )
        )
        :pattern
        (
          (has_type x BOOL)
        )
        :skolemid
        skolem_prelude_box_unbox_bool
        :qid
        mariposa_qid_7
      )
    )
    :named
    mariposa_cid_70
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (T%0&. Dcr)
        (T%0& Type)
        (T%1&. Dcr)
        (T%1& Type)
        (x %%Function%%)
      )
      (! 
        (=> 
          (forall 
            (
              (T%0 Poly)
            )
            (! 
              (=> 
                (has_type T%0 T%0&)
                (has_type 
                  (%%apply%%0 x T%0)
                  T%1&
                )
              )
              :pattern
              (
                (has_type 
                  (%%apply%%0 x T%0)
                  T%1&
                )
              )
              :skolemid
              skolem_internal_crate__fun__1_constructor_inner_definition
              :qid
              mariposa_qid_47
            )
          )
          (has_type 
            (Poly%fun%1. 
              (mk_fun x)
            )
            (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)
          )
        )
        :pattern
        (
          (has_type 
            (Poly%fun%1. 
              (mk_fun x)
            )
            (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)
          )
        )
        :skolemid
        skolem_internal_crate__fun__1_constructor_definition
        :qid
        mariposa_qid_48
      )
    )
    :named
    mariposa_cid_1128
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (T%0&. Dcr)
        (T%0& Type)
        (T%1&. Dcr)
        (T%1& Type)
        (T%0 Poly)
        (x %%Function%%)
      )
      (! 
        (=> 
          (and 
            (has_type 
              (Poly%fun%1. x)
              (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)
            )
            (has_type T%0 T%0&)
          )
          (has_type 
            (%%apply%%0 x T%0)
            T%1&
          )
        )
        :pattern
        (
          (%%apply%%0 x T%0)
          (has_type 
            (Poly%fun%1. x)
            (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)
          )
        )
        :skolemid
        skolem_internal_crate__fun__1_apply_definition
        :qid
        mariposa_qid_49
      )
    )
    :named
    mariposa_cid_1129
  )
)
```

