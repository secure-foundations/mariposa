orig path: `data/projs/v_bench/base.z3/mimalloc--config.35.smt2`

core path: `data/projs/v_bench/core.z3/mimalloc--config.35.smt2`

core qid count: 7

trace path: `reseed.2150335716930368347.unsat.36.trace`

| QID              |   Count | In Core   |
|------------------|---------|-----------|
| mariposa_qid_0   |      34 | Y         |
| mariposa_qid_22  |      34 | Y         |
| mariposa_qid_19  |      20 | Y         |
| mariposa_qid_39  |       7 | Y         |
| mariposa_qid_36  |       7 | Y         |
| mariposa_qid_33  |       5 | N         |
| mariposa_qid_461 |       5 | N         |
| mariposa_qid_462 |       4 | N         |
| mariposa_qid_6   |       4 | N         |
| mariposa_qid_35  |       2 | Y         |
| mariposa_qid_38  |       2 | Y         |

removed:
```

(assert 
  (! 
    (forall 
      (
        (x Int)
        (y Int)
      )
      (! 
        (= 
          (Add x y)
          (+ x y)
        )
        :pattern
        (
          (Add x y)
        )
        :skolemid
        skolem_prelude_add
        :qid
        mariposa_qid_33
      )
    )
    :named
    mariposa_cid_129
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (V&. Dcr)
        (V& Type)
      )
      (! 
        (<= 
          0
          (vstd!layout.size_of.? V&. V&)
        )
        :pattern
        (
          (vstd!layout.size_of.? V&. V&)
        )
        :skolemid
        skolem_internal_vstd!layout.size_of.?_pre_post_definition
        :qid
        mariposa_qid_461
      )
    )
    :named
    mariposa_cid_1038
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (V&. Dcr)
        (V& Type)
      )
      (! 
        (<= 
          0
          (vstd!layout.align_of.? V&. V&)
        )
        :pattern
        (
          (vstd!layout.align_of.? V&. V&)
        )
        :skolemid
        skolem_internal_vstd!layout.align_of.?_pre_post_definition
        :qid
        mariposa_qid_462
      )
    )
    :named
    mariposa_cid_1040
  )
)
```

