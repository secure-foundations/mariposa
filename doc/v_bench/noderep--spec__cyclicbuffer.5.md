orig path: `data/projs/v_bench/base.z3/noderep--spec__cyclicbuffer.5.smt2`

core path: `data/projs/v_bench/core.z3/noderep--spec__cyclicbuffer.5.smt2`

core qid count: 11

trace path: `reseed.9468741365361355720.unsat.39.trace`

| QID              |   Count | In Core   |
|------------------|---------|-----------|
| mariposa_qid_0   |      95 | Y         |
| mariposa_qid_6   |       3 | Y         |
| mariposa_qid_18  |       3 | Y         |
| mariposa_qid_286 |       2 | Y         |
| mariposa_qid_287 |       2 | N         |
| mariposa_qid_37  |       2 | Y         |
| mariposa_qid_40  |       2 | N         |
| mariposa_qid_22  |       1 | N         |
| mariposa_qid_25  |       1 | N         |
| mariposa_qid_8   |       1 | Y         |
| mariposa_qid_19  |       1 | Y         |
| mariposa_qid_35  |       1 | Y         |
| mariposa_qid_33  |       1 | Y         |
| mariposa_qid_38  |       1 | Y         |

removed:
```

(assert 
  (! 
    (forall 
      (
        (bits Int)
        (i Int)
      )
      (! 
        (= 
          (uInv bits i)
          (and 
            (<= 0 i)
            (< 
              i
              (uHi bits)
            )
          )
        )
        :pattern
        (
          (uInv bits i)
        )
        :skolemid
        skolem_prelude_u_inv
        :qid
        mariposa_qid_22
      )
    )
    :named
    mariposa_cid_113
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (x Int)
        (y Int)
      )
      (! 
        (=> 
          (and 
            (<= 0 x)
            (< 0 y)
          )
          (and 
            (<= 
              0
              (EucMod x y)
            )
            (< 
              (EucMod x y)
              y
            )
          )
        )
        :pattern
        (
          (EucMod x y)
        )
        :skolemid
        skolem_prelude_mod_unsigned_in_bounds
        :qid
        mariposa_qid_40
      )
    )
    :named
    mariposa_cid_136
  )
)
```

```

(assert 
  (! 
    (forall 
      (
        (logical! Poly)
        (buffer_size! Poly)
      )
      (! 
        (=> 
          (and 
            (has_type logical! INT)
            (has_type buffer_size! NAT)
          )
          (<= 
            0
            (lib!spec.cyclicbuffer.log_entry_idx.? logical! buffer_size!)
          )
        )
        :pattern
        (
          (lib!spec.cyclicbuffer.log_entry_idx.? logical! buffer_size!)
        )
        :skolemid
        skolem_internal_lib!spec.cyclicbuffer.log_entry_idx.?_pre_post_definition
        :qid
        mariposa_qid_287
      )
    )
    :named
    mariposa_cid_939
  )
)
```

