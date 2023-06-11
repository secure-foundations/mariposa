(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid
    prelude_fuel_defaults
    :skolemid
    skolem_prelude_fuel_defaults
))))
(declare-sort Char 0)
(declare-fun char%from_unicode (Int) Char)
(declare-fun char%to_unicode (Char) Int)
(declare-sort StrSlice 0)
(declare-fun str%strslice_is_ascii (StrSlice) Bool)
(declare-fun str%strslice_len (StrSlice) Int)
(declare-fun str%strslice_get_char (StrSlice Int) Char)
(declare-fun str%new_strlit (Int) StrSlice)
(declare-fun str%from_strlit (StrSlice) Int)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun S (StrSlice) Poly)
(declare-fun %S (Poly) StrSlice)
(declare-fun C (Char) Poly)
(declare-fun %C (Poly) Char)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const STRSLICE Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert
 (forall ((i Int)) (= i (const_int (CONST_INT i))))
)
(assert
 (has_type (B true) BOOL)
)
(assert
 (has_type (B false) BOOL)
)
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid
   prelude_as_type
   :skolemid
   skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid
   prelude_mk_fun
   :skolemid
   skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid
   prelude_unbox_box_bool
   :skolemid
   skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid
   prelude_unbox_box_int
   :skolemid
   skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid
   prelude_box_unbox_bool
   :skolemid
   skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid
   prelude_box_unbox_int
   :skolemid
   skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid
   prelude_box_unbox_nat
   :skolemid
   skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid
   prelude_box_unbox_uint
   :skolemid
   skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid
   prelude_box_unbox_sint
   :skolemid
   skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Int)) (!
   (= (str%from_strlit (str%new_strlit x)) x)
   :pattern ((str%new_strlit x))
   :qid
   prelude_strlit_injective
   :skolemid
   skolem_prelude_strlit_injective
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x STRSLICE)
    (= x (S (%S x)))
   )
   :pattern ((has_type x STRSLICE))
   :qid
   prelude_box_unbox_strslice
   :skolemid
   skolem_prelude_box_unbox_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (= x (%S (S x)))
   :pattern ((S x))
   :qid
   prelude_unbox_box_strslice
   :skolemid
   skolem_prelude_unbox_box_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (has_type (S x) STRSLICE)
   :pattern ((has_type (S x) STRSLICE))
   :qid
   prelude_has_type_strslice
   :skolemid
   skolem_prelude_has_type_strslice
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid
   prelude_nat_clip
   :skolemid
   skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid
   prelude_u_clip
   :skolemid
   skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid
   prelude_i_clip
   :skolemid
   skolem_prelude_i_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid
   prelude_u_inv
   :skolemid
   skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid
   prelude_i_inv
   :skolemid
   skolem_prelude_i_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid
   prelude_has_type_int
   :skolemid
   skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid
   prelude_has_type_nat
   :skolemid
   skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid
   prelude_has_type_uint
   :skolemid
   skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid
   prelude_has_type_sint
   :skolemid
   skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid
   prelude_unbox_int
   :skolemid
   skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid
   prelude_unbox_uint
   :skolemid
   skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid
   prelude_unbox_sint
   :skolemid
   skolem_prelude_unbox_sint
)))
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid
   prelude_mul
   :skolemid
   skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid
   prelude_eucdiv
   :skolemid
   skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid
   prelude_eucmod
   :skolemid
   skolem_prelude_eucmod
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (C (%C x)))
   )
   :pattern ((has_type x CHAR))
   :qid
   prelude_box_unbox_char
   :skolemid
   skolem_prelude_box_unbox_char
)))
(assert
 (forall ((x Char)) (!
   (= x (%C (C x)))
   :pattern ((C x))
   :qid
   prelude_unbox_box_char
   :skolemid
   skolem_prelude_unbox_box_char
)))
(assert
 (forall ((x Char)) (!
   (has_type (C x) CHAR)
   :pattern ((has_type (C x) CHAR))
   :qid
   prelude_has_type_char
   :skolemid
   skolem_prelude_has_type_char
)))
(assert
 (forall ((x Int)) (!
   (= (char%to_unicode (char%from_unicode x)) x)
   :pattern ((char%from_unicode x))
   :qid
   prelude_char_injective
   :skolemid
   skolem_prelude_char_injective
)))
(assert
 (forall ((c Char)) (!
   (and
    (<= 0 (char%to_unicode c))
    (< (char%to_unicode c) (uHi 32))
   )
   :pattern ((char%to_unicode c))
   :qid
   prelude_to_unicode_bounds
   :skolemid
   skolem_prelude_to_unicode_bounds
)))
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid
   prelude_check_decreases
   :skolemid
   skolem_prelude_check_decreases
)))
(declare-fun height (Poly) Int)
(assert
 (forall ((x Poly)) (!
   (<= 0 (height x))
   :pattern ((height x))
   :qid
   prelude_height
   :skolemid
   skolem_prelude_height
)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun closure_req (Type Type Poly Poly) Bool)
(declare-fun closure_ens (Type Type Poly Poly Poly) Bool)

;; MODULE ''
;; rust_verify/example/bitvector_equivalence.rs:68:9: 68:15 (#0)

;; Fuel
(declare-const fuel%bitvector_equivalence!equal_lower_n_bits. FuelId)
(assert
 (distinct fuel%bitvector_equivalence!equal_lower_n_bits.)
)

;; Datatypes
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ tuple%0.)) (!
   (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@)))
   :pattern ((Poly%tuple%0. x@))
   :qid
   internal_crate__tuple__0_box_axiom_definition
   :skolemid
   skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%tuple%0.)
    (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))
   )
   :pattern ((has_type x@ TYPE%tuple%0.))
   :qid
   internal_crate__tuple__0_unbox_axiom_definition
   :skolemid
   skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x@ tuple%0.)) (!
   (has_type (Poly%tuple%0. x@) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.))
   :qid
   internal_crate__tuple__0_has_type_always_definition
   :skolemid
   skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Function-Decl bitvector_equivalence::equal_lower_n_bits
(declare-fun bitvector_equivalence!equal_lower_n_bits.? (Poly Poly Poly) Bool)

;; Function-Specs bitvector_equivalence::equal_lower_n_bits
(declare-fun req%bitvector_equivalence!equal_lower_n_bits. (Poly Poly Poly) Bool)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((a~2@ Poly) (b~4@ Poly) (n~6@ Poly)) (!
   (= (req%bitvector_equivalence!equal_lower_n_bits. a~2@ b~4@ n~6@) (=>
     %%global_location_label%%0
     (<= (%I n~6@) 32)
   ))
   :pattern ((req%bitvector_equivalence!equal_lower_n_bits. a~2@ b~4@ n~6@))
   :qid
   internal_req__bitvector_equivalence!equal_lower_n_bits._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equal_lower_n_bits._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof_increment_bv
(declare-fun req%bitvector_equivalence!equivalence_proof_increment_bv. (Int Int Int)
 Bool
)
(declare-const %%global_location_label%%1 Bool)
(declare-const %%global_location_label%%2 Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof_increment_bv. a~2@ b~4@ n~6@) (and
     (=>
      %%global_location_label%%1
      (< n~6@ 32)
     )
     (=>
      %%global_location_label%%2
      (= (uClip 32 (uintand 32 (I a~2@) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I n~6@)))
            1
        ))))
       ) (uClip 32 (uintand 32 (I b~4@) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I n~6@)))
            1
     )))))))
     (=>
      %%global_location_label%%3
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I n~6@)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I n~6@)))))) 1)
   ))))
   :pattern ((req%bitvector_equivalence!equivalence_proof_increment_bv. a~2@ b~4@ n~6@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof_increment_bv._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof_increment_bv._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof_increment
(declare-fun req%bitvector_equivalence!equivalence_proof_increment. (Int Int Int)
 Bool
)
(declare-const %%global_location_label%%4 Bool)
(declare-const %%global_location_label%%5 Bool)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof_increment. a~2@ b~4@ n~6@) (and
     (=>
      %%global_location_label%%4
      (< n~6@ 32)
     )
     (=>
      %%global_location_label%%5
      (bitvector_equivalence!equal_lower_n_bits.? (I a~2@) (I b~4@) (I n~6@))
     )
     (=>
      %%global_location_label%%6
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I n~6@)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I n~6@)))))) 1)
   ))))
   :pattern ((req%bitvector_equivalence!equivalence_proof_increment. a~2@ b~4@ n~6@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof_increment._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof_increment._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof_lower_n
(declare-fun req%bitvector_equivalence!equivalence_proof_lower_n. (Int Int Int) Bool)
(declare-const %%global_location_label%%7 Bool)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof_lower_n. a~2@ b~4@ n~6@) (and
     (=>
      %%global_location_label%%7
      (<= n~6@ 32)
     )
     (=>
      %%global_location_label%%8
      (forall ((i~30$ Poly)) (!
        (=>
         (has_type i~30$ (UINT 32))
         (=>
          (< (%I i~30$) n~6@)
          (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I (%I i~30$)))))))
            1
           ) (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I (%I i~30$)))))))
            1
        ))))
        :pattern ((uClip 32 (uintshr 32 (I a~2@) (I (%I i~30$)))))
        :pattern ((uClip 32 (uintshr 32 (I b~4@) (I (%I i~30$)))))
        :qid
        user_bitvector_equivalence__equivalence_proof_lower_n_0
        :skolemid
        skolem_user_bitvector_equivalence__equivalence_proof_lower_n_0
   )))))
   :pattern ((req%bitvector_equivalence!equivalence_proof_lower_n. a~2@ b~4@ n~6@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof_lower_n._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof_lower_n._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof
(declare-fun req%bitvector_equivalence!equivalence_proof. (Int Int) Bool)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof. a~2@ b~4@) (=>
     %%global_location_label%%9
     (forall ((i~18$ Poly)) (!
       (=>
        (has_type i~18$ (UINT 32))
        (=>
         (< (%I i~18$) 32)
         (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I (%I i~18$)))))))
           1
          ) (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I (%I i~18$)))))))
           1
       ))))
       :pattern ((uClip 32 (uintshr 32 (I a~2@) (I (%I i~18$)))))
       :pattern ((uClip 32 (uintshr 32 (I b~4@) (I (%I i~18$)))))
       :qid
       user_bitvector_equivalence__equivalence_proof_1
       :skolemid
       skolem_user_bitvector_equivalence__equivalence_proof_1
   ))))
   :pattern ((req%bitvector_equivalence!equivalence_proof. a~2@ b~4@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof_bv
(declare-fun req%bitvector_equivalence!equivalence_proof_bv. (Int Int) Bool)
(declare-const %%global_location_label%%10 Bool)
(declare-const %%global_location_label%%11 Bool)
(declare-const %%global_location_label%%12 Bool)
(declare-const %%global_location_label%%13 Bool)
(declare-const %%global_location_label%%14 Bool)
(declare-const %%global_location_label%%15 Bool)
(declare-const %%global_location_label%%16 Bool)
(declare-const %%global_location_label%%17 Bool)
(declare-const %%global_location_label%%18 Bool)
(declare-const %%global_location_label%%19 Bool)
(declare-const %%global_location_label%%20 Bool)
(declare-const %%global_location_label%%21 Bool)
(declare-const %%global_location_label%%22 Bool)
(declare-const %%global_location_label%%23 Bool)
(declare-const %%global_location_label%%24 Bool)
(declare-const %%global_location_label%%25 Bool)
(declare-const %%global_location_label%%26 Bool)
(declare-const %%global_location_label%%27 Bool)
(declare-const %%global_location_label%%28 Bool)
(declare-const %%global_location_label%%29 Bool)
(declare-const %%global_location_label%%30 Bool)
(declare-const %%global_location_label%%31 Bool)
(declare-const %%global_location_label%%32 Bool)
(declare-const %%global_location_label%%33 Bool)
(declare-const %%global_location_label%%34 Bool)
(declare-const %%global_location_label%%35 Bool)
(declare-const %%global_location_label%%36 Bool)
(declare-const %%global_location_label%%37 Bool)
(declare-const %%global_location_label%%38 Bool)
(declare-const %%global_location_label%%39 Bool)
(declare-const %%global_location_label%%40 Bool)
(declare-const %%global_location_label%%41 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof_bv. a~2@ b~4@) (and
     (=>
      %%global_location_label%%10
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 0)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 0)))))) 1)
     ))
     (=>
      %%global_location_label%%11
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 1)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 1)))))) 1)
     ))
     (=>
      %%global_location_label%%12
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 2)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 2)))))) 1)
     ))
     (=>
      %%global_location_label%%13
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 3)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 3)))))) 1)
     ))
     (=>
      %%global_location_label%%14
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 4)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 4)))))) 1)
     ))
     (=>
      %%global_location_label%%15
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 5)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 5)))))) 1)
     ))
     (=>
      %%global_location_label%%16
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 6)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 6)))))) 1)
     ))
     (=>
      %%global_location_label%%17
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 7)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 7)))))) 1)
     ))
     (=>
      %%global_location_label%%18
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 8)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 8)))))) 1)
     ))
     (=>
      %%global_location_label%%19
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 9)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 9)))))) 1)
     ))
     (=>
      %%global_location_label%%20
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 10)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 10)))))) 1)
     ))
     (=>
      %%global_location_label%%21
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 11)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 11)))))) 1)
     ))
     (=>
      %%global_location_label%%22
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 12)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 12)))))) 1)
     ))
     (=>
      %%global_location_label%%23
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 13)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 13)))))) 1)
     ))
     (=>
      %%global_location_label%%24
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 14)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 14)))))) 1)
     ))
     (=>
      %%global_location_label%%25
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 15)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 15)))))) 1)
     ))
     (=>
      %%global_location_label%%26
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 16)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 16)))))) 1)
     ))
     (=>
      %%global_location_label%%27
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 17)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 17)))))) 1)
     ))
     (=>
      %%global_location_label%%28
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 18)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 18)))))) 1)
     ))
     (=>
      %%global_location_label%%29
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 19)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 19)))))) 1)
     ))
     (=>
      %%global_location_label%%30
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 20)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 20)))))) 1)
     ))
     (=>
      %%global_location_label%%31
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 21)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 21)))))) 1)
     ))
     (=>
      %%global_location_label%%32
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 22)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 22)))))) 1)
     ))
     (=>
      %%global_location_label%%33
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 23)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 23)))))) 1)
     ))
     (=>
      %%global_location_label%%34
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 24)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 24)))))) 1)
     ))
     (=>
      %%global_location_label%%35
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 25)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 25)))))) 1)
     ))
     (=>
      %%global_location_label%%36
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 26)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 26)))))) 1)
     ))
     (=>
      %%global_location_label%%37
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 27)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 27)))))) 1)
     ))
     (=>
      %%global_location_label%%38
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 28)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 28)))))) 1)
     ))
     (=>
      %%global_location_label%%39
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 29)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 29)))))) 1)
     ))
     (=>
      %%global_location_label%%40
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 30)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 30)))))) 1)
     ))
     (=>
      %%global_location_label%%41
      (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I 31)))))) 1)
       (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I 31)))))) 1)
   ))))
   :pattern ((req%bitvector_equivalence!equivalence_proof_bv. a~2@ b~4@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof_bv._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof_bv._definition
)))

;; Function-Specs bitvector_equivalence::equivalence_proof_2
(declare-fun req%bitvector_equivalence!equivalence_proof_2. (Int Int) Bool)
(declare-const %%global_location_label%%42 Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (req%bitvector_equivalence!equivalence_proof_2. a~2@ b~4@) (=>
     %%global_location_label%%42
     (forall ((i~18$ Poly)) (!
       (=>
        (has_type i~18$ (UINT 32))
        (=>
         (< (%I i~18$) 32)
         (= (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I a~2@) (I (%I i~18$)))))))
           1
          ) (= (uClip 32 (uintand 32 (I 1) (I (uClip 32 (uintshr 32 (I b~4@) (I (%I i~18$)))))))
           1
       ))))
       :pattern ((uClip 32 (uintshr 32 (I a~2@) (I (%I i~18$)))))
       :pattern ((uClip 32 (uintshr 32 (I b~4@) (I (%I i~18$)))))
       :qid
       user_bitvector_equivalence__equivalence_proof_2_2
       :skolemid
       skolem_user_bitvector_equivalence__equivalence_proof_2_2
   ))))
   :pattern ((req%bitvector_equivalence!equivalence_proof_2. a~2@ b~4@))
   :qid
   internal_req__bitvector_equivalence!equivalence_proof_2._definition
   :skolemid
   skolem_internal_req__bitvector_equivalence!equivalence_proof_2._definition
)))

;; Function-Axioms bitvector_equivalence::equal_lower_n_bits
(assert
 (fuel_bool_default fuel%bitvector_equivalence!equal_lower_n_bits.)
)
(assert
 (=>
  (fuel_bool fuel%bitvector_equivalence!equal_lower_n_bits.)
  (forall ((a~2@ Poly) (b~4@ Poly) (n~6@ Poly)) (!
    (= (bitvector_equivalence!equal_lower_n_bits.? a~2@ b~4@ n~6@) (= (uClip 32 (uintand
        32 (I (%I a~2@)) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I (%I n~6@)))) 1)))
       )
      ) (uClip 32 (uintand 32 (I (%I b~4@)) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I (%I n~6@))))
           1
    )))))))
    :pattern ((bitvector_equivalence!equal_lower_n_bits.? a~2@ b~4@ n~6@))
    :qid
    internal_bitvector_equivalence!equal_lower_n_bits.?_definition
    :skolemid
    skolem_internal_bitvector_equivalence!equal_lower_n_bits.?_definition
))))

;; Function-Axioms bitvector_equivalence::equivalence_proof_increment_bv
(declare-fun ens%bitvector_equivalence!equivalence_proof_increment_bv. (Int Int Int)
 Bool
)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof_increment_bv. a~2@ b~4@ n~6@) (= (uClip
      32 (uintand 32 (I a~2@) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I (uClip 32 (+ n~6@ 1)))))
          1
      ))))
     ) (uClip 32 (uintand 32 (I b~4@) (I (uClip 32 (- (uClip 32 (uintshl 32 (I 1) (I (uClip 32
              (+ n~6@ 1)
           )))
          ) 1
   )))))))
   :pattern ((ens%bitvector_equivalence!equivalence_proof_increment_bv. a~2@ b~4@ n~6@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof_increment_bv._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof_increment_bv._definition
)))

;; Function-Axioms bitvector_equivalence::equivalence_proof_increment
(declare-fun ens%bitvector_equivalence!equivalence_proof_increment. (Int Int Int)
 Bool
)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof_increment. a~2@ b~4@ n~6@) (bitvector_equivalence!equal_lower_n_bits.?
     (I a~2@) (I b~4@) (I (uClip 32 (+ n~6@ 1)))
   ))
   :pattern ((ens%bitvector_equivalence!equivalence_proof_increment. a~2@ b~4@ n~6@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof_increment._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof_increment._definition
)))

;; Function-Axioms bitvector_equivalence::equivalence_proof_lower_n
(declare-fun ens%bitvector_equivalence!equivalence_proof_lower_n. (Int Int Int) Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int) (n~6@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof_lower_n. a~2@ b~4@ n~6@) (bitvector_equivalence!equal_lower_n_bits.?
     (I a~2@) (I b~4@) (I n~6@)
   ))
   :pattern ((ens%bitvector_equivalence!equivalence_proof_lower_n. a~2@ b~4@ n~6@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof_lower_n._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof_lower_n._definition
)))

;; Function-Axioms bitvector_equivalence::equivalence_proof
(declare-fun ens%bitvector_equivalence!equivalence_proof. (Int Int) Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof. a~2@ b~4@) (= a~2@ b~4@))
   :pattern ((ens%bitvector_equivalence!equivalence_proof. a~2@ b~4@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof._definition
)))

;; Function-Axioms bitvector_equivalence::equivalence_proof_bv
(declare-fun ens%bitvector_equivalence!equivalence_proof_bv. (Int Int) Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof_bv. a~2@ b~4@) (= a~2@ b~4@))
   :pattern ((ens%bitvector_equivalence!equivalence_proof_bv. a~2@ b~4@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof_bv._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof_bv._definition
)))

;; Function-Axioms bitvector_equivalence::equivalence_proof_2
(declare-fun ens%bitvector_equivalence!equivalence_proof_2. (Int Int) Bool)
(assert
 (forall ((a~2@ Int) (b~4@ Int)) (!
   (= (ens%bitvector_equivalence!equivalence_proof_2. a~2@ b~4@) (= a~2@ b~4@))
   :pattern ((ens%bitvector_equivalence!equivalence_proof_2. a~2@ b~4@))
   :qid
   internal_ens__bitvector_equivalence!equivalence_proof_2._definition
   :skolemid
   skolem_internal_ens__bitvector_equivalence!equivalence_proof_2._definition
)))

;; Function-Def bitvector_equivalence::equivalence_proof_lower_n
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :smt.ematching false)
(set-option :smt.case_split 0)
(declare-const a~2@0 (_ BitVec 32))
(declare-const b~4@0 (_ BitVec 32))
(declare-const n~6@0 (_ BitVec 32))
(declare-const tmp%1@0 (_ BitVec 32))
(declare-const tmp%2@0 (_ BitVec 32))
(assert
 true
)
;; bitvector ensures not satisfied
(declare-const %%location_label%%0 Bool)
(declare-const %%query%% Bool)
(assert
 (=>
  %%query%%
  (not (=>
    %%location_label%%0
    (= (bvand a~2@0 (bvsub (bvshl (_ bv1 32) (_ bv0 32)) (_ bv1 32))) (bvand b~4@0 (bvsub
       (bvshl (_ bv1 32) (_ bv0 32)) (_ bv1 32)
)))))))
(get-info :version)
(assert
 %%query%%
)
(set-option :rlimit 30000000)
(check-sat)
(set-option :rlimit 0)
