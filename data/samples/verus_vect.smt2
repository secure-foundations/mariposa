(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

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
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) fndef)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (I (%I x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
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
(declare-fun charClip (Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
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
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
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
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(assert
 (forall ((i Int)) (!
   (and
    (or
     (and
      (<= 0 (charClip i))
      (<= (charClip i) 55295)
     )
     (and
      (<= 57344 (charClip i))
      (<= (charClip i) 1114111)
    ))
    (=>
     (or
      (and
       (<= 0 i)
       (<= i 55295)
      )
      (and
       (<= 57344 i)
       (<= i 1114111)
     ))
     (= i (charClip i))
   ))
   :pattern ((charClip i))
   :qid prelude_char_clip
   :skolemid skolem_prelude_char_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((i Int)) (!
   (= (charInv i) (or
     (and
      (<= 0 i)
      (<= i 55295)
     )
     (and
      (<= 57344 i)
      (<= i 1114111)
   )))
   :pattern ((charInv i))
   :qid prelude_char_inv
   :skolemid skolem_prelude_char_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Int)) (!
   (=>
    (charInv x)
    (has_type (I x) CHAR)
   )
   :pattern ((has_type (I x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitxor x y))
   )
   :pattern ((uClip bits (bitxor x y)))
   :qid prelude_bit_xor_u_inv
   :skolemid skolem_prelude_bit_xor_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitxor x y))
   )
   :pattern ((iClip bits (bitxor x y)))
   :qid prelude_bit_xor_i_inv
   :skolemid skolem_prelude_bit_xor_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitor x y))
   )
   :pattern ((uClip bits (bitor x y)))
   :qid prelude_bit_or_u_inv
   :skolemid skolem_prelude_bit_or_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitor x y))
   )
   :pattern ((iClip bits (bitor x y)))
   :qid prelude_bit_or_i_inv
   :skolemid skolem_prelude_bit_or_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitand x y))
   )
   :pattern ((uClip bits (bitand x y)))
   :qid prelude_bit_and_u_inv
   :skolemid skolem_prelude_bit_and_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitand x y))
   )
   :pattern ((iClip bits (bitand x y)))
   :qid prelude_bit_and_i_inv
   :skolemid skolem_prelude_bit_and_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (<= 0 (%I y))
    )
    (uInv bits (bitshr x y))
   )
   :pattern ((uClip bits (bitshr x y)))
   :qid prelude_bit_shr_u_inv
   :skolemid skolem_prelude_bit_shr_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (<= 0 (%I y))
    )
    (iInv bits (bitshr x y))
   )
   :pattern ((iClip bits (bitshr x y)))
   :qid prelude_bit_shr_i_inv
   :skolemid skolem_prelude_bit_shr_i_inv
)))
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
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
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))

;; MODULE 'root module'

;; Fuel
(declare-const fuel%vstd!std_specs.option.impl&%0.is_Some. FuelId)
(declare-const fuel%vstd!std_specs.option.impl&%0.get_Some_0. FuelId)
(declare-const fuel%vstd!std_specs.option.spec_unwrap. FuelId)
(declare-const fuel%vstd!std_specs.vec.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!std_specs.vec.axiom_spec_len. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%4.view. FuelId)
(declare-const fuel%vstd!raw_ptr.axiom_ptr_mut_from_data. FuelId)
(declare-const fuel%vstd!raw_ptr.ptrs_mut_eq. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_index_decreases. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_empty. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_new_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_new_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_index_same. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_index_different. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_update_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_update_same. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_update_different. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal_deep. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_subrange_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_subrange_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_index1. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_index2. FuelId)
(declare-const fuel%vstd!slice.axiom_spec_len. FuelId)
(declare-const fuel%vstd!view.impl&%0.view. FuelId)
(declare-const fuel%vstd!view.impl&%2.view. FuelId)
(declare-const fuel%vstd!view.impl&%4.view. FuelId)
(declare-const fuel%vstd!view.impl&%6.view. FuelId)
(declare-const fuel%vstd!view.impl&%10.view. FuelId)
(declare-const fuel%vstd!view.impl&%12.view. FuelId)
(declare-const fuel%vstd!view.impl&%20.view. FuelId)
(declare-const fuel%vstd!view.impl&%24.view. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!ptr.group_ptr_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_axioms. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(assert
 (distinct fuel%vstd!std_specs.option.impl&%0.is_Some. fuel%vstd!std_specs.option.impl&%0.get_Some_0.
  fuel%vstd!std_specs.option.spec_unwrap. fuel%vstd!std_specs.vec.impl&%0.spec_index.
  fuel%vstd!std_specs.vec.axiom_spec_len. fuel%vstd!raw_ptr.impl&%4.view. fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.
  fuel%vstd!raw_ptr.ptrs_mut_eq. fuel%vstd!seq.impl&%0.spec_index. fuel%vstd!seq.axiom_seq_index_decreases.
  fuel%vstd!seq.axiom_seq_empty. fuel%vstd!seq.axiom_seq_new_len. fuel%vstd!seq.axiom_seq_new_index.
  fuel%vstd!seq.axiom_seq_push_len. fuel%vstd!seq.axiom_seq_push_index_same. fuel%vstd!seq.axiom_seq_push_index_different.
  fuel%vstd!seq.axiom_seq_update_len. fuel%vstd!seq.axiom_seq_update_same. fuel%vstd!seq.axiom_seq_update_different.
  fuel%vstd!seq.axiom_seq_ext_equal. fuel%vstd!seq.axiom_seq_ext_equal_deep. fuel%vstd!seq.axiom_seq_subrange_len.
  fuel%vstd!seq.axiom_seq_subrange_index. fuel%vstd!seq.axiom_seq_add_len. fuel%vstd!seq.axiom_seq_add_index1.
  fuel%vstd!seq.axiom_seq_add_index2. fuel%vstd!slice.axiom_spec_len. fuel%vstd!view.impl&%0.view.
  fuel%vstd!view.impl&%2.view. fuel%vstd!view.impl&%4.view. fuel%vstd!view.impl&%6.view.
  fuel%vstd!view.impl&%10.view. fuel%vstd!view.impl&%12.view. fuel%vstd!view.impl&%20.view.
  fuel%vstd!view.impl&%24.view. fuel%vstd!array.group_array_axioms. fuel%vstd!map.group_map_axioms.
  fuel%vstd!multiset.group_multiset_axioms. fuel%vstd!ptr.group_ptr_axioms. fuel%vstd!raw_ptr.group_raw_ptr_axioms.
  fuel%vstd!seq.group_seq_axioms. fuel%vstd!seq_lib.group_seq_lib_default. fuel%vstd!set.group_set_axioms.
  fuel%vstd!set_lib.group_set_lib_axioms. fuel%vstd!slice.group_slice_axioms. fuel%vstd!string.group_string_axioms.
  fuel%vstd!std_specs.bits.group_bits_axioms. fuel%vstd!std_specs.control_flow.group_control_flow_axioms.
  fuel%vstd!std_specs.range.group_range_axioms. fuel%vstd!std_specs.vec.group_vec_axioms.
  fuel%vstd!group_vstd_default.
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
  (and
   (fuel_bool_default fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.)
   (fuel_bool_default fuel%vstd!raw_ptr.ptrs_mut_eq.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
  (and
   (fuel_bool_default fuel%vstd!seq.axiom_seq_index_decreases.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_empty.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_new_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_new_index.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_index_same.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_index_different.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_update_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_update_same.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_update_different.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal_deep.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_subrange_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_subrange_index.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_index1.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_index2.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
  (fuel_bool_default fuel%vstd!slice.axiom_spec_len.)
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
  (fuel_bool_default fuel%vstd!std_specs.vec.axiom_spec_len.)
))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!ptr.group_ptr_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
)))

;; Associated-Type-Decls
(declare-fun proj%%vstd!view.View./V (Dcr Type) Dcr)
(declare-fun proj%vstd!view.View./V (Dcr Type) Type)

;; Datatypes
(declare-sort alloc!vec.Vec<u64./allocator_global%.>. 0)
(declare-sort vstd!raw_ptr.DynMetadata. 0)
(declare-sort vstd!raw_ptr.Provenance. 0)
(declare-sort vstd!seq.Seq<u64.>. 0)
(declare-sort allocator_global%. 0)
(declare-datatypes ((core!option.Option. 0) (vstd!raw_ptr.Metadata. 0) (vstd!raw_ptr.PtrData.
   0
  ) (tuple%0. 0)
 ) (((core!option.Option./None) (core!option.Option./Some (core!option.Option./Some/?0
     Poly
   ))
  ) ((vstd!raw_ptr.Metadata./Thin) (vstd!raw_ptr.Metadata./Length (vstd!raw_ptr.Metadata./Length/?0
     Int
    )
   ) (vstd!raw_ptr.Metadata./Dyn (vstd!raw_ptr.Metadata./Dyn/?0 vstd!raw_ptr.DynMetadata.))
  ) ((vstd!raw_ptr.PtrData./PtrData (vstd!raw_ptr.PtrData./PtrData/?addr Int) (vstd!raw_ptr.PtrData./PtrData/?provenance
     vstd!raw_ptr.Provenance.
    ) (vstd!raw_ptr.PtrData./PtrData/?metadata vstd!raw_ptr.Metadata.)
   )
  ) ((tuple%0./tuple%0))
))
(declare-fun core!option.Option./Some/0 (core!option.Option.) Poly)
(declare-fun vstd!raw_ptr.Metadata./Length/0 (vstd!raw_ptr.Metadata.) Int)
(declare-fun vstd!raw_ptr.Metadata./Dyn/0 (vstd!raw_ptr.Metadata.) vstd!raw_ptr.DynMetadata.)
(declare-fun vstd!raw_ptr.PtrData./PtrData/addr (vstd!raw_ptr.PtrData.) Int)
(declare-fun vstd!raw_ptr.PtrData./PtrData/provenance (vstd!raw_ptr.PtrData.) vstd!raw_ptr.Provenance.)
(declare-fun vstd!raw_ptr.PtrData./PtrData/metadata (vstd!raw_ptr.PtrData.) vstd!raw_ptr.Metadata.)
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%core!option.Option. (Dcr Type) Type)
(declare-fun TYPE%alloc!vec.Vec. (Dcr Type Dcr Type) Type)
(declare-const TYPE%vstd!raw_ptr.Provenance. Type)
(declare-const TYPE%vstd!raw_ptr.DynMetadata. Type)
(declare-const TYPE%vstd!raw_ptr.Metadata. Type)
(declare-const TYPE%vstd!raw_ptr.PtrData. Type)
(declare-fun TYPE%vstd!seq.Seq. (Dcr Type) Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%alloc!vec.Vec<u64./allocator_global%.>. (alloc!vec.Vec<u64./allocator_global%.>.)
 Poly
)
(declare-fun %Poly%alloc!vec.Vec<u64./allocator_global%.>. (Poly) alloc!vec.Vec<u64./allocator_global%.>.)
(declare-fun Poly%vstd!raw_ptr.DynMetadata. (vstd!raw_ptr.DynMetadata.) Poly)
(declare-fun %Poly%vstd!raw_ptr.DynMetadata. (Poly) vstd!raw_ptr.DynMetadata.)
(declare-fun Poly%vstd!raw_ptr.Provenance. (vstd!raw_ptr.Provenance.) Poly)
(declare-fun %Poly%vstd!raw_ptr.Provenance. (Poly) vstd!raw_ptr.Provenance.)
(declare-fun Poly%vstd!seq.Seq<u64.>. (vstd!seq.Seq<u64.>.) Poly)
(declare-fun %Poly%vstd!seq.Seq<u64.>. (Poly) vstd!seq.Seq<u64.>.)
(declare-fun Poly%allocator_global%. (allocator_global%.) Poly)
(declare-fun %Poly%allocator_global%. (Poly) allocator_global%.)
(declare-fun Poly%core!option.Option. (core!option.Option.) Poly)
(declare-fun %Poly%core!option.Option. (Poly) core!option.Option.)
(declare-fun Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.Metadata.) Poly)
(declare-fun %Poly%vstd!raw_ptr.Metadata. (Poly) vstd!raw_ptr.Metadata.)
(declare-fun Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData.) Poly)
(declare-fun %Poly%vstd!raw_ptr.PtrData. (Poly) vstd!raw_ptr.PtrData.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%1. (Poly%fun%1. x)))
   :pattern ((Poly%fun%1. x))
   :qid internal_crate__fun__1_box_axiom_definition
   :skolemid skolem_internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%fun%1. (%Poly%fun%1. x)))
   )
   :pattern ((has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_unbox_axiom_definition
   :skolemid skolem_internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x %%Function%%)) (!
   (=>
    (forall ((T%0 Poly)) (!
      (=>
       (has_type T%0 T%0&)
       (has_type (%%apply%%0 x T%0) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x T%0) T%1&))
      :qid internal_crate__fun__1_constructor_inner_definition
      :skolemid skolem_internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_constructor_definition
   :skolemid skolem_internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (has_type (%%apply%%0 x T%0) T%1&)
   )
   :pattern ((%%apply%%0 x T%0) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&.
      T%1&
   )))
   :qid internal_crate__fun__1_apply_definition
   :skolemid skolem_internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (height_lt (height (%%apply%%0 x T%0)) (height (fun_from_recursive_field (Poly%fun%1.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%0 x T%0)) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_crate__fun__1_height_apply_definition
   :skolemid skolem_internal_crate__fun__1_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (forall ((T%0 Poly)) (!
       (=>
        (has_type T%0 T%0&)
        (ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1. y) T%0))
       )
       :pattern ((ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1.
           y
          ) T%0
       )))
       :qid internal_crate__fun__1_inner_ext_equal_definition
       :skolemid skolem_internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_crate__fun__1_ext_equal_definition
   :skolemid skolem_internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x alloc!vec.Vec<u64./allocator_global%.>.)) (!
   (= x (%Poly%alloc!vec.Vec<u64./allocator_global%.>. (Poly%alloc!vec.Vec<u64./allocator_global%.>.
      x
   )))
   :pattern ((Poly%alloc!vec.Vec<u64./allocator_global%.>. x))
   :qid internal_alloc__vec__Vec<u64./allocator_global__.>_box_axiom_definition
   :skolemid skolem_internal_alloc__vec__Vec<u64./allocator_global__.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%alloc!vec.Vec. $ (UINT 64) $ ALLOCATOR_GLOBAL))
    (= x (Poly%alloc!vec.Vec<u64./allocator_global%.>. (%Poly%alloc!vec.Vec<u64./allocator_global%.>.
       x
   ))))
   :pattern ((has_type x (TYPE%alloc!vec.Vec. $ (UINT 64) $ ALLOCATOR_GLOBAL)))
   :qid internal_alloc__vec__Vec<u64./allocator_global__.>_unbox_axiom_definition
   :skolemid skolem_internal_alloc__vec__Vec<u64./allocator_global__.>_unbox_axiom_definition
)))
(assert
 (forall ((x alloc!vec.Vec<u64./allocator_global%.>.)) (!
   (has_type (Poly%alloc!vec.Vec<u64./allocator_global%.>. x) (TYPE%alloc!vec.Vec. $ (
      UINT 64
     ) $ ALLOCATOR_GLOBAL
   ))
   :pattern ((has_type (Poly%alloc!vec.Vec<u64./allocator_global%.>. x) (TYPE%alloc!vec.Vec.
      $ (UINT 64) $ ALLOCATOR_GLOBAL
   )))
   :qid internal_alloc__vec__Vec<u64./allocator_global__.>_has_type_always_definition
   :skolemid skolem_internal_alloc__vec__Vec<u64./allocator_global__.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.DynMetadata.)) (!
   (= x (%Poly%vstd!raw_ptr.DynMetadata. (Poly%vstd!raw_ptr.DynMetadata. x)))
   :pattern ((Poly%vstd!raw_ptr.DynMetadata. x))
   :qid internal_vstd__raw_ptr__DynMetadata_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__DynMetadata_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.DynMetadata.)
    (= x (Poly%vstd!raw_ptr.DynMetadata. (%Poly%vstd!raw_ptr.DynMetadata. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.DynMetadata.))
   :qid internal_vstd__raw_ptr__DynMetadata_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__DynMetadata_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.DynMetadata.)) (!
   (has_type (Poly%vstd!raw_ptr.DynMetadata. x) TYPE%vstd!raw_ptr.DynMetadata.)
   :pattern ((has_type (Poly%vstd!raw_ptr.DynMetadata. x) TYPE%vstd!raw_ptr.DynMetadata.))
   :qid internal_vstd__raw_ptr__DynMetadata_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__DynMetadata_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Provenance.)) (!
   (= x (%Poly%vstd!raw_ptr.Provenance. (Poly%vstd!raw_ptr.Provenance. x)))
   :pattern ((Poly%vstd!raw_ptr.Provenance. x))
   :qid internal_vstd__raw_ptr__Provenance_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.Provenance.)
    (= x (Poly%vstd!raw_ptr.Provenance. (%Poly%vstd!raw_ptr.Provenance. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.Provenance.))
   :qid internal_vstd__raw_ptr__Provenance_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Provenance.)) (!
   (has_type (Poly%vstd!raw_ptr.Provenance. x) TYPE%vstd!raw_ptr.Provenance.)
   :pattern ((has_type (Poly%vstd!raw_ptr.Provenance. x) TYPE%vstd!raw_ptr.Provenance.))
   :qid internal_vstd__raw_ptr__Provenance_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_has_type_always_definition
)))
(assert
 (forall ((x vstd!seq.Seq<u64.>.)) (!
   (= x (%Poly%vstd!seq.Seq<u64.>. (Poly%vstd!seq.Seq<u64.>. x)))
   :pattern ((Poly%vstd!seq.Seq<u64.>. x))
   :qid internal_vstd__seq__Seq<u64.>_box_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<u64.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!seq.Seq. $ (UINT 64)))
    (= x (Poly%vstd!seq.Seq<u64.>. (%Poly%vstd!seq.Seq<u64.>. x)))
   )
   :pattern ((has_type x (TYPE%vstd!seq.Seq. $ (UINT 64))))
   :qid internal_vstd__seq__Seq<u64.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<u64.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!seq.Seq<u64.>.)) (!
   (has_type (Poly%vstd!seq.Seq<u64.>. x) (TYPE%vstd!seq.Seq. $ (UINT 64)))
   :pattern ((has_type (Poly%vstd!seq.Seq<u64.>. x) (TYPE%vstd!seq.Seq. $ (UINT 64))))
   :qid internal_vstd__seq__Seq<u64.>_has_type_always_definition
   :skolemid skolem_internal_vstd__seq__Seq<u64.>_has_type_always_definition
)))
(assert
 (forall ((x allocator_global%.)) (!
   (= x (%Poly%allocator_global%. (Poly%allocator_global%. x)))
   :pattern ((Poly%allocator_global%. x))
   :qid internal_crate__allocator_global___box_axiom_definition
   :skolemid skolem_internal_crate__allocator_global___box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ALLOCATOR_GLOBAL)
    (= x (Poly%allocator_global%. (%Poly%allocator_global%. x)))
   )
   :pattern ((has_type x ALLOCATOR_GLOBAL))
   :qid internal_crate__allocator_global___unbox_axiom_definition
   :skolemid skolem_internal_crate__allocator_global___unbox_axiom_definition
)))
(assert
 (forall ((x allocator_global%.)) (!
   (has_type (Poly%allocator_global%. x) ALLOCATOR_GLOBAL)
   :pattern ((has_type (Poly%allocator_global%. x) ALLOCATOR_GLOBAL))
   :qid internal_crate__allocator_global___has_type_always_definition
   :skolemid skolem_internal_crate__allocator_global___has_type_always_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= x (%Poly%core!option.Option. (Poly%core!option.Option. x)))
   :pattern ((Poly%core!option.Option. x))
   :qid internal_core__option__Option_box_axiom_definition
   :skolemid skolem_internal_core__option__Option_box_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (= x (Poly%core!option.Option. (%Poly%core!option.Option. x)))
   )
   :pattern ((has_type x (TYPE%core!option.Option. V&. V&)))
   :qid internal_core__option__Option_unbox_axiom_definition
   :skolemid skolem_internal_core__option__Option_unbox_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
     V&. V&
   ))
   :pattern ((has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./None_constructor_definition
   :skolemid skolem_internal_core!option.Option./None_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (_0! Poly)) (!
   (=>
    (has_type _0! V&)
    (has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :pattern ((has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some_constructor_definition
   :skolemid skolem_internal_core!option.Option./Some_constructor_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= (core!option.Option./Some/0 x) (core!option.Option./Some/?0 x))
   :pattern ((core!option.Option./Some/0 x))
   :qid internal_core!option.Option./Some/0_accessor_definition
   :skolemid skolem_internal_core!option.Option./Some/0_accessor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (has_type (core!option.Option./Some/0 (%Poly%core!option.Option. x)) V&)
   )
   :pattern ((core!option.Option./Some/0 (%Poly%core!option.Option. x)) (has_type x (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some/0_invariant_definition
   :skolemid skolem_internal_core!option.Option./Some/0_invariant_definition
)))
(assert
 (forall ((x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (height_lt (height (core!option.Option./Some/0 x)) (height (Poly%core!option.Option.
       x
   ))))
   :pattern ((height (core!option.Option./Some/0 x)))
   :qid prelude_datatype_height_core!option.Option./Some/0
   :skolemid skolem_prelude_datatype_height_core!option.Option./Some/0
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./None (%Poly%core!option.Option. x))
     (is-core!option.Option./None (%Poly%core!option.Option. y))
    )
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./None_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./None_ext_equal_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./Some (%Poly%core!option.Option. x))
     (is-core!option.Option./Some (%Poly%core!option.Option. y))
     (ext_eq deep V& (core!option.Option./Some/0 (%Poly%core!option.Option. x)) (core!option.Option./Some/0
       (%Poly%core!option.Option. y)
    )))
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./Some_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./Some_ext_equal_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Metadata.)) (!
   (= x (%Poly%vstd!raw_ptr.Metadata. (Poly%vstd!raw_ptr.Metadata. x)))
   :pattern ((Poly%vstd!raw_ptr.Metadata. x))
   :qid internal_vstd__raw_ptr__Metadata_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Metadata_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.Metadata.)
    (= x (Poly%vstd!raw_ptr.Metadata. (%Poly%vstd!raw_ptr.Metadata. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.Metadata.))
   :qid internal_vstd__raw_ptr__Metadata_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Metadata_unbox_axiom_definition
)))
(assert
 (has_type (Poly%vstd!raw_ptr.Metadata. vstd!raw_ptr.Metadata./Thin) TYPE%vstd!raw_ptr.Metadata.)
)
(assert
 (forall ((_0! Int)) (!
   (=>
    (uInv SZ _0!)
    (has_type (Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.Metadata./Length _0!)) TYPE%vstd!raw_ptr.Metadata.)
   )
   :pattern ((has_type (Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.Metadata./Length _0!))
     TYPE%vstd!raw_ptr.Metadata.
   ))
   :qid internal_vstd!raw_ptr.Metadata./Length_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.Metadata./Length_constructor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Metadata.)) (!
   (= (vstd!raw_ptr.Metadata./Length/0 x) (vstd!raw_ptr.Metadata./Length/?0 x))
   :pattern ((vstd!raw_ptr.Metadata./Length/0 x))
   :qid internal_vstd!raw_ptr.Metadata./Length/0_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.Metadata./Length/0_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.Metadata.)
    (uInv SZ (vstd!raw_ptr.Metadata./Length/0 (%Poly%vstd!raw_ptr.Metadata. x)))
   )
   :pattern ((vstd!raw_ptr.Metadata./Length/0 (%Poly%vstd!raw_ptr.Metadata. x)) (has_type
     x TYPE%vstd!raw_ptr.Metadata.
   ))
   :qid internal_vstd!raw_ptr.Metadata./Length/0_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.Metadata./Length/0_invariant_definition
)))
(assert
 (forall ((_0! vstd!raw_ptr.DynMetadata.)) (!
   (has_type (Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.Metadata./Dyn _0!)) TYPE%vstd!raw_ptr.Metadata.)
   :pattern ((has_type (Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.Metadata./Dyn _0!))
     TYPE%vstd!raw_ptr.Metadata.
   ))
   :qid internal_vstd!raw_ptr.Metadata./Dyn_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.Metadata./Dyn_constructor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Metadata.)) (!
   (= (vstd!raw_ptr.Metadata./Dyn/0 x) (vstd!raw_ptr.Metadata./Dyn/?0 x))
   :pattern ((vstd!raw_ptr.Metadata./Dyn/0 x))
   :qid internal_vstd!raw_ptr.Metadata./Dyn/0_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.Metadata./Dyn/0_accessor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= x (%Poly%vstd!raw_ptr.PtrData. (Poly%vstd!raw_ptr.PtrData. x)))
   :pattern ((Poly%vstd!raw_ptr.PtrData. x))
   :qid internal_vstd__raw_ptr__PtrData_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PtrData_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.PtrData.)
    (= x (Poly%vstd!raw_ptr.PtrData. (%Poly%vstd!raw_ptr.PtrData. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.PtrData.))
   :qid internal_vstd__raw_ptr__PtrData_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PtrData_unbox_axiom_definition
)))
(assert
 (forall ((_addr! Int) (_provenance! vstd!raw_ptr.Provenance.) (_metadata! vstd!raw_ptr.Metadata.))
  (!
   (=>
    (and
     (uInv SZ _addr!)
     (has_type (Poly%vstd!raw_ptr.Metadata. _metadata!) TYPE%vstd!raw_ptr.Metadata.)
    )
    (has_type (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData _addr! _provenance!
       _metadata!
      )
     ) TYPE%vstd!raw_ptr.PtrData.
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData _addr!
       _provenance! _metadata!
      )
     ) TYPE%vstd!raw_ptr.PtrData.
   ))
   :qid internal_vstd!raw_ptr.PtrData./PtrData_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData_constructor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/addr x) (vstd!raw_ptr.PtrData./PtrData/?addr x))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/addr x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/addr_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/addr_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.PtrData.)
    (uInv SZ (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. x)))
   )
   :pattern ((vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. x)) (has_type
     x TYPE%vstd!raw_ptr.PtrData.
   ))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/addr_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/addr_invariant_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/provenance x) (vstd!raw_ptr.PtrData./PtrData/?provenance
     x
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/provenance x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/provenance_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/provenance_accessor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/metadata x) (vstd!raw_ptr.PtrData./PtrData/?metadata
     x
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/metadata x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/metadata_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/metadata_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.PtrData.)
    (has_type (Poly%vstd!raw_ptr.Metadata. (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData.
        x
      ))
     ) TYPE%vstd!raw_ptr.Metadata.
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. x))
    (has_type x TYPE%vstd!raw_ptr.PtrData.)
   )
   :qid internal_vstd!raw_ptr.PtrData./PtrData/metadata_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/metadata_invariant_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Traits
(declare-fun tr_bound%vstd!view.View. (Dcr Type) Bool)
(declare-fun tr_bound%core!alloc.Allocator. (Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.option.OptionAdditionalFns. (Dcr Type Dcr Type)
 Bool
)
(declare-fun tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. (Dcr Type Dcr Type)
 Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   true
   :pattern ((tr_bound%vstd!view.View. Self%&. Self%&))
   :qid internal_vstd__view__View_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__view__View_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   true
   :pattern ((tr_bound%core!alloc.Allocator. Self%&. Self%&))
   :qid internal_core__alloc__Allocator_trait_type_bounds_definition
   :skolemid skolem_internal_core__alloc__Allocator_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   true
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. Self%&. Self%& T&. T&)
    (and
     (tr_bound%vstd!view.View. Self%&. Self%&)
     (and
      (= $ (proj%%vstd!view.View./V Self%&. Self%&))
      (= (TYPE%vstd!seq.Seq. T&. T&) (proj%vstd!view.View./V Self%&. Self%&))
   )))
   :pattern ((tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__std_specs__vec__VecAdditionalSpecFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__vec__VecAdditionalSpecFns_trait_type_bounds_definition
)))

;; Associated-Type-Impls
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $ (PTR T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $ (PTR T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $ (PTR T&. T&)) TYPE%vstd!raw_ptr.PtrData.)
   :pattern ((proj%vstd!view.View./V $ (PTR T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)) TYPE%vstd!raw_ptr.PtrData.)
   :pattern ((proj%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $ (SLICE T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $ (SLICE T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $ (SLICE T&. T&)) (TYPE%vstd!seq.Seq. T&. T&))
   :pattern ((proj%vstd!view.View./V $ (SLICE T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (REF A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (REF A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (BOX $ ALLOCATOR_GLOBAL A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (BOX $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (BOX $ ALLOCATOR_GLOBAL A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (BOX $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (RC $ ALLOCATOR_GLOBAL A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (RC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (RC $ ALLOCATOR_GLOBAL A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (RC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (ARC $ ALLOCATOR_GLOBAL A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (ARC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (ARC $ ALLOCATOR_GLOBAL A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (ARC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)) $)
   :pattern ((proj%%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)) (TYPE%vstd!seq.Seq.
     T&. T&
   ))
   :pattern ((proj%vstd!view.View./V $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (= (proj%%vstd!view.View./V $ TYPE%tuple%0.) $)
)
(assert
 (= (proj%vstd!view.View./V $ TYPE%tuple%0.) TYPE%tuple%0.)
)
(assert
 (= (proj%%vstd!view.View./V $ BOOL) $)
)
(assert
 (= (proj%vstd!view.View./V $ BOOL) BOOL)
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 64)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 64)) (UINT 64))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT SZ)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT SZ)) (UINT SZ))
)

;; Function-Decl vstd::view::View::view
(declare-fun vstd!view.View.view.? (Dcr Type Poly) Poly)
(declare-fun vstd!view.View.view%default%.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq::Seq::len
(declare-fun vstd!seq.Seq.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? (Dcr Type Dcr Type
  Poly Poly
 ) Poly
)
(declare-fun vstd!std_specs.vec.VecAdditionalSpecFns.spec_index%default%.? (Dcr Type
  Dcr Type Poly Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::OptionAdditionalFns::is_Some
(declare-fun vstd!std_specs.option.OptionAdditionalFns.is_Some.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.option.OptionAdditionalFns.is_Some%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::OptionAdditionalFns::get_Some_0
(declare-fun vstd!std_specs.option.OptionAdditionalFns.get_Some_0.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.option.OptionAdditionalFns.get_Some_0%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::spec_unwrap
(declare-fun vstd!std_specs.option.spec_unwrap.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::std_specs::vec::spec_vec_len
(declare-fun vstd!std_specs.vec.spec_vec_len.? (Dcr Type Dcr Type Poly) Int)

;; Function-Decl vstd::seq::Seq::empty
(declare-fun vstd!seq.Seq.empty.? (Dcr Type) Poly)

;; Function-Decl vstd::seq::Seq::push
(declare-fun vstd!seq.Seq.push.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::index
(declare-fun vstd!seq.Seq.index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_index
(declare-fun vstd!seq.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::subrange
(declare-fun vstd!seq.Seq.subrange.? (Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::raw_ptr::ptr_mut_from_data
(declare-fun vstd!raw_ptr.ptr_mut_from_data.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::view_reverse_for_eq
(declare-fun vstd!raw_ptr.view_reverse_for_eq.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq::Seq::new
(declare-fun vstd!seq.Seq.new.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::update
(declare-fun vstd!seq.Seq.update.? (Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::add
(declare-fun vstd!seq.Seq.add.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::slice::spec_slice_len
(declare-fun vstd!slice.spec_slice_len.? (Dcr Type Poly) Int)

;; Function-Decl vectors::uninterp_fn
(declare-fun vectors!uninterp_fn.? (Poly) Bool)

;; Function-Axioms vstd::view::View::view
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!view.View.view.? Self%&. Self%& self!) (proj%vstd!view.View./V Self%&.
      Self%&
   )))
   :pattern ((vstd!view.View.view.? Self%&. Self%& self!))
   :qid internal_vstd!view.View.view.?_pre_post_definition
   :skolemid skolem_internal_vstd!view.View.view.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::Seq::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (<= 0 (vstd!seq.Seq.len.? A&. A& self!))
   )
   :pattern ((vstd!seq.Seq.len.? A&. A& self!))
   :qid internal_vstd!seq.Seq.len.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.len.?_pre_post_definition
)))

;; Function-Specs vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(declare-fun req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. (Dcr Type Dcr
  Type Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (= (req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. Self%&. Self%& T&. T& self!
     i!
    ) (=>
     %%global_location_label%%0
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? Self%&. Self%& self!)))
   )))
   :pattern ((req%vstd!std_specs.vec.VecAdditionalSpecFns.spec_index. Self%&. Self%& T&.
     T& self! i!
   ))
   :qid internal_req__vstd!std_specs.vec.VecAdditionalSpecFns.spec_index._definition
   :skolemid skolem_internal_req__vstd!std_specs.vec.VecAdditionalSpecFns.spec_index._definition
)))

;; Function-Axioms vstd::std_specs::vec::VecAdditionalSpecFns::spec_index
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (=>
    (and
     (has_type self! Self%&)
     (has_type i! INT)
    )
    (has_type (vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? Self%&. Self%& T&.
      T& self! i!
     ) T&
   ))
   :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? Self%&. Self%& T&.
     T& self! i!
   ))
   :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::option::OptionAdditionalFns::is_Some
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.option.OptionAdditionalFns.is_Some.? Self%&. Self%& T&. T&
      self!
     ) BOOL
   ))
   :pattern ((vstd!std_specs.option.OptionAdditionalFns.is_Some.? Self%&. Self%& T&. T&
     self!
   ))
   :qid internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::option::OptionAdditionalFns::get_Some_0
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.option.OptionAdditionalFns.get_Some_0.? Self%&. Self%& T&.
      T& self!
     ) T&
   ))
   :pattern ((vstd!std_specs.option.OptionAdditionalFns.get_Some_0.? Self%&. Self%& T&.
     T& self!
   ))
   :qid internal_vstd!std_specs.option.OptionAdditionalFns.get_Some_0.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.get_Some_0.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::option::impl&%0::is_Some
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%0.is_Some.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%0.is_Some.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!std_specs.option.OptionAdditionalFns.is_Some.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
     ) (B (is-core!option.Option./Some (%Poly%core!option.Option. self!)))
    )
    :pattern ((vstd!std_specs.option.OptionAdditionalFns.is_Some.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_definition
))))

;; Function-Axioms vstd::std_specs::option::impl&%0::get_Some_0
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%0.get_Some_0.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%0.get_Some_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!std_specs.option.OptionAdditionalFns.get_Some_0.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
     ) (core!option.Option./Some/0 (%Poly%core!option.Option. self!))
    )
    :pattern ((vstd!std_specs.option.OptionAdditionalFns.get_Some_0.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.option.OptionAdditionalFns.get_Some_0.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.get_Some_0.?_definition
))))

;; Function-Specs vstd::std_specs::option::spec_unwrap
(declare-fun req%vstd!std_specs.option.spec_unwrap. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (= (req%vstd!std_specs.option.spec_unwrap. T&. T& option!) (=>
     %%global_location_label%%1
     (%B (B (is-core!option.Option./Some (%Poly%core!option.Option. option!))))
   ))
   :pattern ((req%vstd!std_specs.option.spec_unwrap. T&. T& option!))
   :qid internal_req__vstd!std_specs.option.spec_unwrap._definition
   :skolemid skolem_internal_req__vstd!std_specs.option.spec_unwrap._definition
)))

;; Function-Axioms vstd::std_specs::option::spec_unwrap
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.spec_unwrap.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.spec_unwrap.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.spec_unwrap.? T&. T& option!) (core!option.Option./Some/0
      (%Poly%core!option.Option. option!)
    ))
    :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
    :qid internal_vstd!std_specs.option.spec_unwrap.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (=>
    (has_type option! (TYPE%core!option.Option. T&. T&))
    (has_type (vstd!std_specs.option.spec_unwrap.? T&. T& option!) T&)
   )
   :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
   :qid internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
)))

;; Function-Specs core::option::impl&%0::unwrap
(declare-fun req%core!option.impl&%0.unwrap. (Dcr Type core!option.Option.) Bool)
(declare-const %%global_location_label%%2 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (option! core!option.Option.)) (!
   (= (req%core!option.impl&%0.unwrap. T&. T& option!) (=>
     %%global_location_label%%2
     (%B (B (is-core!option.Option./Some (%Poly%core!option.Option. (Poly%core!option.Option.
          option!
   )))))))
   :pattern ((req%core!option.impl&%0.unwrap. T&. T& option!))
   :qid internal_req__core!option.impl&__0.unwrap._definition
   :skolemid skolem_internal_req__core!option.impl&__0.unwrap._definition
)))
(declare-fun ens%core!option.impl&%0.unwrap. (Dcr Type core!option.Option. Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (option! core!option.Option.) (t! Poly)) (!
   (= (ens%core!option.impl&%0.unwrap. T&. T& option! t!) (and
     (has_type t! T&)
     (= t! (core!option.Option./Some/0 (%Poly%core!option.Option. (Poly%core!option.Option.
         option!
   ))))))
   :pattern ((ens%core!option.impl&%0.unwrap. T&. T& option! t!))
   :qid internal_ens__core!option.impl&__0.unwrap._definition
   :skolemid skolem_internal_ens__core!option.impl&__0.unwrap._definition
)))

;; Function-Axioms vstd::std_specs::vec::spec_vec_len
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (v! Poly)) (!
   (=>
    (has_type v! (TYPE%alloc!vec.Vec. T&. T& A&. A&))
    (uInv SZ (vstd!std_specs.vec.spec_vec_len.? T&. T& A&. A& v!))
   )
   :pattern ((vstd!std_specs.vec.spec_vec_len.? T&. T& A&. A& v!))
   :qid internal_vstd!std_specs.vec.spec_vec_len.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.vec.spec_vec_len.?_pre_post_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!alloc.Allocator. $ ALLOCATOR_GLOBAL)
)

;; Function-Specs vstd::std_specs::vec::axiom_spec_len
(declare-fun ens%vstd!std_specs.vec.axiom_spec_len. (Dcr Type Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (v! Poly)) (!
   (= (ens%vstd!std_specs.vec.axiom_spec_len. A&. A& v!) (= (vstd!std_specs.vec.spec_vec_len.?
      A&. A& $ ALLOCATOR_GLOBAL v!
     ) (vstd!seq.Seq.len.? A&. A& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. A&. A& $
        ALLOCATOR_GLOBAL
       ) v!
   ))))
   :pattern ((ens%vstd!std_specs.vec.axiom_spec_len. A&. A& v!))
   :qid internal_ens__vstd!std_specs.vec.axiom_spec_len._definition
   :skolemid skolem_internal_ens__vstd!std_specs.vec.axiom_spec_len._definition
)))

;; Broadcast vstd::std_specs::vec::axiom_spec_len
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.vec.axiom_spec_len.)
  (forall ((A&. Dcr) (A& Type) (v! Poly)) (!
    (=>
     (has_type v! (TYPE%alloc!vec.Vec. A&. A& $ ALLOCATOR_GLOBAL))
     (= (vstd!std_specs.vec.spec_vec_len.? A&. A& $ ALLOCATOR_GLOBAL v!) (vstd!seq.Seq.len.?
       A&. A& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. A&. A& $ ALLOCATOR_GLOBAL) v!)
    )))
    :pattern ((vstd!std_specs.vec.spec_vec_len.? A&. A& $ ALLOCATOR_GLOBAL v!))
    :qid user_vstd__std_specs__vec__axiom_spec_len_0
    :skolemid skolem_user_vstd__std_specs__vec__axiom_spec_len_0
))))

;; Function-Axioms vstd::seq::Seq::empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!seq.Seq.empty.? A&. A&) (TYPE%vstd!seq.Seq. A&. A&))
   :pattern ((vstd!seq.Seq.empty.? A&. A&))
   :qid internal_vstd!seq.Seq.empty.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.empty.?_pre_post_definition
)))

;; Function-Specs alloc::vec::impl&%0::new
(declare-fun ens%alloc!vec.impl&%0.new. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (v! Poly)) (!
   (= (ens%alloc!vec.impl&%0.new. T&. T& v!) (and
     (has_type v! (TYPE%alloc!vec.Vec. T&. T& $ ALLOCATOR_GLOBAL))
     (= (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& $ ALLOCATOR_GLOBAL) v!) (vstd!seq.Seq.empty.?
       T&. T&
   ))))
   :pattern ((ens%alloc!vec.impl&%0.new. T&. T& v!))
   :qid internal_ens__alloc!vec.impl&__0.new._definition
   :skolemid skolem_internal_ens__alloc!vec.impl&__0.new._definition
)))

;; Function-Axioms vstd::seq::Seq::push
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!seq.Seq.push.? A&. A& self! a!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.push.? A&. A& self! a!))
   :qid internal_vstd!seq.Seq.push.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.push.?_pre_post_definition
)))

;; Function-Specs alloc::vec::impl&%1::push
(declare-fun ens%alloc!vec.impl&%1.push. (Dcr Type Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (pre%vec! Poly) (vec! Poly) (value!
    Poly
   )
  ) (!
   (= (ens%alloc!vec.impl&%1.push. T&. T& A&. A& pre%vec! vec! value!) (and
     (has_type vec! (TYPE%alloc!vec.Vec. T&. T& A&. A&))
     (= (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) vec!) (vstd!seq.Seq.push.?
       T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) pre%vec!) value!
   ))))
   :pattern ((ens%alloc!vec.impl&%1.push. T&. T& A&. A& pre%vec! vec! value!))
   :qid internal_ens__alloc!vec.impl&__1.push._definition
   :skolemid skolem_internal_ens__alloc!vec.impl&__1.push._definition
)))

;; Function-Specs vstd::seq::Seq::index
(declare-fun req%vstd!seq.Seq.index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.Seq.index. A&. A& self! i!) (=>
     %%global_location_label%%3
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.index. A&. A& self! i!))
   :qid internal_req__vstd!seq.Seq.index._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.index._definition
)))

;; Function-Axioms vstd::seq::Seq::index
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.Seq.index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.Seq.index.? A&. A& self! i!))
   :qid internal_vstd!seq.Seq.index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.index.?_pre_post_definition
)))

;; Function-Specs vstd::seq::impl&%0::spec_index
(declare-fun req%vstd!seq.impl&%0.spec_index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.impl&%0.spec_index. A&. A& self! i!) (=>
     %%global_location_label%%4
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.impl&%0.spec_index. A&. A& self! i!))
   :qid internal_req__vstd!seq.impl&__0.spec_index._definition
   :skolemid skolem_internal_req__vstd!seq.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::seq::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_index.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) (vstd!seq.Seq.index.? A&. A& self!
      i!
    ))
    :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
    :qid internal_vstd!seq.impl&__0.spec_index.?_definition
    :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
   :qid internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::subrange
(declare-fun req%vstd!seq.Seq.subrange. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (= (req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!) (=>
     %%global_location_label%%5
     (and
      (and
       (<= 0 (%I start_inclusive!))
       (<= (%I start_inclusive!) (%I end_exclusive!))
      )
      (<= (%I end_exclusive!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_req__vstd!seq.Seq.subrange._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.subrange._definition
)))

;; Function-Axioms vstd::seq::Seq::subrange
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type start_inclusive! INT)
     (has_type end_exclusive! INT)
    )
    (has_type (vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!) (
      TYPE%vstd!seq.Seq. A&. A&
   )))
   :pattern ((vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_vstd!seq.Seq.subrange.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.subrange.?_pre_post_definition
)))

;; Function-Specs alloc::vec::impl&%1::pop
(declare-fun ens%alloc!vec.impl&%1.pop. (Dcr Type Dcr Type Poly Poly core!option.Option.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (pre%vec! Poly) (vec! Poly) (value!
    core!option.Option.
   )
  ) (!
   (= (ens%alloc!vec.impl&%1.pop. T&. T& A&. A& pre%vec! vec! value!) (and
     (has_type (Poly%core!option.Option. value!) (TYPE%core!option.Option. T&. T&))
     (has_type vec! (TYPE%alloc!vec.Vec. T&. T& A&. A&))
     (=>
      (> (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&.
          A&
         ) pre%vec!
        )
       ) 0
      )
      (and
       (= value! (core!option.Option./Some (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.?
           $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) pre%vec!
          ) (I (Sub (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&.
               T& A&. A&
              ) pre%vec!
             )
            ) 1
       )))))
       (= (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) vec!) (vstd!seq.Seq.subrange.?
         T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) pre%vec!) (I 0)
         (I (Sub (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T&
              A&. A&
             ) pre%vec!
            )
           ) 1
     ))))))
     (=>
      (= (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&.
          A&
         ) pre%vec!
        )
       ) 0
      )
      (and
       (= value! core!option.Option./None)
       (= (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) vec!) (vstd!view.View.view.?
         $ (TYPE%alloc!vec.Vec. T&. T& A&. A&) pre%vec!
   ))))))
   :pattern ((ens%alloc!vec.impl&%1.pop. T&. T& A&. A& pre%vec! vec! value!))
   :qid internal_ens__alloc!vec.impl&__1.pop._definition
   :skolemid skolem_internal_ens__alloc!vec.impl&__1.pop._definition
)))

;; Function-Axioms vstd::raw_ptr::ptr_mut_from_data
(assert
 (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
   (=>
    (has_type data! TYPE%vstd!raw_ptr.PtrData.)
    (has_type (vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!) (PTR T&. T&))
   )
   :pattern ((vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
   :qid internal_vstd!raw_ptr.ptr_mut_from_data.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.ptr_mut_from_data.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::axiom_ptr_mut_from_data
(declare-fun ens%vstd!raw_ptr.axiom_ptr_mut_from_data. (Dcr Type vstd!raw_ptr.PtrData.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (data! vstd!raw_ptr.PtrData.)) (!
   (= (ens%vstd!raw_ptr.axiom_ptr_mut_from_data. T&. T& data!) (= (%Poly%vstd!raw_ptr.PtrData.
      (vstd!view.View.view.? $ (PTR T&. T&) (vstd!raw_ptr.ptr_mut_from_data.? T&. T& (Poly%vstd!raw_ptr.PtrData.
         data!
      )))
     ) data!
   ))
   :pattern ((ens%vstd!raw_ptr.axiom_ptr_mut_from_data. T&. T& data!))
   :qid internal_ens__vstd!raw_ptr.axiom_ptr_mut_from_data._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.axiom_ptr_mut_from_data._definition
)))

;; Broadcast vstd::raw_ptr::axiom_ptr_mut_from_data
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.)
  (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
    (=>
     (has_type data! TYPE%vstd!raw_ptr.PtrData.)
     (= (vstd!view.View.view.? $ (PTR T&. T&) (vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
      data!
    ))
    :pattern ((vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
    :qid user_vstd__raw_ptr__axiom_ptr_mut_from_data_1
    :skolemid skolem_user_vstd__raw_ptr__axiom_ptr_mut_from_data_1
))))

;; Function-Axioms vstd::raw_ptr::view_reverse_for_eq
(assert
 (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
   (=>
    (has_type data! TYPE%vstd!raw_ptr.PtrData.)
    (has_type (vstd!raw_ptr.view_reverse_for_eq.? T&. T& data!) (PTR T&. T&))
   )
   :pattern ((vstd!raw_ptr.view_reverse_for_eq.? T&. T& data!))
   :qid internal_vstd!raw_ptr.view_reverse_for_eq.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.view_reverse_for_eq.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::ptrs_mut_eq
(declare-fun ens%vstd!raw_ptr.ptrs_mut_eq. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (a! Poly)) (!
   (= (ens%vstd!raw_ptr.ptrs_mut_eq. T&. T& a!) (= (vstd!raw_ptr.view_reverse_for_eq.?
      T&. T& (vstd!view.View.view.? $ (PTR T&. T&) a!)
     ) a!
   ))
   :pattern ((ens%vstd!raw_ptr.ptrs_mut_eq. T&. T& a!))
   :qid internal_ens__vstd!raw_ptr.ptrs_mut_eq._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.ptrs_mut_eq._definition
)))

;; Broadcast vstd::raw_ptr::ptrs_mut_eq
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.ptrs_mut_eq.)
  (forall ((T&. Dcr) (T& Type) (a! Poly)) (!
    (=>
     (has_type a! (PTR T&. T&))
     (= (vstd!raw_ptr.view_reverse_for_eq.? T&. T& (vstd!view.View.view.? $ (PTR T&. T&)
        a!
       )
      ) a!
    ))
    :pattern ((vstd!view.View.view.? $ (PTR T&. T&) a!))
    :qid user_vstd__raw_ptr__ptrs_mut_eq_2
    :skolemid skolem_user_vstd__raw_ptr__ptrs_mut_eq_2
))))

;; Function-Axioms vstd::seq::Seq::new
(assert
 (forall ((A&. Dcr) (A& Type) (impl%1&. Dcr) (impl%1& Type) (len! Poly) (f! Poly))
  (!
   (=>
    (and
     (has_type len! NAT)
     (has_type f! impl%1&)
    )
    (has_type (vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!) (TYPE%vstd!seq.Seq.
      A&. A&
   )))
   :pattern ((vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!))
   :qid internal_vstd!seq.Seq.new.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.new.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::update
(declare-fun req%vstd!seq.Seq.update. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly) (a! Poly)) (!
   (= (req%vstd!seq.Seq.update. A&. A& self! i! a!) (=>
     %%global_location_label%%6
     (and
      (<= 0 (%I i!))
      (< (%I i!) (vstd!seq.Seq.len.? A&. A& self!))
   )))
   :pattern ((req%vstd!seq.Seq.update. A&. A& self! i! a!))
   :qid internal_req__vstd!seq.Seq.update._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.update._definition
)))

;; Function-Axioms vstd::seq::Seq::update
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
     (has_type a! A&)
    )
    (has_type (vstd!seq.Seq.update.? A&. A& self! i! a!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.update.? A&. A& self! i! a!))
   :qid internal_vstd!seq.Seq.update.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.update.?_pre_post_definition
)))

;; Function-Axioms vstd::seq::Seq::add
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type rhs! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (has_type (vstd!seq.Seq.add.? A&. A& self! rhs!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.add.? A&. A& self! rhs!))
   :qid internal_vstd!seq.Seq.add.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.add.?_pre_post_definition
)))

;; Function-Specs vstd::seq::axiom_seq_index_decreases
(declare-fun req%vstd!seq.axiom_seq_index_decreases. (Dcr Type Poly Int) Bool)
(declare-const %%global_location_label%%7 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!) (=>
     %%global_location_label%%7
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!))
   :qid internal_req__vstd!seq.axiom_seq_index_decreases._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_index_decreases._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_index_decreases. (Dcr Type Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!) (height_lt (height (vstd!seq.Seq.index.?
       A&. A& s! (I i!)
      )
     ) (height s!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_index_decreases. A&. A& s! i!))
   :qid internal_ens__vstd!seq.axiom_seq_index_decreases._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_index_decreases._definition
)))

;; Broadcast vstd::seq::axiom_seq_index_decreases
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_index_decreases.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (height_lt (height (vstd!seq.Seq.index.? A&. A& s! i!)) (height s!))
    ))
    :pattern ((height (vstd!seq.Seq.index.? A&. A& s! i!)))
    :qid user_vstd__seq__axiom_seq_index_decreases_3
    :skolemid skolem_user_vstd__seq__axiom_seq_index_decreases_3
))))

;; Function-Specs vstd::seq::axiom_seq_empty
(declare-fun ens%vstd!seq.axiom_seq_empty. (Dcr Type) Bool)
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (ens%vstd!seq.axiom_seq_empty. A&. A&) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.?
       A&. A&
      )
     ) 0
   ))
   :pattern ((ens%vstd!seq.axiom_seq_empty. A&. A&))
   :qid internal_ens__vstd!seq.axiom_seq_empty._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_empty._definition
)))

;; Broadcast vstd::seq::axiom_seq_empty
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_empty.)
  (forall ((A&. Dcr) (A& Type)) (!
    (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)) 0)
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)))
    :qid user_vstd__seq__axiom_seq_empty_4
    :skolemid skolem_user_vstd__seq__axiom_seq_empty_4
))))

;; Function-Specs vstd::seq::axiom_seq_new_len
(declare-fun ens%vstd!seq.axiom_seq_new_len. (Dcr Type Int %%Function%%) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%)) (!
   (= (ens%vstd!seq.axiom_seq_new_len. A&. A& len! f!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.?
       A&. A& $ (TYPE%fun%1. $ INT A&. A&) (I len!) (Poly%fun%1. f!)
      )
     ) len!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_new_len. A&. A& len! f!))
   :qid internal_ens__vstd!seq.axiom_seq_new_len._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_new_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_new_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_new_len.)
  (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly)) (!
    (=>
     (and
      (has_type len! NAT)
      (has_type f! (TYPE%fun%1. $ INT A&. A&))
     )
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
        len! f!
       )
      ) (%I len!)
    ))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
        A&. A&
       ) len! f!
    )))
    :qid user_vstd__seq__axiom_seq_new_len_5
    :skolemid skolem_user_vstd__seq__axiom_seq_new_len_5
))))

;; Function-Specs vstd::seq::axiom_seq_new_index
(declare-fun req%vstd!seq.axiom_seq_new_index. (Dcr Type Int %%Function%% Int) Bool)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!) (=>
     %%global_location_label%%8
     (and
      (<= 0 i!)
      (< i! len!)
   )))
   :pattern ((req%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!))
   :qid internal_req__vstd!seq.axiom_seq_new_index._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_new_index._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_new_index. (Dcr Type Int %%Function%% Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (len! Int) (f! %%Function%%) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&) (I len!) (Poly%fun%1. f!))
      (I i!)
     ) (%%apply%%0 f! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_new_index. A&. A& len! f! i!))
   :qid internal_ens__vstd!seq.axiom_seq_new_index._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_new_index._definition
)))

;; Broadcast vstd::seq::axiom_seq_new_index
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_new_index.)
  (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type len! NAT)
      (has_type f! (TYPE%fun%1. $ INT A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (%I len!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
         len! f!
        ) i!
       ) (%%apply%%0 (%Poly%fun%1. f!) i!)
    )))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
        A&. A&
       ) len! f!
      ) i!
    ))
    :qid user_vstd__seq__axiom_seq_new_index_6
    :skolemid skolem_user_vstd__seq__axiom_seq_new_index_6
))))

;; Function-Specs vstd::seq::axiom_seq_push_len
(declare-fun ens%vstd!seq.axiom_seq_push_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_push_len. A&. A& s! a!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.?
       A&. A& s! a!
      )
     ) (nClip (Add (vstd!seq.Seq.len.? A&. A& s!) 1))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_len. A&. A& s! a!))
   :qid internal_ens__vstd!seq.axiom_seq_push_len._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_push_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
     )
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)) (nClip (Add (vstd!seq.Seq.len.?
         A&. A& s!
        ) 1
    ))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)))
    :qid user_vstd__seq__axiom_seq_push_len_7
    :skolemid skolem_user_vstd__seq__axiom_seq_push_len_7
))))

;; Function-Specs vstd::seq::axiom_seq_push_index_same
(declare-fun req%vstd!seq.axiom_seq_push_index_same. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!) (=>
     %%global_location_label%%9
     (= i! (vstd!seq.Seq.len.? A&. A& s!))
   ))
   :pattern ((req%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!))
   :qid internal_req__vstd!seq.axiom_seq_push_index_same._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_push_index_same._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_push_index_same. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) (I i!)
     ) a!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_index_same. A&. A& s! a! i!))
   :qid internal_ens__vstd!seq.axiom_seq_push_index_same._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_push_index_same._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_index_same
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_index_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
      (has_type i! INT)
     )
     (=>
      (= (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) a!)
    ))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
    :qid user_vstd__seq__axiom_seq_push_index_same_8
    :skolemid skolem_user_vstd__seq__axiom_seq_push_index_same_8
))))

;; Function-Specs vstd::seq::axiom_seq_push_index_different
(declare-fun req%vstd!seq.axiom_seq_push_index_different. (Dcr Type Poly Poly Int)
 Bool
)
(declare-const %%global_location_label%%10 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!) (=>
     %%global_location_label%%10
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!))
   :qid internal_req__vstd!seq.axiom_seq_push_index_different._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_push_index_different._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_push_index_different. (Dcr Type Poly Poly Int)
 Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_push_index_different. A&. A& s! a! i!))
   :qid internal_ens__vstd!seq.axiom_seq_push_index_different._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_push_index_different._definition
)))

;; Broadcast vstd::seq::axiom_seq_push_index_different
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_index_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
      (has_type i! INT)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) (vstd!seq.Seq.index.?
        A&. A& s! i!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
    :qid user_vstd__seq__axiom_seq_push_index_different_9
    :skolemid skolem_user_vstd__seq__axiom_seq_push_index_different_9
))))

;; Function-Specs vstd::seq::axiom_seq_update_len
(declare-fun req%vstd!seq.axiom_seq_update_len. (Dcr Type Poly Int Poly) Bool)
(declare-const %%global_location_label%%11 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!) (=>
     %%global_location_label%%11
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_len._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_update_len._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_len. (Dcr Type Poly Int Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!) (= (vstd!seq.Seq.len.? A&. A&
      (vstd!seq.Seq.update.? A&. A& s! (I i!) a!)
     ) (vstd!seq.Seq.len.? A&. A& s!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_len. A&. A& s! i! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_len._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_update_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_update_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
      (has_type a! A&)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!)) (vstd!seq.Seq.len.?
        A&. A& s!
    ))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!)))
    :qid user_vstd__seq__axiom_seq_update_len_10
    :skolemid skolem_user_vstd__seq__axiom_seq_update_len_10
))))

;; Function-Specs vstd::seq::axiom_seq_update_same
(declare-fun req%vstd!seq.axiom_seq_update_same. (Dcr Type Poly Int Poly) Bool)
(declare-const %%global_location_label%%12 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!) (=>
     %%global_location_label%%12
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_same._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_update_same._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_same. (Dcr Type Poly Int Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.update.? A&. A& s! (I i!) a!) (I i!)
     ) a!
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_same. A&. A& s! i! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_same._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_update_same._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_same
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_update_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
      (has_type a! A&)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!) i!) a!)
    ))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i! a!) i!))
    :qid user_vstd__seq__axiom_seq_update_same_11
    :skolemid skolem_user_vstd__seq__axiom_seq_update_same_11
))))

;; Function-Specs vstd::seq::axiom_seq_update_different
(declare-fun req%vstd!seq.axiom_seq_update_different. (Dcr Type Poly Int Int Poly)
 Bool
)
(declare-const %%global_location_label%%13 Bool)
(declare-const %%global_location_label%%14 Bool)
(declare-const %%global_location_label%%15 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Int) (i2! Int) (a! Poly)) (!
   (= (req%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!) (and
     (=>
      %%global_location_label%%13
      (and
       (<= 0 i1!)
       (< i1! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%14
      (and
       (<= 0 i2!)
       (< i2! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%15
      (not (= i1! i2!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!))
   :qid internal_req__vstd!seq.axiom_seq_update_different._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_update_different._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_update_different. (Dcr Type Poly Int Int Poly)
 Bool
)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Int) (i2! Int) (a! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.update.? A&. A& s! (I i2!) a!) (I i1!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I i1!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_update_different. A&. A& s! i1! i2! a!))
   :qid internal_ens__vstd!seq.axiom_seq_update_different._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_update_different._definition
)))

;; Broadcast vstd::seq::axiom_seq_update_different
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_update_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i1! Poly) (i2! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i1! INT)
      (has_type i2! INT)
      (has_type a! A&)
     )
     (=>
      (and
       (and
        (and
         (<= 0 (%I i1!))
         (< (%I i1!) (vstd!seq.Seq.len.? A&. A& s!))
        )
        (and
         (<= 0 (%I i2!))
         (< (%I i2!) (vstd!seq.Seq.len.? A&. A& s!))
       ))
       (not (= i1! i2!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i2! a!) i1!) (vstd!seq.Seq.index.?
        A&. A& s! i1!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.update.? A&. A& s! i2! a!) i1!))
    :qid user_vstd__seq__axiom_seq_update_different_12
    :skolemid skolem_user_vstd__seq__axiom_seq_update_different_12
))))

;; Function-Specs vstd::seq::axiom_seq_ext_equal
(declare-fun ens%vstd!seq.axiom_seq_ext_equal. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_ext_equal. A&. A& s1! s2!) (= (ext_eq false (TYPE%vstd!seq.Seq.
       A&. A&
      ) s1! s2!
     ) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
        ))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_13
        :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_13
   )))))
   :pattern ((ens%vstd!seq.axiom_seq_ext_equal. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_ext_equal._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_ext_equal._definition
)))

;; Broadcast vstd::seq::axiom_seq_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (= (ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
       (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
       (forall ((i$ Poly)) (!
         (=>
          (has_type i$ INT)
          (=>
           (and
            (<= 0 (%I i$))
            (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
           )
           (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
         ))
         :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
         :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
         :qid user_vstd__seq__axiom_seq_ext_equal_14
         :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_14
    )))))
    :pattern ((ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_15
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_15
))))

;; Function-Specs vstd::seq::axiom_seq_ext_equal_deep
(declare-fun ens%vstd!seq.axiom_seq_ext_equal_deep. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_ext_equal_deep. A&. A& s1! s2!) (= (ext_eq true (TYPE%vstd!seq.Seq.
       A&. A&
      ) s1! s2!
     ) (and
      (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
          )
          (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
            i$
        ))))
        :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
        :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
        :qid user_vstd__seq__axiom_seq_ext_equal_deep_16
        :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_16
   )))))
   :pattern ((ens%vstd!seq.axiom_seq_ext_equal_deep. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_ext_equal_deep._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_ext_equal_deep._definition
)))

;; Broadcast vstd::seq::axiom_seq_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (= (ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
       (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
       (forall ((i$ Poly)) (!
         (=>
          (has_type i$ INT)
          (=>
           (and
            (<= 0 (%I i$))
            (< (%I i$) (vstd!seq.Seq.len.? A&. A& s1!))
           )
           (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
             i$
         ))))
         :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
         :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
         :qid user_vstd__seq__axiom_seq_ext_equal_deep_17
         :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_17
    )))))
    :pattern ((ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_deep_18
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_18
))))

;; Function-Specs vstd::seq::axiom_seq_subrange_len
(declare-fun req%vstd!seq.axiom_seq_subrange_len. (Dcr Type Poly Int Int) Bool)
(declare-const %%global_location_label%%16 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int)) (!
   (= (req%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!) (=>
     %%global_location_label%%16
     (and
      (and
       (<= 0 j!)
       (<= j! k!)
      )
      (<= k! (vstd!seq.Seq.len.? A&. A& s!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!))
   :qid internal_req__vstd!seq.axiom_seq_subrange_len._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_subrange_len._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_subrange_len. (Dcr Type Poly Int Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int)) (!
   (= (ens%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!) (= (vstd!seq.Seq.len.? A&.
      A& (vstd!seq.Seq.subrange.? A&. A& s! (I j!) (I k!))
     ) (Sub k! j!)
   ))
   :pattern ((ens%vstd!seq.axiom_seq_subrange_len. A&. A& s! j! k!))
   :qid internal_ens__vstd!seq.axiom_seq_subrange_len._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_subrange_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_subrange_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_subrange_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type j! INT)
      (has_type k! INT)
     )
     (=>
      (and
       (and
        (<= 0 (%I j!))
        (<= (%I j!) (%I k!))
       )
       (<= (%I k!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)) (Sub (%I k!)
        (%I j!)
    ))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)))
    :qid user_vstd__seq__axiom_seq_subrange_len_19
    :skolemid skolem_user_vstd__seq__axiom_seq_subrange_len_19
))))

;; Function-Specs vstd::seq::axiom_seq_subrange_index
(declare-fun req%vstd!seq.axiom_seq_subrange_index. (Dcr Type Poly Int Int Int) Bool)
(declare-const %%global_location_label%%17 Bool)
(declare-const %%global_location_label%%18 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!) (and
     (=>
      %%global_location_label%%17
      (and
       (and
        (<= 0 j!)
        (<= j! k!)
       )
       (<= k! (vstd!seq.Seq.len.? A&. A& s!))
     ))
     (=>
      %%global_location_label%%18
      (and
       (<= 0 i!)
       (< i! (Sub k! j!))
   ))))
   :pattern ((req%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!))
   :qid internal_req__vstd!seq.axiom_seq_subrange_index._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_subrange_index._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_subrange_index. (Dcr Type Poly Int Int Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Int) (k! Int) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!) (= (vstd!seq.Seq.index.?
      A&. A& (vstd!seq.Seq.subrange.? A&. A& s! (I j!) (I k!)) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s! (I (Add i! j!)))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_subrange_index. A&. A& s! j! k! i!))
   :qid internal_ens__vstd!seq.axiom_seq_subrange_index._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_subrange_index._definition
)))

;; Broadcast vstd::seq::axiom_seq_subrange_index
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_subrange_index.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type j! INT)
      (has_type k! INT)
      (has_type i! INT)
     )
     (=>
      (and
       (and
        (and
         (<= 0 (%I j!))
         (<= (%I j!) (%I k!))
        )
        (<= (%I k!) (vstd!seq.Seq.len.? A&. A& s!))
       )
       (and
        (<= 0 (%I i!))
        (< (%I i!) (Sub (%I k!) (%I j!)))
      ))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!) (vstd!seq.Seq.index.?
        A&. A& s! (I (Add (%I i!) (%I j!)))
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!))
    :qid user_vstd__seq__axiom_seq_subrange_index_20
    :skolemid skolem_user_vstd__seq__axiom_seq_subrange_index_20
))))

;; Function-Specs vstd::seq::axiom_seq_add_len
(declare-fun ens%vstd!seq.axiom_seq_add_len. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
   (= (ens%vstd!seq.axiom_seq_add_len. A&. A& s1! s2!) (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.?
       A&. A& s1! s2!
      )
     ) (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!)))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_len. A&. A& s1! s2!))
   :qid internal_ens__vstd!seq.axiom_seq_add_len._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_add_len._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_len.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)) (nClip (Add (vstd!seq.Seq.len.?
         A&. A& s1!
        ) (vstd!seq.Seq.len.? A&. A& s2!)
    ))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)))
    :qid user_vstd__seq__axiom_seq_add_len_21
    :skolemid skolem_user_vstd__seq__axiom_seq_add_len_21
))))

;; Function-Specs vstd::seq::axiom_seq_add_index1
(declare-fun req%vstd!seq.axiom_seq_add_index1. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%19 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!) (=>
     %%global_location_label%%19
     (and
      (<= 0 i!)
      (< i! (vstd!seq.Seq.len.? A&. A& s1!))
   )))
   :pattern ((req%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!))
   :qid internal_req__vstd!seq.axiom_seq_add_index1._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_add_index1._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_add_index1. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.add.? A&. A& s1! s2!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s1! (I i!))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_index1. A&. A& s1! s2! i!))
   :qid internal_ens__vstd!seq.axiom_seq_add_index1._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_add_index1._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_index1
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_index1.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (<= 0 (%I i!))
       (< (%I i!) (vstd!seq.Seq.len.? A&. A& s1!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
        A&. A& s1! i!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
    :qid user_vstd__seq__axiom_seq_add_index1_22
    :skolemid skolem_user_vstd__seq__axiom_seq_add_index1_22
))))

;; Function-Specs vstd::seq::axiom_seq_add_index2
(declare-fun req%vstd!seq.axiom_seq_add_index2. (Dcr Type Poly Poly Int) Bool)
(declare-const %%global_location_label%%20 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (req%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!) (=>
     %%global_location_label%%20
     (and
      (<= (vstd!seq.Seq.len.? A&. A& s1!) i!)
      (< i! (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))))
   )))
   :pattern ((req%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!))
   :qid internal_req__vstd!seq.axiom_seq_add_index2._definition
   :skolemid skolem_internal_req__vstd!seq.axiom_seq_add_index2._definition
)))
(declare-fun ens%vstd!seq.axiom_seq_add_index2. (Dcr Type Poly Poly Int) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Int)) (!
   (= (ens%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!) (= (vstd!seq.Seq.index.? A&.
      A& (vstd!seq.Seq.add.? A&. A& s1! s2!) (I i!)
     ) (vstd!seq.Seq.index.? A&. A& s2! (I (Sub i! (vstd!seq.Seq.len.? A&. A& s1!))))
   ))
   :pattern ((ens%vstd!seq.axiom_seq_add_index2. A&. A& s1! s2! i!))
   :qid internal_ens__vstd!seq.axiom_seq_add_index2._definition
   :skolemid skolem_internal_ens__vstd!seq.axiom_seq_add_index2._definition
)))

;; Broadcast vstd::seq::axiom_seq_add_index2
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_index2.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (<= (vstd!seq.Seq.len.? A&. A& s1!) (%I i!))
       (< (%I i!) (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
        A&. A& s2! (I (Sub (%I i!) (vstd!seq.Seq.len.? A&. A& s1!)))
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
    :qid user_vstd__seq__axiom_seq_add_index2_23
    :skolemid skolem_user_vstd__seq__axiom_seq_add_index2_23
))))

;; Function-Axioms vstd::slice::spec_slice_len
(assert
 (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
   (=>
    (has_type slice! (SLICE T&. T&))
    (uInv SZ (vstd!slice.spec_slice_len.? T&. T& slice!))
   )
   :pattern ((vstd!slice.spec_slice_len.? T&. T& slice!))
   :qid internal_vstd!slice.spec_slice_len.?_pre_post_definition
   :skolemid skolem_internal_vstd!slice.spec_slice_len.?_pre_post_definition
)))

;; Function-Specs vstd::slice::axiom_spec_len
(declare-fun ens%vstd!slice.axiom_spec_len. (Dcr Type Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
   (= (ens%vstd!slice.axiom_spec_len. T&. T& slice!) (= (vstd!slice.spec_slice_len.? T&.
      T& slice!
     ) (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (SLICE T&. T&) slice!))
   ))
   :pattern ((ens%vstd!slice.axiom_spec_len. T&. T& slice!))
   :qid internal_ens__vstd!slice.axiom_spec_len._definition
   :skolemid skolem_internal_ens__vstd!slice.axiom_spec_len._definition
)))

;; Broadcast vstd::slice::axiom_spec_len
(assert
 (=>
  (fuel_bool fuel%vstd!slice.axiom_spec_len.)
  (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
    (=>
     (has_type slice! (SLICE T&. T&))
     (= (vstd!slice.spec_slice_len.? T&. T& slice!) (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.?
        $ (SLICE T&. T&) slice!
    ))))
    :pattern ((vstd!slice.spec_slice_len.? T&. T& slice!))
    :qid user_vstd__slice__axiom_spec_len_24
    :skolemid skolem_user_vstd__slice__axiom_spec_len_24
))))

;; Function-Axioms vstd::std_specs::vec::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!std_specs.vec.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.vec.impl&%0.spec_index.)
  (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (=>
     (tr_bound%core!alloc.Allocator. A&. A&)
     (= (vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? $ (TYPE%alloc!vec.Vec. T&.
        T& A&. A&
       ) T&. T& self! i!
      ) (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec. T&. T&
         A&. A&
        ) self!
       ) i!
    )))
    :pattern ((vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.? $ (TYPE%alloc!vec.Vec.
       T&. T& A&. A&
      ) T&. T& self! i!
    ))
    :qid internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_definition
    :skolemid skolem_internal_vstd!std_specs.vec.VecAdditionalSpecFns.spec_index.?_definition
))))

;; Function-Axioms vstd::raw_ptr::impl&%4::view
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%4.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%4.view.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (CONST_PTR $) (PTR T&. T&) self!) (vstd!view.View.view.?
      $ (PTR T&. T&) self!
    ))
    :pattern ((vstd!view.View.view.? (CONST_PTR $) (PTR T&. T&) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%0::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%0.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%0.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (REF A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    )
    :pattern ((vstd!view.View.view.? (REF A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%2::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%2.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%2.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (BOX $ ALLOCATOR_GLOBAL A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (BOX $ ALLOCATOR_GLOBAL A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%4::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%4.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%4.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (RC $ ALLOCATOR_GLOBAL A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (RC $ ALLOCATOR_GLOBAL A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%6::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%6.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%6.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (ARC $ ALLOCATOR_GLOBAL A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (ARC $ ALLOCATOR_GLOBAL A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%10::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%10.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%10.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ TYPE%tuple%0. self!) self!)
    :pattern ((vstd!view.View.view.? $ TYPE%tuple%0. self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%12::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%12.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%12.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ BOOL self!) self!)
    :pattern ((vstd!view.View.view.? $ BOOL self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%20::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%20.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%20.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 64) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 64) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%24::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%24.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%24.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT SZ) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT SZ) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!view.View. $ (PTR T&. T&))
   :pattern ((tr_bound%vstd!view.View. $ (PTR T&. T&)))
   :qid internal_vstd__raw_ptr__impl&__3_trait_impl_definition
   :skolemid skolem_internal_vstd__raw_ptr__impl&__3_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!view.View. (CONST_PTR $) (PTR T&. T&))
   :pattern ((tr_bound%vstd!view.View. (CONST_PTR $) (PTR T&. T&)))
   :qid internal_vstd__raw_ptr__impl&__4_trait_impl_definition
   :skolemid skolem_internal_vstd__raw_ptr__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!view.View. $ (SLICE T&. T&))
   :pattern ((tr_bound%vstd!view.View. $ (SLICE T&. T&)))
   :qid internal_vstd__slice__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__slice__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (REF A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (REF A&.) A&))
   :qid internal_vstd__view__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (BOX $ ALLOCATOR_GLOBAL A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (BOX $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_vstd__view__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (RC $ ALLOCATOR_GLOBAL A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (RC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_vstd__view__impl&__4_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (ARC $ ALLOCATOR_GLOBAL A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (ARC $ ALLOCATOR_GLOBAL A&.) A&))
   :qid internal_vstd__view__impl&__6_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__6_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%core!alloc.Allocator. A&. A&)
    (tr_bound%vstd!view.View. $ (TYPE%alloc!vec.Vec. T&. T& A&. A&))
   )
   :pattern ((tr_bound%vstd!view.View. $ (TYPE%alloc!vec.Vec. T&. T& A&. A&)))
   :qid internal_vstd__view__impl&__8_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__8_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ TYPE%tuple%0.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT SZ))
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option. T&.
     T&
    ) T&. T&
   )
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option.
      T&. T&
     ) T&. T&
   ))
   :qid internal_vstd__std_specs__option__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__option__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%core!alloc.Allocator. A&. A&)
    (tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. $ (TYPE%alloc!vec.Vec. T&. T& A&.
      A&
     ) T&. T&
   ))
   :pattern ((tr_bound%vstd!std_specs.vec.VecAdditionalSpecFns. $ (TYPE%alloc!vec.Vec.
      T&. T& A&. A&
     ) T&. T&
   ))
   :qid internal_vstd__std_specs__vec__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__vec__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%core!alloc.Allocator. A&. A&)
    (tr_bound%core!alloc.Allocator. (REF A&.) A&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (REF A&.) A&))
   :qid internal_core__alloc__impl&__2_trait_impl_definition
   :skolemid skolem_internal_core__alloc__impl&__2_trait_impl_definition
)))

;; Function-Def vectors::pusher
;; rust_verify/example/vectors.rs:104:1: 104:24 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const no%param Int)
 (declare-const tmp%1 Poly)
 (declare-const verus_tmp_goal@ vstd!seq.Seq<u64.>.)
 (declare-const tmp%2 Bool)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 core!option.Option.)
 (declare-const tmp%5 Bool)
 (declare-const v@0 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const verus_tmp@0 vstd!seq.Seq<u64.>.)
 (declare-const goal@0 vstd!seq.Seq<u64.>.)
 (assert
  fuel_defaults
 )
 (declare-fun %%lambda%%0 (Int) %%Function%%)
 (assert
  (forall ((%%hole%%0 Int) (i$ Poly)) (!
    (= (%%apply%%0 (%%lambda%%0 %%hole%%0) i$) (I (uClip %%hole%%0 (%I i$))))
    :pattern ((%%apply%%0 (%%lambda%%0 %%hole%%0) i$))
 )))
 (declare-const v@1 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const v@2 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const v@3 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const v@4 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const v@5 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const verus_tmp@1 vstd!seq.Seq<u64.>.)
 (declare-const goal@1 vstd!seq.Seq<u64.>.)
 (declare-const v@6 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const v@7 alloc!vec.Vec<u64./allocator_global%.>.)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 (assert
  (not (=>
    (ens%alloc!vec.impl&%0.new. $ (UINT 64) tmp%1)
    (=>
     (= v@0 (%Poly%alloc!vec.Vec<u64./allocator_global%.>. tmp%1))
     (=>
      (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
        v@0
       ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@1) (I 0)
      )
      (=>
       (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
         v@1
        ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@2) (I 1)
       )
       (=>
        (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
          v@2
         ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@3) (I 2)
        )
        (=>
         (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
           v@3
          ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@4) (I 3)
         )
         (=>
          (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
            v@4
           ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@5) (I 4)
          )
          (=>
           (= verus_tmp@1 (%Poly%vstd!seq.Seq<u64.>. (vstd!seq.Seq.new.? $ (UINT 64) $ (TYPE%fun%1.
               $ INT $ (UINT 64)
              ) (I 5) (Poly%fun%1. (mk_fun (%%lambda%%0 64)))
           )))
           (=>
            (= verus_tmp_goal@ verus_tmp@1)
            (=>
             (= goal@1 verus_tmp_goal@)
             (=>
              (= tmp%2 (ext_eq false (TYPE%vstd!seq.Seq. $ (UINT 64)) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                  $ (UINT 64) $ ALLOCATOR_GLOBAL
                 ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@5)
                ) (Poly%vstd!seq.Seq<u64.>. goal@1)
              ))
              (and
               (=>
                %%location_label%%0
                tmp%2
               )
               (=>
                tmp%2
                (=>
                 (= tmp%3 (= (%I (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                       $ (UINT 64) $ ALLOCATOR_GLOBAL
                      ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@5)
                     ) (I 2)
                    )
                   ) 2
                 ))
                 (and
                  (=>
                   %%location_label%%1
                   tmp%3
                  )
                  (=>
                   tmp%3
                   (=>
                    (ens%alloc!vec.impl&%1.pop. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
                      v@5
                     ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@6) tmp%4
                    )
                    (=>
                     (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
                       v@6
                      ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@7) (I 4)
                     )
                     (=>
                      (= tmp%5 (ext_eq false (TYPE%vstd!seq.Seq. $ (UINT 64)) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                          $ (UINT 64) $ ALLOCATOR_GLOBAL
                         ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. v@7)
                        ) (Poly%vstd!seq.Seq<u64.>. goal@1)
                      ))
                      (=>
                       %%location_label%%2
                       tmp%5
 ))))))))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs vectors::pop_test
(declare-fun req%vectors!pop_test. (alloc!vec.Vec<u64./allocator_global%.>.) Bool)
(declare-const %%global_location_label%%21 Bool)
(declare-const %%global_location_label%%22 Bool)
(assert
 (forall ((t! alloc!vec.Vec<u64./allocator_global%.>.)) (!
   (= (req%vectors!pop_test. t!) (and
     (=>
      %%global_location_label%%21
      (> (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
         t!
        )
       ) 0
     ))
     (=>
      %%global_location_label%%22
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
              t!
          ))))
          (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
              $ (UINT 64) $ ALLOCATOR_GLOBAL
             ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
            ) i$
        ))))
        :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
            $ (UINT 64) $ ALLOCATOR_GLOBAL
           ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
          ) i$
        ))
        :qid user_vectors__pop_test_25
        :skolemid skolem_user_vectors__pop_test_25
   )))))
   :pattern ((req%vectors!pop_test. t!))
   :qid internal_req__vectors!pop_test._definition
   :skolemid skolem_internal_req__vectors!pop_test._definition
)))

;; Function-Def vectors::pop_test
;; rust_verify/example/vectors.rs:122:1: 122:25 (#0)
(get-info :all-statistics)
(push)
 (declare-const t! alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const tmp%1 core!option.Option.)
 (declare-const tmp%2 Poly)
 (declare-const tmp%3 Bool)
 (declare-const tmp%4 Bool)
 (declare-const t@0 alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const x@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (> (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
     t!
    )
   ) 0
 ))
 (assert
  (forall ((i$ Poly)) (!
    (=>
     (has_type i$ INT)
     (=>
      (and
       (<= 0 (%I i$))
       (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
          t!
      ))))
      (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
          $ (UINT 64) $ ALLOCATOR_GLOBAL
         ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
        ) i$
    ))))
    :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
        $ (UINT 64) $ ALLOCATOR_GLOBAL
       ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
      ) i$
    ))
    :qid user_vectors__pop_test_27
    :skolemid skolem_user_vectors__pop_test_27
 )))
 (declare-const t@1 alloc!vec.Vec<u64./allocator_global%.>.)
 ;; precondition not satisfied
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 (assert
  (not (=>
    (= t@0 t!)
    (=>
     (ens%alloc!vec.impl&%1.pop. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
       t@0
      ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1) tmp%1
     )
     (and
      (=>
       %%location_label%%0
       (req%core!option.impl&%0.unwrap. $ (UINT 64) tmp%1)
      )
      (=>
       (ens%core!option.impl&%0.unwrap. $ (UINT 64) tmp%1 tmp%2)
       (=>
        (= x@ (%I tmp%2))
        (=>
         (= tmp%3 (vectors!uninterp_fn.? (I x@)))
         (and
          (=>
           %%location_label%%1
           tmp%3
          )
          (=>
           tmp%3
           (=>
            (= tmp%4 (forall ((i$ Poly)) (!
               (=>
                (has_type i$ INT)
                (=>
                 (and
                  (<= 0 (%I i$))
                  (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
                     t@1
                 ))))
                 (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                     $ (UINT 64) $ ALLOCATOR_GLOBAL
                    ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1)
                   ) i$
               ))))
               :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
                   $ (UINT 64) $ ALLOCATOR_GLOBAL
                  ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1)
                 ) i$
               ))
               :qid user_vectors__pop_test_26
               :skolemid skolem_user_vectors__pop_test_26
            )))
            (=>
             %%location_label%%2
             tmp%4
 ))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Specs vectors::push_test
(declare-fun req%vectors!push_test. (alloc!vec.Vec<u64./allocator_global%.>. Int)
 Bool
)
(declare-const %%global_location_label%%23 Bool)
(declare-const %%global_location_label%%24 Bool)
(assert
 (forall ((t! alloc!vec.Vec<u64./allocator_global%.>.) (y! Int)) (!
   (= (req%vectors!push_test. t! y!) (and
     (=>
      %%global_location_label%%23
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (<= 0 (%I i$))
           (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
              t!
          ))))
          (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
              $ (UINT 64) $ ALLOCATOR_GLOBAL
             ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
            ) i$
        ))))
        :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
            $ (UINT 64) $ ALLOCATOR_GLOBAL
           ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
          ) i$
        ))
        :qid user_vectors__push_test_28
        :skolemid skolem_user_vectors__push_test_28
     )))
     (=>
      %%global_location_label%%24
      (vectors!uninterp_fn.? (I y!))
   )))
   :pattern ((req%vectors!push_test. t! y!))
   :qid internal_req__vectors!push_test._definition
   :skolemid skolem_internal_req__vectors!push_test._definition
)))

;; Function-Def vectors::push_test
;; rust_verify/example/vectors.rs:133:1: 133:34 (#0)
(get-info :all-statistics)
(push)
 (declare-const t! alloc!vec.Vec<u64./allocator_global%.>.)
 (declare-const y! Int)
 (declare-const tmp%1 Bool)
 (declare-const t@0 alloc!vec.Vec<u64./allocator_global%.>.)
 (assert
  fuel_defaults
 )
 (assert
  (uInv 64 y!)
 )
 (assert
  (forall ((i$ Poly)) (!
    (=>
     (has_type i$ INT)
     (=>
      (and
       (<= 0 (%I i$))
       (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
          t!
      ))))
      (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
          $ (UINT 64) $ ALLOCATOR_GLOBAL
         ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
        ) i$
    ))))
    :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
        $ (UINT 64) $ ALLOCATOR_GLOBAL
       ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t!)
      ) i$
    ))
    :qid user_vectors__push_test_30
    :skolemid skolem_user_vectors__push_test_30
 )))
 (assert
  (vectors!uninterp_fn.? (I y!))
 )
 (declare-const t@1 alloc!vec.Vec<u64./allocator_global%.>.)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 (assert
  (not (=>
    (= t@0 t!)
    (=>
     (ens%alloc!vec.impl&%1.push. $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
       t@0
      ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1) (I y!)
     )
     (=>
      (= tmp%1 (forall ((i$ Poly)) (!
         (=>
          (has_type i$ INT)
          (=>
           (and
            (<= 0 (%I i$))
            (< (%I i$) (vstd!std_specs.vec.spec_vec_len.? $ (UINT 64) $ ALLOCATOR_GLOBAL (Poly%alloc!vec.Vec<u64./allocator_global%.>.
               t@1
           ))))
           (vectors!uninterp_fn.? (vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
               $ (UINT 64) $ ALLOCATOR_GLOBAL
              ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1)
             ) i$
         ))))
         :pattern ((vstd!seq.Seq.index.? $ (UINT 64) (vstd!view.View.view.? $ (TYPE%alloc!vec.Vec.
             $ (UINT 64) $ ALLOCATOR_GLOBAL
            ) (Poly%alloc!vec.Vec<u64./allocator_global%.>. t@1)
           ) i$
         ))
         :qid user_vectors__push_test_29
         :skolemid skolem_user_vectors__push_test_29
      )))
      (=>
       %%location_label%%0
       tmp%1
 ))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)
