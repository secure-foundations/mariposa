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

;; Fuel
(assert
 true
)

;; Datatypes
(declare-sort anonymous_closure%11. 0)
(declare-sort vstd!thread.IsThread. 0)
(declare-sort vstd!thread.JoinHandle<tuple%0.>. 0)
(declare-sort vstd!thread.ThreadId. 0)
(declare-datatypes ((tuple%0. 0) (tuple%2. 0)) (((tuple%0./tuple%0)) ((tuple%2./tuple%2
    (tuple%2./tuple%2/?field%0 Poly) (tuple%2./tuple%2/?field%1 Poly)
))))
(declare-fun tuple%2./tuple%2/field%0 (tuple%2.) Poly)
(declare-fun tuple%2./tuple%2/field%1 (tuple%2.) Poly)
(declare-fun TYPE%vstd!thread.JoinHandle. (Type) Type)
(declare-const TYPE%vstd!thread.ThreadId. Type)
(declare-const TYPE%vstd!thread.IsThread. Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun TYPE%tuple%2. (Type Type) Type)
(declare-const TYPE%anonymous_closure%11. Type)
(declare-fun Poly%anonymous_closure%11. (anonymous_closure%11.) Poly)
(declare-fun %Poly%anonymous_closure%11. (Poly) anonymous_closure%11.)
(declare-fun Poly%vstd!thread.IsThread. (vstd!thread.IsThread.) Poly)
(declare-fun %Poly%vstd!thread.IsThread. (Poly) vstd!thread.IsThread.)
(declare-fun Poly%vstd!thread.JoinHandle<tuple%0.>. (vstd!thread.JoinHandle<tuple%0.>.)
 Poly
)
(declare-fun %Poly%vstd!thread.JoinHandle<tuple%0.>. (Poly) vstd!thread.JoinHandle<tuple%0.>.)
(declare-fun Poly%vstd!thread.ThreadId. (vstd!thread.ThreadId.) Poly)
(declare-fun %Poly%vstd!thread.ThreadId. (Poly) vstd!thread.ThreadId.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun %Poly%tuple%2. (Poly) tuple%2.)
(assert
 (forall ((x@ anonymous_closure%11.)) (!
   (= x@ (%Poly%anonymous_closure%11. (Poly%anonymous_closure%11. x@)))
   :pattern ((Poly%anonymous_closure%11. x@))
   :qid
   internal_crate__anonymous_closure__11_box_axiom_definition
   :skolemid
   skolem_internal_crate__anonymous_closure__11_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%anonymous_closure%11.)
    (= x@ (Poly%anonymous_closure%11. (%Poly%anonymous_closure%11. x@)))
   )
   :pattern ((has_type x@ TYPE%anonymous_closure%11.))
   :qid
   internal_crate__anonymous_closure__11_unbox_axiom_definition
   :skolemid
   skolem_internal_crate__anonymous_closure__11_unbox_axiom_definition
)))
(assert
 (forall ((x@ anonymous_closure%11.)) (!
   (has_type (Poly%anonymous_closure%11. x@) TYPE%anonymous_closure%11.)
   :pattern ((has_type (Poly%anonymous_closure%11. x@) TYPE%anonymous_closure%11.))
   :qid
   internal_crate__anonymous_closure__11_has_type_always_definition
   :skolemid
   skolem_internal_crate__anonymous_closure__11_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!thread.IsThread.)) (!
   (= x@ (%Poly%vstd!thread.IsThread. (Poly%vstd!thread.IsThread. x@)))
   :pattern ((Poly%vstd!thread.IsThread. x@))
   :qid
   internal_vstd__thread__IsThread_box_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__IsThread_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%vstd!thread.IsThread.)
    (= x@ (Poly%vstd!thread.IsThread. (%Poly%vstd!thread.IsThread. x@)))
   )
   :pattern ((has_type x@ TYPE%vstd!thread.IsThread.))
   :qid
   internal_vstd__thread__IsThread_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__IsThread_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!thread.IsThread.)) (!
   (has_type (Poly%vstd!thread.IsThread. x@) TYPE%vstd!thread.IsThread.)
   :pattern ((has_type (Poly%vstd!thread.IsThread. x@) TYPE%vstd!thread.IsThread.))
   :qid
   internal_vstd__thread__IsThread_has_type_always_definition
   :skolemid
   skolem_internal_vstd__thread__IsThread_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!thread.JoinHandle<tuple%0.>.)) (!
   (= x@ (%Poly%vstd!thread.JoinHandle<tuple%0.>. (Poly%vstd!thread.JoinHandle<tuple%0.>.
      x@
   )))
   :pattern ((Poly%vstd!thread.JoinHandle<tuple%0.>. x@))
   :qid
   internal_vstd__thread__JoinHandle<tuple__0.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__JoinHandle<tuple__0.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!thread.JoinHandle. TYPE%tuple%0.))
    (= x@ (Poly%vstd!thread.JoinHandle<tuple%0.>. (%Poly%vstd!thread.JoinHandle<tuple%0.>.
       x@
   ))))
   :pattern ((has_type x@ (TYPE%vstd!thread.JoinHandle. TYPE%tuple%0.)))
   :qid
   internal_vstd__thread__JoinHandle<tuple__0.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__JoinHandle<tuple__0.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!thread.JoinHandle<tuple%0.>.)) (!
   (has_type (Poly%vstd!thread.JoinHandle<tuple%0.>. x@) (TYPE%vstd!thread.JoinHandle.
     TYPE%tuple%0.
   ))
   :pattern ((has_type (Poly%vstd!thread.JoinHandle<tuple%0.>. x@) (TYPE%vstd!thread.JoinHandle.
      TYPE%tuple%0.
   )))
   :qid
   internal_vstd__thread__JoinHandle<tuple__0.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__thread__JoinHandle<tuple__0.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!thread.ThreadId.)) (!
   (= x@ (%Poly%vstd!thread.ThreadId. (Poly%vstd!thread.ThreadId. x@)))
   :pattern ((Poly%vstd!thread.ThreadId. x@))
   :qid
   internal_vstd__thread__ThreadId_box_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__ThreadId_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%vstd!thread.ThreadId.)
    (= x@ (Poly%vstd!thread.ThreadId. (%Poly%vstd!thread.ThreadId. x@)))
   )
   :pattern ((has_type x@ TYPE%vstd!thread.ThreadId.))
   :qid
   internal_vstd__thread__ThreadId_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__thread__ThreadId_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!thread.ThreadId.)) (!
   (has_type (Poly%vstd!thread.ThreadId. x@) TYPE%vstd!thread.ThreadId.)
   :pattern ((has_type (Poly%vstd!thread.ThreadId. x@) TYPE%vstd!thread.ThreadId.))
   :qid
   internal_vstd__thread__ThreadId_has_type_always_definition
   :skolemid
   skolem_internal_vstd__thread__ThreadId_has_type_always_definition
)))
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
(assert
 (forall ((x@ tuple%2.)) (!
   (= x@ (%Poly%tuple%2. (Poly%tuple%2. x@)))
   :pattern ((Poly%tuple%2. x@))
   :qid
   internal_crate__tuple__2_box_axiom_definition
   :skolemid
   skolem_internal_crate__tuple__2_box_axiom_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%tuple%2. T%0& T%1&))
    (= x@ (Poly%tuple%2. (%Poly%tuple%2. x@)))
   )
   :pattern ((has_type x@ (TYPE%tuple%2. T%0& T%1&)))
   :qid
   internal_crate__tuple__2_unbox_axiom_definition
   :skolemid
   skolem_internal_crate__tuple__2_unbox_axiom_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (field%0@ Poly) (field%1@ Poly)) (!
   (=>
    (and
     (has_type field%0@ T%0&)
     (has_type field%1@ T%1&)
    )
    (has_type (Poly%tuple%2. (tuple%2./tuple%2 field%0@ field%1@)) (TYPE%tuple%2. T%0&
      T%1&
   )))
   :pattern ((has_type (Poly%tuple%2. (tuple%2./tuple%2 field%0@ field%1@)) (TYPE%tuple%2.
      T%0& T%1&
   )))
   :qid
   internal_tuple__2./tuple__2_constructor_definition
   :skolemid
   skolem_internal_tuple__2./tuple__2_constructor_definition
)))
(assert
 (forall ((x@ tuple%2.)) (!
   (= (tuple%2./tuple%2/field%0 x@) (tuple%2./tuple%2/?field%0 x@))
   :pattern ((tuple%2./tuple%2/field%0 x@))
   :qid
   internal_tuple__2./tuple__2/field__0_accessor_definition
   :skolemid
   skolem_internal_tuple__2./tuple__2/field__0_accessor_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%tuple%2. T%0& T%1&))
    (has_type (tuple%2./tuple%2/field%0 (%Poly%tuple%2. x@)) T%0&)
   )
   :pattern ((tuple%2./tuple%2/field%0 (%Poly%tuple%2. x@)) (has_type x@ (TYPE%tuple%2.
      T%0& T%1&
   )))
   :qid
   internal_tuple__2./tuple__2/field__0_invariant_definition
   :skolemid
   skolem_internal_tuple__2./tuple__2/field__0_invariant_definition
)))
(assert
 (forall ((x@ tuple%2.)) (!
   (= (tuple%2./tuple%2/field%1 x@) (tuple%2./tuple%2/?field%1 x@))
   :pattern ((tuple%2./tuple%2/field%1 x@))
   :qid
   internal_tuple__2./tuple__2/field__1_accessor_definition
   :skolemid
   skolem_internal_tuple__2./tuple__2/field__1_accessor_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%tuple%2. T%0& T%1&))
    (has_type (tuple%2./tuple%2/field%1 (%Poly%tuple%2. x@)) T%1&)
   )
   :pattern ((tuple%2./tuple%2/field%1 (%Poly%tuple%2. x@)) (has_type x@ (TYPE%tuple%2.
      T%0& T%1&
   )))
   :qid
   internal_tuple__2./tuple__2/field__1_invariant_definition
   :skolemid
   skolem_internal_tuple__2./tuple__2/field__1_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (< (height (tuple%2./tuple%2/field%0 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/field%0 x)))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (< (height (tuple%2./tuple%2/field%1 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/field%1 x)))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))

;; Function-Decl vstd::thread::JoinHandle::predicate
(declare-fun vstd!thread.JoinHandle.predicate.? (Type Poly Poly) Bool)

;; Function-Decl vstd::thread::IsThread::view
(declare-fun vstd!thread.IsThread.view.? (Poly) vstd!thread.ThreadId.)

;; Function-Axioms vstd::thread::IsThread::agrees
(declare-fun ens%vstd!thread.IsThread.agrees. (vstd!thread.IsThread. vstd!thread.IsThread.)
 Bool
)
(assert
 (forall ((self~2@ vstd!thread.IsThread.) (other~4@ vstd!thread.IsThread.)) (!
   (= (ens%vstd!thread.IsThread.agrees. self~2@ other~4@) (= (vstd!thread.IsThread.view.?
      (Poly%vstd!thread.IsThread. self~2@)
     ) (vstd!thread.IsThread.view.? (Poly%vstd!thread.IsThread. other~4@))
   ))
   :pattern ((ens%vstd!thread.IsThread.agrees. self~2@ other~4@))
   :qid
   internal_ens__vstd!thread.IsThread.agrees._definition
   :skolemid
   skolem_internal_ens__vstd!thread.IsThread.agrees._definition
)))

;; Function-Specs vstd::thread::spawn
(declare-fun req%vstd!thread.spawn. (Type Type Poly) Bool)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((F& Type) (Ret& Type) (f~2@ Poly)) (!
   (= (req%vstd!thread.spawn. F& Ret& f~2@) (=>
     %%global_location_label%%0
     (closure_req F& TYPE%tuple%0. f~2@ (Poly%tuple%0. tuple%0./tuple%0))
   ))
   :pattern ((req%vstd!thread.spawn. F& Ret& f~2@))
   :qid
   internal_req__vstd!thread.spawn._definition
   :skolemid
   skolem_internal_req__vstd!thread.spawn._definition
)))

;; Function-Axioms vstd::thread::spawn
(declare-fun ens%vstd!thread.spawn. (Type Type Poly Poly) Bool)
(assert
 (forall ((F& Type) (Ret& Type) (f~2@ Poly) (handle~22@ Poly)) (!
   (= (ens%vstd!thread.spawn. F& Ret& f~2@ handle~22@) (and
     (has_type handle~22@ (TYPE%vstd!thread.JoinHandle. Ret&))
     (forall ((ret~31$ Poly)) (!
       (=>
        (has_type ret~31$ Ret&)
        (=>
         (vstd!thread.JoinHandle.predicate.? Ret& handle~22@ ret~31$)
         (closure_ens F& TYPE%tuple%0. f~2@ (Poly%tuple%0. tuple%0./tuple%0) ret~31$)
       ))
       :pattern ((vstd!thread.JoinHandle.predicate.? Ret& handle~22@ ret~31$))
       :qid
       user_vstd__thread__spawn_0
       :skolemid
       skolem_user_vstd__thread__spawn_0
   ))))
   :pattern ((ens%vstd!thread.spawn. F& Ret& f~2@ handle~22@))
   :qid
   internal_ens__vstd!thread.spawn._definition
   :skolemid
   skolem_internal_ens__vstd!thread.spawn._definition
)))

;; Function-Axioms vstd::thread::thread_id
(declare-fun ens%vstd!thread.thread_id. (Int tuple%2.) Bool)
(assert
 (forall ((no%param@ Int) (res~8@ tuple%2.)) (!
   (= (ens%vstd!thread.thread_id. no%param@ res~8@) (and
     (has_type (Poly%tuple%2. res~8@) (TYPE%tuple%2. TYPE%vstd!thread.ThreadId. TYPE%vstd!thread.IsThread.))
     (= (vstd!thread.IsThread.view.? (tuple%2./tuple%2/field%1 (%Poly%tuple%2. (Poly%tuple%2.
          res~8@
       )))
      ) (%Poly%vstd!thread.ThreadId. (tuple%2./tuple%2/field%0 (%Poly%tuple%2. (Poly%tuple%2.
          res~8@
   )))))))
   :pattern ((ens%vstd!thread.thread_id. no%param@ res~8@))
   :qid
   internal_ens__vstd!thread.thread_id._definition
   :skolemid
   skolem_internal_ens__vstd!thread.thread_id._definition
)))

;; Function-Def thread::main
(push)
 (declare-const no%param@ Int)
 (assert
  fuel_defaults
 )
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not true)
 ))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def thread::test_calling_thread_id_twice_same_value
(push)
 (declare-const no%param@ Int)
 (declare-const tmp%1@ Bool)
 (declare-const tmp%%1@ tuple%2.)
 (declare-const tid1~6@ vstd!thread.ThreadId.)
 (declare-const verus_tmp_is1~7@ vstd!thread.IsThread.)
 (declare-const is1~11@0 vstd!thread.IsThread.)
 (declare-const tmp%%2@ tuple%2.)
 (declare-const tid2~28@ vstd!thread.ThreadId.)
 (declare-const verus_tmp_is2~29@ vstd!thread.IsThread.)
 (declare-const is2~33@0 vstd!thread.IsThread.)
 (assert
  fuel_defaults
 )
 (declare-const is1~11@1 vstd!thread.IsThread.)
 (declare-const is2~33@1 vstd!thread.IsThread.)
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (ens%vstd!thread.thread_id. 0 tmp%%1@)
     (=>
      (= tid1~6@ (%Poly%vstd!thread.ThreadId. (tuple%2./tuple%2/field%0 (%Poly%tuple%2. (Poly%tuple%2.
           tmp%%1@
      )))))
      (=>
       (= verus_tmp_is1~7@ (%Poly%vstd!thread.IsThread. (tuple%2./tuple%2/field%1 (%Poly%tuple%2.
           (Poly%tuple%2. tmp%%1@)
       ))))
       (=>
        (= is1~11@1 verus_tmp_is1~7@)
        (=>
         (ens%vstd!thread.thread_id. 0 tmp%%2@)
         (=>
          (= tid2~28@ (%Poly%vstd!thread.ThreadId. (tuple%2./tuple%2/field%0 (%Poly%tuple%2. (Poly%tuple%2.
               tmp%%2@
          )))))
          (=>
           (= verus_tmp_is2~29@ (%Poly%vstd!thread.IsThread. (tuple%2./tuple%2/field%1 (%Poly%tuple%2.
               (Poly%tuple%2. tmp%%2@)
           ))))
           (=>
            (= is2~33@1 verus_tmp_is2~29@)
            (=>
             (ens%vstd!thread.IsThread.agrees. is1~11@1 is2~33@1)
             (=>
              (= tmp%1@ (= tid1~6@ tid2~28@))
              (=>
               %%location_label%%0
               tmp%1@
 ))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 0)
 (check-sat)
 (set-option :rlimit 0)
(pop)

;; Function-Def thread::test_calling_thread_id_twice_diff_threads
(push)
 (declare-const no%param@ Int)
 (declare-const %closure_return27@ tuple%0.)
 (declare-const tmp%%2@ tuple%2.)
 (declare-const tid2~33@ vstd!thread.ThreadId.)
 (declare-const verus_tmp_is2~34@ vstd!thread.IsThread.)
 (declare-const is2~38@0 vstd!thread.IsThread.)
 (declare-const tmp%%3@ anonymous_closure%11.)
 (declare-const tmp%1@ Poly)
 (declare-const tmp%%1@ tuple%2.)
 (declare-const tid1~6@ vstd!thread.ThreadId.)
 (declare-const verus_tmp_is1~7@ vstd!thread.IsThread.)
 (declare-const is1~11@0 vstd!thread.IsThread.)
 (assert
  fuel_defaults
 )
 (declare-const is1~11@1 vstd!thread.IsThread.)
 (declare-const is2~38@1 vstd!thread.IsThread.)
 ;; precondition not satisfied
 (declare-const %%location_label%%0 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (ens%vstd!thread.thread_id. 0 tmp%%1@)
     (=>
      (= tid1~6@ (%Poly%vstd!thread.ThreadId. (tuple%2./tuple%2/field%0 (%Poly%tuple%2. (Poly%tuple%2.
           tmp%%1@
      )))))
      (=>
       (= verus_tmp_is1~7@ (%Poly%vstd!thread.IsThread. (tuple%2./tuple%2/field%1 (%Poly%tuple%2.
           (Poly%tuple%2. tmp%%1@)
       ))))
       (=>
        (= is1~11@1 verus_tmp_is1~7@)
        (=>
         (forall ((tmp%%4$ Poly)) (!
           (=>
            (has_type tmp%%4$ TYPE%tuple%0.)
            (closure_req TYPE%anonymous_closure%11. TYPE%tuple%0. (Poly%anonymous_closure%11. tmp%%3@)
             tmp%%4$
           ))
           :pattern ((closure_req TYPE%anonymous_closure%11. TYPE%tuple%0. (Poly%anonymous_closure%11.
              tmp%%3@
             ) tmp%%4$
           ))
           :qid
           user_thread__test_calling_thread_id_twice_diff_threads_1
           :skolemid
           skolem_user_thread__test_calling_thread_id_twice_diff_threads_1
         ))
         (=>
          %%location_label%%0
          (req%vstd!thread.spawn. TYPE%anonymous_closure%11. TYPE%tuple%0. (Poly%anonymous_closure%11.
            tmp%%3@
 )))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 0)
 (check-sat)
 (set-option :rlimit 0)
(pop)
