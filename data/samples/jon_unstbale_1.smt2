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
(declare-fun REF (Type) Type)
(declare-fun MUT_REF (Type) Type)
(declare-fun BOX (Type) Type)
(declare-fun RC (Type) Type)
(declare-fun ARC (Type) Type)
(declare-fun GHOST (Type) Type)
(declare-fun TRACKED (Type) Type)
(declare-fun NEVER (Type) Type)
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
(declare-fun ext_eq (Bool Type Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (td Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t td x y))
   :pattern ((ext_eq deep t td x y))
   :qid
   prelude_ext_eq
   :skolemid
   skolem_prelude_ext_eq
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
(declare-fun closure_req (Type Type Type Type Poly Poly) Bool)
(declare-fun closure_ens (Type Type Type Type Poly Poly Poly) Bool)

;; MODULE 'journal::LinkedJournal_v'

;; Fuel
(declare-const fuel%vstd!map.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!map.impl&%0.contains_key. FuelId)
(declare-const fuel%vstd!map.impl&%0.le. FuelId)
(declare-const fuel%vstd!map.check_argument_is_map. FuelId)
(declare-const fuel%vstd!option.impl&%1.spec_unwrap. FuelId)
(declare-const fuel%vstd!set.impl&%0.subset_of. FuelId)
(declare-const fuel%vstd!set.impl&%0.choose. FuelId)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.wf. FuelId)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains. FuelId)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.
 FuelId
)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty. FuelId)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow. FuelId)
(declare-const fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%0.wf. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%0.has_link. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%0.cropped_prior. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%0.contains_lsn. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.entries_wf. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.
 FuelId
)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.
 FuelId
)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.
 FuelId
)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.wf. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.acyclic. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.the_ranking. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.decodable. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.discard_old. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.
 FuelId
)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.build_tight. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.representation. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.can_crop. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.iptr. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.next. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%1.is_tight. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.wf. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_start. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_end. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.discard_old. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.decodable. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.can_crop. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.crop. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.append_record. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.build_tight. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.representation. FuelId)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.
 FuelId
)
(declare-const fuel%bundle!journal.LinkedJournal_v.impl&%2.mkfs. FuelId)
(assert
 (distinct fuel%vstd!map.impl&%0.spec_index. fuel%vstd!map.impl&%0.contains_key. fuel%vstd!map.impl&%0.le.
  fuel%vstd!map.check_argument_is_map. fuel%vstd!option.impl&%1.spec_unwrap. fuel%vstd!set.impl&%0.subset_of.
  fuel%vstd!set.impl&%0.choose. fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.wf.
  fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains. fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.
  fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty. fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.
  fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat. fuel%bundle!journal.LinkedJournal_v.impl&%0.wf.
  fuel%bundle!journal.LinkedJournal_v.impl&%0.has_link. fuel%bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.
  fuel%bundle!journal.LinkedJournal_v.impl&%0.contains_lsn. fuel%bundle!journal.LinkedJournal_v.impl&%1.entries_wf.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer. fuel%bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat. fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link. fuel%bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.wf. fuel%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.acyclic. fuel%bundle!journal.LinkedJournal_v.impl&%1.the_ranking.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.decodable. fuel%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.discard_old. fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn. fuel%bundle!journal.LinkedJournal_v.impl&%1.build_tight.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.representation. fuel%bundle!journal.LinkedJournal_v.impl&%1.can_crop.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop. fuel%bundle!journal.LinkedJournal_v.impl&%1.iptr.
  fuel%bundle!journal.LinkedJournal_v.impl&%1.next. fuel%bundle!journal.LinkedJournal_v.impl&%1.is_tight.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.wf. fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_start.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_end. fuel%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.discard_old. fuel%bundle!journal.LinkedJournal_v.impl&%2.decodable.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.can_crop. fuel%bundle!journal.LinkedJournal_v.impl&%2.crop.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.append_record. fuel%bundle!journal.LinkedJournal_v.impl&%2.build_tight.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.representation. fuel%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.
  fuel%bundle!journal.LinkedJournal_v.impl&%2.mkfs.
))

;; Datatypes
(declare-sort vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
 0
)
(declare-sort vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. 0)
(declare-sort vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
 0
)
(declare-sort vstd!set.Set<nat.>. 0)
(declare-sort vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. 0)
(declare-datatypes ((vstd!option.Option. 0) (bundle!spec.Messages_t.Value. 0) (bundle!spec.Messages_t.Delta.
   0
  ) (bundle!spec.Messages_t.Message. 0) (bundle!spec.KeyType_t.Key. 0) (bundle!coordination_layer.MsgHistory_v.KeyedMessage.
   0
  ) (bundle!coordination_layer.MsgHistory_v.MsgHistory. 0) (bundle!journal.PagedJournal_v.JournalRecord.
   0
  ) (bundle!journal.LinkedJournal_v.JournalRecord. 0) (bundle!journal.LinkedJournal_v.DiskView.
   0
  ) (bundle!journal.LinkedJournal_v.TruncatedJournal. 0) (bundle!disk.GenericDisk_v.Address.
   0
  ) (tuple%0. 0)
 ) (((vstd!option.Option./None) (vstd!option.Option./Some (vstd!option.Option./Some/?_0
     Poly
   ))
  ) ((bundle!spec.Messages_t.Value./Value (bundle!spec.Messages_t.Value./Value/?_0 Int)))
  ((bundle!spec.Messages_t.Delta./Delta (bundle!spec.Messages_t.Delta./Delta/?_0 Int)))
  ((bundle!spec.Messages_t.Message./Define (bundle!spec.Messages_t.Message./Define/?value
     bundle!spec.Messages_t.Value.
    )
   ) (bundle!spec.Messages_t.Message./Update (bundle!spec.Messages_t.Message./Update/?delta
     bundle!spec.Messages_t.Delta.
   ))
  ) ((bundle!spec.KeyType_t.Key./Key (bundle!spec.KeyType_t.Key./Key/?_0 Int))) ((bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage
    (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/?key bundle!spec.KeyType_t.Key.)
    (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/?message bundle!spec.Messages_t.Message.)
   )
  ) ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?msgs
     vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
    ) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?seq_start Int)
    (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?seq_end Int)
   )
  ) ((bundle!journal.PagedJournal_v.JournalRecord./JournalRecord (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/?message_seq
     bundle!coordination_layer.MsgHistory_v.MsgHistory.
    ) (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/?prior_rec vstd!option.Option.)
   )
  ) ((bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/?message_seq
     bundle!coordination_layer.MsgHistory_v.MsgHistory.
    ) (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/?prior_rec vstd!option.Option.)
   )
  ) ((bundle!journal.LinkedJournal_v.DiskView./DiskView (bundle!journal.LinkedJournal_v.DiskView./DiskView/?boundary_lsn
     Int
    ) (bundle!journal.LinkedJournal_v.DiskView./DiskView/?entries vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
   )
  ) ((bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/?freshest_rec
     vstd!option.Option.
    ) (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/?disk_view bundle!journal.LinkedJournal_v.DiskView.)
   )
  ) ((bundle!disk.GenericDisk_v.Address./Address (bundle!disk.GenericDisk_v.Address./Address/?au
     Int
    ) (bundle!disk.GenericDisk_v.Address./Address/?page Int)
   )
  ) ((tuple%0./tuple%0))
))
(declare-fun vstd!option.Option./Some/_0 (vstd!option.Option.) Poly)
(declare-fun bundle!spec.Messages_t.Value./Value/_0 (bundle!spec.Messages_t.Value.)
 Int
)
(declare-fun bundle!spec.Messages_t.Delta./Delta/_0 (bundle!spec.Messages_t.Delta.)
 Int
)
(declare-fun bundle!spec.Messages_t.Message./Define/value (bundle!spec.Messages_t.Message.)
 bundle!spec.Messages_t.Value.
)
(declare-fun bundle!spec.Messages_t.Message./Update/delta (bundle!spec.Messages_t.Message.)
 bundle!spec.Messages_t.Delta.
)
(declare-fun bundle!spec.KeyType_t.Key./Key/_0 (bundle!spec.KeyType_t.Key.) Int)
(declare-fun bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key
 (bundle!coordination_layer.MsgHistory_v.KeyedMessage.) bundle!spec.KeyType_t.Key.
)
(declare-fun bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message
 (bundle!coordination_layer.MsgHistory_v.KeyedMessage.) bundle!spec.Messages_t.Message.
)
(declare-fun bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs (bundle!coordination_layer.MsgHistory_v.MsgHistory.)
 vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
)
(declare-fun bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
 (bundle!coordination_layer.MsgHistory_v.MsgHistory.) Int
)
(declare-fun bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end
 (bundle!coordination_layer.MsgHistory_v.MsgHistory.) Int
)
(declare-fun bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq
 (bundle!journal.PagedJournal_v.JournalRecord.) bundle!coordination_layer.MsgHistory_v.MsgHistory.
)
(declare-fun bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec
 (bundle!journal.PagedJournal_v.JournalRecord.) vstd!option.Option.
)
(declare-fun bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
 (bundle!journal.LinkedJournal_v.JournalRecord.) bundle!coordination_layer.MsgHistory_v.MsgHistory.
)
(declare-fun bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec
 (bundle!journal.LinkedJournal_v.JournalRecord.) vstd!option.Option.
)
(declare-fun bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (bundle!journal.LinkedJournal_v.DiskView.)
 Int
)
(declare-fun bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (bundle!journal.LinkedJournal_v.DiskView.)
 vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
)
(declare-fun bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
 (bundle!journal.LinkedJournal_v.TruncatedJournal.) vstd!option.Option.
)
(declare-fun bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
 (bundle!journal.LinkedJournal_v.TruncatedJournal.) bundle!journal.LinkedJournal_v.DiskView.
)
(declare-fun bundle!disk.GenericDisk_v.Address./Address/au (bundle!disk.GenericDisk_v.Address.)
 Int
)
(declare-fun bundle!disk.GenericDisk_v.Address./Address/page (bundle!disk.GenericDisk_v.Address.)
 Int
)
(declare-fun TYPE%fun%1. (Type Type) Type)
(declare-fun TYPE%vstd!map.Map. (Type Type) Type)
(declare-fun TYPE%vstd!option.Option. (Type) Type)
(declare-fun TYPE%vstd!set.Set. (Type) Type)
(declare-const TYPE%bundle!spec.Messages_t.Value. Type)
(declare-const TYPE%bundle!spec.Messages_t.Delta. Type)
(declare-const TYPE%bundle!spec.Messages_t.Message. Type)
(declare-const TYPE%bundle!spec.KeyType_t.Key. Type)
(declare-const TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage. Type)
(declare-const TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory. Type)
(declare-const TYPE%bundle!journal.PagedJournal_v.JournalRecord. Type)
(declare-const TYPE%bundle!journal.LinkedJournal_v.JournalRecord. Type)
(declare-const TYPE%bundle!journal.LinkedJournal_v.DiskView. Type)
(declare-const TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal. Type)
(declare-const TYPE%bundle!disk.GenericDisk_v.Address. Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
 (vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.) Poly
)
(declare-fun %Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
 (Poly) vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
)
(declare-fun Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.)
 Poly
)
(declare-fun %Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (Poly) vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.)
(declare-fun Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
 (vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
 Poly
)
(declare-fun %Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
 (Poly) vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
)
(declare-fun Poly%vstd!set.Set<nat.>. (vstd!set.Set<nat.>.) Poly)
(declare-fun %Poly%vstd!set.Set<nat.>. (Poly) vstd!set.Set<nat.>.)
(declare-fun Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)
 Poly
)
(declare-fun %Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (Poly) vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)
(declare-fun Poly%vstd!option.Option. (vstd!option.Option.) Poly)
(declare-fun %Poly%vstd!option.Option. (Poly) vstd!option.Option.)
(declare-fun Poly%bundle!spec.Messages_t.Value. (bundle!spec.Messages_t.Value.) Poly)
(declare-fun %Poly%bundle!spec.Messages_t.Value. (Poly) bundle!spec.Messages_t.Value.)
(declare-fun Poly%bundle!spec.Messages_t.Delta. (bundle!spec.Messages_t.Delta.) Poly)
(declare-fun %Poly%bundle!spec.Messages_t.Delta. (Poly) bundle!spec.Messages_t.Delta.)
(declare-fun Poly%bundle!spec.Messages_t.Message. (bundle!spec.Messages_t.Message.)
 Poly
)
(declare-fun %Poly%bundle!spec.Messages_t.Message. (Poly) bundle!spec.Messages_t.Message.)
(declare-fun Poly%bundle!spec.KeyType_t.Key. (bundle!spec.KeyType_t.Key.) Poly)
(declare-fun %Poly%bundle!spec.KeyType_t.Key. (Poly) bundle!spec.KeyType_t.Key.)
(declare-fun Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
 Poly
)
(declare-fun %Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (Poly) bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
(declare-fun Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!coordination_layer.MsgHistory_v.MsgHistory.)
 Poly
)
(declare-fun %Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly) bundle!coordination_layer.MsgHistory_v.MsgHistory.)
(declare-fun Poly%bundle!journal.PagedJournal_v.JournalRecord. (bundle!journal.PagedJournal_v.JournalRecord.)
 Poly
)
(declare-fun %Poly%bundle!journal.PagedJournal_v.JournalRecord. (Poly) bundle!journal.PagedJournal_v.JournalRecord.)
(declare-fun Poly%bundle!journal.LinkedJournal_v.JournalRecord. (bundle!journal.LinkedJournal_v.JournalRecord.)
 Poly
)
(declare-fun %Poly%bundle!journal.LinkedJournal_v.JournalRecord. (Poly) bundle!journal.LinkedJournal_v.JournalRecord.)
(declare-fun Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.DiskView.)
 Poly
)
(declare-fun %Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly) bundle!journal.LinkedJournal_v.DiskView.)
(declare-fun Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.TruncatedJournal.)
 Poly
)
(declare-fun %Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (Poly) bundle!journal.LinkedJournal_v.TruncatedJournal.)
(declare-fun Poly%bundle!disk.GenericDisk_v.Address. (bundle!disk.GenericDisk_v.Address.)
 Poly
)
(declare-fun %Poly%bundle!disk.GenericDisk_v.Address. (Poly) bundle!disk.GenericDisk_v.Address.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ %%Function%%)) (!
   (= x@ (%Poly%fun%1. (Poly%fun%1. x@)))
   :pattern ((Poly%fun%1. x@))
   :qid
   internal_crate__fun__1_box_axiom_definition
   :skolemid
   skolem_internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%fun%1. T%0& T%1&))
    (= x@ (Poly%fun%1. (%Poly%fun%1. x@)))
   )
   :pattern ((has_type x@ (TYPE%fun%1. T%0& T%1&)))
   :qid
   internal_crate__fun__1_unbox_axiom_definition
   :skolemid
   skolem_internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0& Type) (T%1& Type) (x@ %%Function%%)) (!
   (=>
    (forall ((T%0@ Poly)) (!
      (=>
       (has_type T%0@ T%0&)
       (has_type (%%apply%%0 x@ T%0@) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x@ T%0@) T%1&))
      :qid
      internal_crate__fun__1_constructor_inner_definition
      :skolemid
      skolem_internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x@)) (TYPE%fun%1. T%0& T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x@)) (TYPE%fun%1. T%0& T%1&)))
   :qid
   internal_crate__fun__1_constructor_definition
   :skolemid
   skolem_internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0& Type) (T%1& Type) (T%0@ Poly) (x@ %%Function%%)) (!
   (=>
    (and
     (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0& T%1&))
     (has_type T%0@ T%0&)
    )
    (has_type (%%apply%%0 x@ T%0@) T%1&)
   )
   :pattern ((%%apply%%0 x@ T%0@) (has_type (Poly%fun%1. x@) (TYPE%fun%1. T%0& T%1&)))
   :qid
   internal_crate__fun__1_apply_definition
   :skolemid
   skolem_internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0& Type) (T%0&. Type) (T%1& Type) (T%1&. Type) (deep@ Bool) (x@ Poly) (
    y@ Poly
   )
  ) (!
   (=>
    (and
     (has_type x@ (TYPE%fun%1. T%0& T%1&))
     (has_type y@ (TYPE%fun%1. T%0& T%1&))
     (forall ((T%0@ Poly)) (!
       (=>
        (has_type T%0@ T%0&)
        (ext_eq deep@ T%1& T%1&. (%%apply%%0 (%Poly%fun%1. x@) T%0@) (%%apply%%0 (%Poly%fun%1.
           y@
          ) T%0@
       )))
       :pattern ((ext_eq deep@ T%1& T%1&. (%%apply%%0 (%Poly%fun%1. x@) T%0@) (%%apply%%0 (
           %Poly%fun%1. y@
          ) T%0@
       )))
       :qid
       internal_crate__fun__1_inner_ext_equal_definition
       :skolemid
       skolem_internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep@ (TYPE%fun%1. T%0& T%1&) (TYPE%fun%1. T%0&. T%1&.) x@ y@)
   )
   :pattern ((ext_eq deep@ (TYPE%fun%1. T%0& T%1&) (TYPE%fun%1. T%0&. T%1&.) x@ y@))
   :qid
   internal_crate__fun__1_ext_equal_definition
   :skolemid
   skolem_internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x@ vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.))
  (!
   (= x@ (%Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
     (Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>. x@)
   ))
   :pattern ((Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
     x@
   ))
   :qid
   internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!map.Map. NAT TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.))
    (= x@ (Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
      (%Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>. x@)
   )))
   :pattern ((has_type x@ (TYPE%vstd!map.Map. NAT TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)))
   :qid
   internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.))
  (!
   (has_type (Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
     x@
    ) (TYPE%vstd!map.Map. NAT TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
   )
   :pattern ((has_type (Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.
      x@
     ) (TYPE%vstd!map.Map. NAT TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
   ))
   :qid
   internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__map__Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.)) (!
   (= x@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.
      x@
   )))
   :pattern ((Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. x@))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT))
    (= x@ (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.
       x@
   ))))
   :pattern ((has_type x@ (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT)))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.)) (!
   (has_type (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. x@) (TYPE%vstd!map.Map.
     TYPE%bundle!disk.GenericDisk_v.Address. NAT
   ))
   :pattern ((has_type (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. x@)
     (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT)
   ))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./nat.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.))
  (!
   (= x@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
      x@
   )))
   :pattern ((Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
     x@
   ))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.))
    (= x@ (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
      (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
       x@
   ))))
   :pattern ((has_type x@ (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.))
  (!
   (has_type (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
     x@
    ) (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
   )
   :pattern ((has_type (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
      x@
     ) (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
   ))
   :qid
   internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__map__Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!set.Set<nat.>.)) (!
   (= x@ (%Poly%vstd!set.Set<nat.>. (Poly%vstd!set.Set<nat.>. x@)))
   :pattern ((Poly%vstd!set.Set<nat.>. x@))
   :qid
   internal_vstd__set__Set<nat.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__set__Set<nat.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!set.Set. NAT))
    (= x@ (Poly%vstd!set.Set<nat.>. (%Poly%vstd!set.Set<nat.>. x@)))
   )
   :pattern ((has_type x@ (TYPE%vstd!set.Set. NAT)))
   :qid
   internal_vstd__set__Set<nat.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__set__Set<nat.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!set.Set<nat.>.)) (!
   (has_type (Poly%vstd!set.Set<nat.>. x@) (TYPE%vstd!set.Set. NAT))
   :pattern ((has_type (Poly%vstd!set.Set<nat.>. x@) (TYPE%vstd!set.Set. NAT)))
   :qid
   internal_vstd__set__Set<nat.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__set__Set<nat.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)) (!
   (= x@ (%Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.
      x@
   )))
   :pattern ((Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. x@))
   :qid
   internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_box_axiom_definition
   :skolemid
   skolem_internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!set.Set. TYPE%bundle!disk.GenericDisk_v.Address.))
    (= x@ (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (%Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.
       x@
   ))))
   :pattern ((has_type x@ (TYPE%vstd!set.Set. TYPE%bundle!disk.GenericDisk_v.Address.)))
   :qid
   internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_unbox_axiom_definition
)))
(assert
 (forall ((x@ vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)) (!
   (has_type (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. x@) (TYPE%vstd!set.Set.
     TYPE%bundle!disk.GenericDisk_v.Address.
   ))
   :pattern ((has_type (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. x@) (TYPE%vstd!set.Set.
      TYPE%bundle!disk.GenericDisk_v.Address.
   )))
   :qid
   internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_has_type_always_definition
   :skolemid
   skolem_internal_vstd__set__Set<bundle!disk.GenericDisk_v.Address.>_has_type_always_definition
)))
(assert
 (forall ((x@ vstd!option.Option.)) (!
   (= x@ (%Poly%vstd!option.Option. (Poly%vstd!option.Option. x@)))
   :pattern ((Poly%vstd!option.Option. x@))
   :qid
   internal_vstd__option__Option_box_axiom_definition
   :skolemid
   skolem_internal_vstd__option__Option_box_axiom_definition
)))
(assert
 (forall ((A& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!option.Option. A&))
    (= x@ (Poly%vstd!option.Option. (%Poly%vstd!option.Option. x@)))
   )
   :pattern ((has_type x@ (TYPE%vstd!option.Option. A&)))
   :qid
   internal_vstd__option__Option_unbox_axiom_definition
   :skolemid
   skolem_internal_vstd__option__Option_unbox_axiom_definition
)))
(assert
 (forall ((A& Type)) (!
   (has_type (Poly%vstd!option.Option. vstd!option.Option./None) (TYPE%vstd!option.Option.
     A&
   ))
   :pattern ((has_type (Poly%vstd!option.Option. vstd!option.Option./None) (TYPE%vstd!option.Option.
      A&
   )))
   :qid
   internal_vstd!option.Option./None_constructor_definition
   :skolemid
   skolem_internal_vstd!option.Option./None_constructor_definition
)))
(assert
 (forall ((A& Type) (_0@ Poly)) (!
   (=>
    (has_type _0@ A&)
    (has_type (Poly%vstd!option.Option. (vstd!option.Option./Some _0@)) (TYPE%vstd!option.Option.
      A&
   )))
   :pattern ((has_type (Poly%vstd!option.Option. (vstd!option.Option./Some _0@)) (TYPE%vstd!option.Option.
      A&
   )))
   :qid
   internal_vstd!option.Option./Some_constructor_definition
   :skolemid
   skolem_internal_vstd!option.Option./Some_constructor_definition
)))
(assert
 (forall ((x@ vstd!option.Option.)) (!
   (= (vstd!option.Option./Some/_0 x@) (vstd!option.Option./Some/?_0 x@))
   :pattern ((vstd!option.Option./Some/_0 x@))
   :qid
   internal_vstd!option.Option./Some/_0_accessor_definition
   :skolemid
   skolem_internal_vstd!option.Option./Some/_0_accessor_definition
)))
(assert
 (forall ((A& Type) (x@ Poly)) (!
   (=>
    (has_type x@ (TYPE%vstd!option.Option. A&))
    (has_type (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. x@)) A&)
   )
   :pattern ((vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. x@)) (has_type x@
     (TYPE%vstd!option.Option. A&)
   ))
   :qid
   internal_vstd!option.Option./Some/_0_invariant_definition
   :skolemid
   skolem_internal_vstd!option.Option./Some/_0_invariant_definition
)))
(assert
 (forall ((x vstd!option.Option.)) (!
   (=>
    (is-vstd!option.Option./Some x)
    (< (height (vstd!option.Option./Some/_0 x)) (height (Poly%vstd!option.Option. x)))
   )
   :pattern ((height (vstd!option.Option./Some/_0 x)))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((A& Type) (A&. Type) (deep@ Bool) (x@ Poly) (y@ Poly)) (!
   (=>
    (and
     (has_type x@ (TYPE%vstd!option.Option. A&))
     (has_type y@ (TYPE%vstd!option.Option. A&))
     (is-vstd!option.Option./None (%Poly%vstd!option.Option. x@))
     (is-vstd!option.Option./None (%Poly%vstd!option.Option. y@))
    )
    (ext_eq deep@ (TYPE%vstd!option.Option. A&) (TYPE%vstd!option.Option. A&.) x@ y@)
   )
   :pattern ((ext_eq deep@ (TYPE%vstd!option.Option. A&) (TYPE%vstd!option.Option. A&.)
     x@ y@
   ))
   :qid
   internal_vstd!option.Option./None_ext_equal_definition
   :skolemid
   skolem_internal_vstd!option.Option./None_ext_equal_definition
)))
(assert
 (forall ((A& Type) (A&. Type) (deep@ Bool) (x@ Poly) (y@ Poly)) (!
   (=>
    (and
     (has_type x@ (TYPE%vstd!option.Option. A&))
     (has_type y@ (TYPE%vstd!option.Option. A&))
     (is-vstd!option.Option./Some (%Poly%vstd!option.Option. x@))
     (is-vstd!option.Option./Some (%Poly%vstd!option.Option. y@))
     (ext_eq deep@ A& A&. (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. x@))
      (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. y@))
    ))
    (ext_eq deep@ (TYPE%vstd!option.Option. A&) (TYPE%vstd!option.Option. A&.) x@ y@)
   )
   :pattern ((ext_eq deep@ (TYPE%vstd!option.Option. A&) (TYPE%vstd!option.Option. A&.)
     x@ y@
   ))
   :qid
   internal_vstd!option.Option./Some_ext_equal_definition
   :skolemid
   skolem_internal_vstd!option.Option./Some_ext_equal_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Value.)) (!
   (= x@ (%Poly%bundle!spec.Messages_t.Value. (Poly%bundle!spec.Messages_t.Value. x@)))
   :pattern ((Poly%bundle!spec.Messages_t.Value. x@))
   :qid
   internal_bundle__spec__Messages_t__Value_box_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Value_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!spec.Messages_t.Value.)
    (= x@ (Poly%bundle!spec.Messages_t.Value. (%Poly%bundle!spec.Messages_t.Value. x@)))
   )
   :pattern ((has_type x@ TYPE%bundle!spec.Messages_t.Value.))
   :qid
   internal_bundle__spec__Messages_t__Value_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Value_unbox_axiom_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Value.)) (!
   (= (bundle!spec.Messages_t.Value./Value/_0 x@) (bundle!spec.Messages_t.Value./Value/?_0
     x@
   ))
   :pattern ((bundle!spec.Messages_t.Value./Value/_0 x@))
   :qid
   internal_bundle!spec.Messages_t.Value./Value/_0_accessor_definition
   :skolemid
   skolem_internal_bundle!spec.Messages_t.Value./Value/_0_accessor_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Value.)) (!
   (has_type (Poly%bundle!spec.Messages_t.Value. x@) TYPE%bundle!spec.Messages_t.Value.)
   :pattern ((has_type (Poly%bundle!spec.Messages_t.Value. x@) TYPE%bundle!spec.Messages_t.Value.))
   :qid
   internal_bundle__spec__Messages_t__Value_has_type_always_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Value_has_type_always_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Delta.)) (!
   (= x@ (%Poly%bundle!spec.Messages_t.Delta. (Poly%bundle!spec.Messages_t.Delta. x@)))
   :pattern ((Poly%bundle!spec.Messages_t.Delta. x@))
   :qid
   internal_bundle__spec__Messages_t__Delta_box_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Delta_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!spec.Messages_t.Delta.)
    (= x@ (Poly%bundle!spec.Messages_t.Delta. (%Poly%bundle!spec.Messages_t.Delta. x@)))
   )
   :pattern ((has_type x@ TYPE%bundle!spec.Messages_t.Delta.))
   :qid
   internal_bundle__spec__Messages_t__Delta_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Delta_unbox_axiom_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Delta.)) (!
   (= (bundle!spec.Messages_t.Delta./Delta/_0 x@) (bundle!spec.Messages_t.Delta./Delta/?_0
     x@
   ))
   :pattern ((bundle!spec.Messages_t.Delta./Delta/_0 x@))
   :qid
   internal_bundle!spec.Messages_t.Delta./Delta/_0_accessor_definition
   :skolemid
   skolem_internal_bundle!spec.Messages_t.Delta./Delta/_0_accessor_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Delta.)) (!
   (has_type (Poly%bundle!spec.Messages_t.Delta. x@) TYPE%bundle!spec.Messages_t.Delta.)
   :pattern ((has_type (Poly%bundle!spec.Messages_t.Delta. x@) TYPE%bundle!spec.Messages_t.Delta.))
   :qid
   internal_bundle__spec__Messages_t__Delta_has_type_always_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Delta_has_type_always_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Message.)) (!
   (= x@ (%Poly%bundle!spec.Messages_t.Message. (Poly%bundle!spec.Messages_t.Message. x@)))
   :pattern ((Poly%bundle!spec.Messages_t.Message. x@))
   :qid
   internal_bundle__spec__Messages_t__Message_box_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Message_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!spec.Messages_t.Message.)
    (= x@ (Poly%bundle!spec.Messages_t.Message. (%Poly%bundle!spec.Messages_t.Message. x@)))
   )
   :pattern ((has_type x@ TYPE%bundle!spec.Messages_t.Message.))
   :qid
   internal_bundle__spec__Messages_t__Message_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Message_unbox_axiom_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Message.)) (!
   (= (bundle!spec.Messages_t.Message./Define/value x@) (bundle!spec.Messages_t.Message./Define/?value
     x@
   ))
   :pattern ((bundle!spec.Messages_t.Message./Define/value x@))
   :qid
   internal_bundle!spec.Messages_t.Message./Define/value_accessor_definition
   :skolemid
   skolem_internal_bundle!spec.Messages_t.Message./Define/value_accessor_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Message.)) (!
   (= (bundle!spec.Messages_t.Message./Update/delta x@) (bundle!spec.Messages_t.Message./Update/?delta
     x@
   ))
   :pattern ((bundle!spec.Messages_t.Message./Update/delta x@))
   :qid
   internal_bundle!spec.Messages_t.Message./Update/delta_accessor_definition
   :skolemid
   skolem_internal_bundle!spec.Messages_t.Message./Update/delta_accessor_definition
)))
(assert
 (forall ((x@ bundle!spec.Messages_t.Message.)) (!
   (has_type (Poly%bundle!spec.Messages_t.Message. x@) TYPE%bundle!spec.Messages_t.Message.)
   :pattern ((has_type (Poly%bundle!spec.Messages_t.Message. x@) TYPE%bundle!spec.Messages_t.Message.))
   :qid
   internal_bundle__spec__Messages_t__Message_has_type_always_definition
   :skolemid
   skolem_internal_bundle__spec__Messages_t__Message_has_type_always_definition
)))
(assert
 (forall ((x bundle!spec.Messages_t.Message.)) (!
   (=>
    (is-bundle!spec.Messages_t.Message./Define x)
    (< (height (Poly%bundle!spec.Messages_t.Value. (bundle!spec.Messages_t.Message./Define/value
        x
      ))
     ) (height (Poly%bundle!spec.Messages_t.Message. x))
   ))
   :pattern ((height (Poly%bundle!spec.Messages_t.Value. (bundle!spec.Messages_t.Message./Define/value
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x bundle!spec.Messages_t.Message.)) (!
   (=>
    (is-bundle!spec.Messages_t.Message./Update x)
    (< (height (Poly%bundle!spec.Messages_t.Delta. (bundle!spec.Messages_t.Message./Update/delta
        x
      ))
     ) (height (Poly%bundle!spec.Messages_t.Message. x))
   ))
   :pattern ((height (Poly%bundle!spec.Messages_t.Delta. (bundle!spec.Messages_t.Message./Update/delta
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x@ bundle!spec.KeyType_t.Key.)) (!
   (= x@ (%Poly%bundle!spec.KeyType_t.Key. (Poly%bundle!spec.KeyType_t.Key. x@)))
   :pattern ((Poly%bundle!spec.KeyType_t.Key. x@))
   :qid
   internal_bundle__spec__KeyType_t__Key_box_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__KeyType_t__Key_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!spec.KeyType_t.Key.)
    (= x@ (Poly%bundle!spec.KeyType_t.Key. (%Poly%bundle!spec.KeyType_t.Key. x@)))
   )
   :pattern ((has_type x@ TYPE%bundle!spec.KeyType_t.Key.))
   :qid
   internal_bundle__spec__KeyType_t__Key_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__spec__KeyType_t__Key_unbox_axiom_definition
)))
(assert
 (forall ((_0@ Int)) (!
   (=>
    (<= 0 _0@)
    (has_type (Poly%bundle!spec.KeyType_t.Key. (bundle!spec.KeyType_t.Key./Key _0@)) TYPE%bundle!spec.KeyType_t.Key.)
   )
   :pattern ((has_type (Poly%bundle!spec.KeyType_t.Key. (bundle!spec.KeyType_t.Key./Key
       _0@
      )
     ) TYPE%bundle!spec.KeyType_t.Key.
   ))
   :qid
   internal_bundle!spec.KeyType_t.Key./Key_constructor_definition
   :skolemid
   skolem_internal_bundle!spec.KeyType_t.Key./Key_constructor_definition
)))
(assert
 (forall ((x@ bundle!spec.KeyType_t.Key.)) (!
   (= (bundle!spec.KeyType_t.Key./Key/_0 x@) (bundle!spec.KeyType_t.Key./Key/?_0 x@))
   :pattern ((bundle!spec.KeyType_t.Key./Key/_0 x@))
   :qid
   internal_bundle!spec.KeyType_t.Key./Key/_0_accessor_definition
   :skolemid
   skolem_internal_bundle!spec.KeyType_t.Key./Key/_0_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!spec.KeyType_t.Key.)
    (<= 0 (bundle!spec.KeyType_t.Key./Key/_0 (%Poly%bundle!spec.KeyType_t.Key. x@)))
   )
   :pattern ((bundle!spec.KeyType_t.Key./Key/_0 (%Poly%bundle!spec.KeyType_t.Key. x@))
    (has_type x@ TYPE%bundle!spec.KeyType_t.Key.)
   )
   :qid
   internal_bundle!spec.KeyType_t.Key./Key/_0_invariant_definition
   :skolemid
   skolem_internal_bundle!spec.KeyType_t.Key./Key/_0_invariant_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.KeyedMessage.)) (!
   (= x@ (%Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
      x@
   )))
   :pattern ((Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. x@))
   :qid
   internal_bundle__coordination_layer__MsgHistory_v__KeyedMessage_box_axiom_definition
   :skolemid
   skolem_internal_bundle__coordination_layer__MsgHistory_v__KeyedMessage_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
    (= x@ (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (%Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.))
   :qid
   internal_bundle__coordination_layer__MsgHistory_v__KeyedMessage_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__coordination_layer__MsgHistory_v__KeyedMessage_unbox_axiom_definition
)))
(assert
 (forall ((key@ bundle!spec.KeyType_t.Key.) (message@ bundle!spec.Messages_t.Message.))
  (!
   (=>
    (has_type (Poly%bundle!spec.KeyType_t.Key. key@) TYPE%bundle!spec.KeyType_t.Key.)
    (has_type (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage
       key@ message@
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
   ))
   :pattern ((has_type (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage
       key@ message@
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
   ))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage_constructor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage_constructor_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.KeyedMessage.)) (!
   (= (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key x@) (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/?key
     x@
   ))
   :pattern ((bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key x@))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key_accessor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
    (has_type (Poly%bundle!spec.KeyType_t.Key. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key
       (%Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. x@)
      )
     ) TYPE%bundle!spec.KeyType_t.Key.
   ))
   :pattern ((bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key (%Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
      x@
     )
    ) (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.)
   )
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key_invariant_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key_invariant_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.KeyedMessage.)) (!
   (= (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message x@)
    (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/?message x@)
   )
   :pattern ((bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message
     x@
   ))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message_accessor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message_accessor_definition
)))
(assert
 (forall ((x bundle!coordination_layer.MsgHistory_v.KeyedMessage.)) (!
   (=>
    (is-bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage x)
    (< (height (Poly%bundle!spec.KeyType_t.Key. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key
        x
      ))
     ) (height (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. x))
   ))
   :pattern ((height (Poly%bundle!spec.KeyType_t.Key. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/key
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x bundle!coordination_layer.MsgHistory_v.KeyedMessage.)) (!
   (=>
    (is-bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage x)
    (< (height (Poly%bundle!spec.Messages_t.Message. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message
        x
      ))
     ) (height (Poly%bundle!coordination_layer.MsgHistory_v.KeyedMessage. x))
   ))
   :pattern ((height (Poly%bundle!spec.Messages_t.Message. (bundle!coordination_layer.MsgHistory_v.KeyedMessage./KeyedMessage/message
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.MsgHistory.)) (!
   (= x@ (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
      x@
   )))
   :pattern ((Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. x@))
   :qid
   internal_bundle__coordination_layer__MsgHistory_v__MsgHistory_box_axiom_definition
   :skolemid
   skolem_internal_bundle__coordination_layer__MsgHistory_v__MsgHistory_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
    (= x@ (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.))
   :qid
   internal_bundle__coordination_layer__MsgHistory_v__MsgHistory_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__coordination_layer__MsgHistory_v__MsgHistory_unbox_axiom_definition
)))
(assert
 (forall ((msgs@ vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>.)
   (seq_start@ Int) (seq_end@ Int)
  ) (!
   (=>
    (and
     (<= 0 seq_start@)
     (<= 0 seq_end@)
    )
    (has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory
       msgs@ seq_start@ seq_end@
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.
   ))
   :pattern ((has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory
       msgs@ seq_start@ seq_end@
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.
   ))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory_constructor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory_constructor_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.MsgHistory.)) (!
   (= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs x@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?msgs
     x@
   ))
   :pattern ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs x@))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs_accessor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs_accessor_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.MsgHistory.)) (!
   (= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start x@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?seq_start
     x@
   ))
   :pattern ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
     x@
   ))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start_accessor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
    (<= 0 (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
       x@
   ))))
   :pattern ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
     (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. x@)
    ) (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
   )
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start_invariant_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start_invariant_definition
)))
(assert
 (forall ((x@ bundle!coordination_layer.MsgHistory_v.MsgHistory.)) (!
   (= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end x@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/?seq_end
     x@
   ))
   :pattern ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end x@))
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end_accessor_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
    (<= 0 (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
       x@
   ))))
   :pattern ((bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
      x@
     )
    ) (has_type x@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
   )
   :qid
   internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end_invariant_definition
   :skolemid
   skolem_internal_bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end_invariant_definition
)))
(assert
 (forall ((x@ bundle!journal.PagedJournal_v.JournalRecord.)) (!
   (= x@ (%Poly%bundle!journal.PagedJournal_v.JournalRecord. (Poly%bundle!journal.PagedJournal_v.JournalRecord.
      x@
   )))
   :pattern ((Poly%bundle!journal.PagedJournal_v.JournalRecord. x@))
   :qid
   internal_bundle__journal__PagedJournal_v__JournalRecord_box_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__PagedJournal_v__JournalRecord_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
    (= x@ (Poly%bundle!journal.PagedJournal_v.JournalRecord. (%Poly%bundle!journal.PagedJournal_v.JournalRecord.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.))
   :qid
   internal_bundle__journal__PagedJournal_v__JournalRecord_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__PagedJournal_v__JournalRecord_unbox_axiom_definition
)))
(assert
 (forall ((message_seq@ bundle!coordination_layer.MsgHistory_v.MsgHistory.) (prior_rec@
    vstd!option.Option.
   )
  ) (!
   (=>
    (and
     (has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. message_seq@) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
     (has_type (Poly%vstd!option.Option. prior_rec@) (TYPE%vstd!option.Option. TYPE%bundle!journal.PagedJournal_v.JournalRecord.))
    )
    (has_type (Poly%bundle!journal.PagedJournal_v.JournalRecord. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord
       message_seq@ prior_rec@
      )
     ) TYPE%bundle!journal.PagedJournal_v.JournalRecord.
   ))
   :pattern ((has_type (Poly%bundle!journal.PagedJournal_v.JournalRecord. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord
       message_seq@ prior_rec@
      )
     ) TYPE%bundle!journal.PagedJournal_v.JournalRecord.
   ))
   :qid
   internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord_constructor_definition
   :skolemid
   skolem_internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord_constructor_definition
)))
(assert
 (forall ((x@ bundle!journal.PagedJournal_v.JournalRecord.)) (!
   (= (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq x@) (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/?message_seq
     x@
   ))
   :pattern ((bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq x@))
   :qid
   internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
    (has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq
       (%Poly%bundle!journal.PagedJournal_v.JournalRecord. x@)
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.
   ))
   :pattern ((bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq (
      %Poly%bundle!journal.PagedJournal_v.JournalRecord. x@
     )
    ) (has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
   )
   :qid
   internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq_invariant_definition
)))
(assert
 (forall ((x@ bundle!journal.PagedJournal_v.JournalRecord.)) (!
   (= (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec x@) (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/?prior_rec
     x@
   ))
   :pattern ((bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec x@))
   :qid
   internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
    (has_type (Poly%vstd!option.Option. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec
       (%Poly%bundle!journal.PagedJournal_v.JournalRecord. x@)
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
   ))
   :pattern ((bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec (%Poly%bundle!journal.PagedJournal_v.JournalRecord.
      x@
     )
    ) (has_type x@ TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
   )
   :qid
   internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec_invariant_definition
)))
(assert
 (forall ((x bundle!journal.PagedJournal_v.JournalRecord.)) (!
   (=>
    (is-bundle!journal.PagedJournal_v.JournalRecord./JournalRecord x)
    (< (height (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq
        x
      ))
     ) (height (Poly%bundle!journal.PagedJournal_v.JournalRecord. x))
   ))
   :pattern ((height (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/message_seq
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x bundle!journal.PagedJournal_v.JournalRecord.)) (!
   (=>
    (is-bundle!journal.PagedJournal_v.JournalRecord./JournalRecord x)
    (< (height (Poly%vstd!option.Option. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec
        x
      ))
     ) (height (Poly%bundle!journal.PagedJournal_v.JournalRecord. x))
   ))
   :pattern ((height (Poly%vstd!option.Option. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord/prior_rec
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.JournalRecord.)) (!
   (= x@ (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%bundle!journal.LinkedJournal_v.JournalRecord.
      x@
   )))
   :pattern ((Poly%bundle!journal.LinkedJournal_v.JournalRecord. x@))
   :qid
   internal_bundle__journal__LinkedJournal_v__JournalRecord_box_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__JournalRecord_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
    (= x@ (Poly%bundle!journal.LinkedJournal_v.JournalRecord. (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.))
   :qid
   internal_bundle__journal__LinkedJournal_v__JournalRecord_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__JournalRecord_unbox_axiom_definition
)))
(assert
 (forall ((message_seq@ bundle!coordination_layer.MsgHistory_v.MsgHistory.) (prior_rec@
    vstd!option.Option.
   )
  ) (!
   (=>
    (and
     (has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. message_seq@) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
     (has_type (Poly%vstd!option.Option. prior_rec@) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.JournalRecord. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord
       message_seq@ prior_rec@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
   ))
   :pattern ((has_type (Poly%bundle!journal.LinkedJournal_v.JournalRecord. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord
       message_seq@ prior_rec@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord_constructor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord_constructor_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.JournalRecord.)) (!
   (= (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq x@) (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/?message_seq
     x@
   ))
   :pattern ((bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
     x@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
    (has_type (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
       (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. x@)
      )
     ) TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
     (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. x@)
    ) (has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
   )
   :qid
   internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq_invariant_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.JournalRecord.)) (!
   (= (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec x@) (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/?prior_rec
     x@
   ))
   :pattern ((bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec x@))
   :qid
   internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec
       (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. x@)
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
      x@
     )
    ) (has_type x@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
   )
   :qid
   internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec_invariant_definition
)))
(assert
 (forall ((x bundle!journal.LinkedJournal_v.JournalRecord.)) (!
   (=>
    (is-bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord x)
    (< (height (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
        x
      ))
     ) (height (Poly%bundle!journal.LinkedJournal_v.JournalRecord. x))
   ))
   :pattern ((height (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x bundle!journal.LinkedJournal_v.JournalRecord.)) (!
   (=>
    (is-bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord x)
    (< (height (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec
        x
      ))
     ) (height (Poly%bundle!journal.LinkedJournal_v.JournalRecord. x))
   ))
   :pattern ((height (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= x@ (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
      x@
   )))
   :pattern ((Poly%bundle!journal.LinkedJournal_v.DiskView. x@))
   :qid
   internal_bundle__journal__LinkedJournal_v__DiskView_box_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__DiskView_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
    (= x@ (Poly%bundle!journal.LinkedJournal_v.DiskView. (%Poly%bundle!journal.LinkedJournal_v.DiskView.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!journal.LinkedJournal_v.DiskView.))
   :qid
   internal_bundle__journal__LinkedJournal_v__DiskView_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__DiskView_unbox_axiom_definition
)))
(assert
 (forall ((boundary_lsn@ Int) (entries@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.))
  (!
   (=>
    (<= 0 boundary_lsn@)
    (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.DiskView./DiskView
       boundary_lsn@ entries@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.DiskView.
   ))
   :pattern ((has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.DiskView./DiskView
       boundary_lsn@ entries@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.DiskView.
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.DiskView./DiskView_constructor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.DiskView./DiskView_constructor_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn x@) (bundle!journal.LinkedJournal_v.DiskView./DiskView/?boundary_lsn
     x@
   ))
   :pattern ((bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn x@))
   :qid
   internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
    (<= 0 (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
       x@
   ))))
   :pattern ((bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
      x@
     )
    ) (has_type x@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
   )
   :qid
   internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn_invariant_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries x@) (bundle!journal.LinkedJournal_v.DiskView./DiskView/?entries
     x@
   ))
   :pattern ((bundle!journal.LinkedJournal_v.DiskView./DiskView/entries x@))
   :qid
   internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/entries_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.DiskView./DiskView/entries_accessor_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (= x@ (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
      x@
   )))
   :pattern ((Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x@))
   :qid
   internal_bundle__journal__LinkedJournal_v__TruncatedJournal_box_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__TruncatedJournal_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (= x@ (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.))
   :qid
   internal_bundle__journal__LinkedJournal_v__TruncatedJournal_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__journal__LinkedJournal_v__TruncatedJournal_unbox_axiom_definition
)))
(assert
 (forall ((freshest_rec@ vstd!option.Option.) (disk_view@ bundle!journal.LinkedJournal_v.DiskView.))
  (!
   (=>
    (and
     (has_type (Poly%vstd!option.Option. freshest_rec@) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
     (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. disk_view@) TYPE%bundle!journal.LinkedJournal_v.DiskView.)
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal
       freshest_rec@ disk_view@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal
       freshest_rec@ disk_view@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal_constructor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal_constructor_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (= (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
     x@
    ) (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/?freshest_rec
     x@
   ))
   :pattern ((bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
     x@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
       (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x@)
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
     (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x@)
    ) (has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
   )
   :qid
   internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec_invariant_definition
)))
(assert
 (forall ((x@ bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (= (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view x@)
    (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/?disk_view x@)
   )
   :pattern ((bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
     x@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view_accessor_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
       (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x@)
      )
     ) TYPE%bundle!journal.LinkedJournal_v.DiskView.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
     (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x@)
    ) (has_type x@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
   )
   :qid
   internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view_invariant_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view_invariant_definition
)))
(assert
 (forall ((x bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (=>
    (is-bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal x)
    (< (height (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
        x
      ))
     ) (height (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x))
   ))
   :pattern ((height (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (=>
    (is-bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal x)
    (< (height (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
        x
      ))
     ) (height (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. x))
   ))
   :pattern ((height (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
       x
   ))))
   :qid
   prelude_datatype_height
   :skolemid
   skolem_prelude_datatype_height
)))
(assert
 (forall ((x@ bundle!disk.GenericDisk_v.Address.)) (!
   (= x@ (%Poly%bundle!disk.GenericDisk_v.Address. (Poly%bundle!disk.GenericDisk_v.Address.
      x@
   )))
   :pattern ((Poly%bundle!disk.GenericDisk_v.Address. x@))
   :qid
   internal_bundle__disk__GenericDisk_v__Address_box_axiom_definition
   :skolemid
   skolem_internal_bundle__disk__GenericDisk_v__Address_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.)
    (= x@ (Poly%bundle!disk.GenericDisk_v.Address. (%Poly%bundle!disk.GenericDisk_v.Address.
       x@
   ))))
   :pattern ((has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.))
   :qid
   internal_bundle__disk__GenericDisk_v__Address_unbox_axiom_definition
   :skolemid
   skolem_internal_bundle__disk__GenericDisk_v__Address_unbox_axiom_definition
)))
(assert
 (forall ((au@ Int) (page@ Int)) (!
   (=>
    (and
     (<= 0 au@)
     (<= 0 page@)
    )
    (has_type (Poly%bundle!disk.GenericDisk_v.Address. (bundle!disk.GenericDisk_v.Address./Address
       au@ page@
      )
     ) TYPE%bundle!disk.GenericDisk_v.Address.
   ))
   :pattern ((has_type (Poly%bundle!disk.GenericDisk_v.Address. (bundle!disk.GenericDisk_v.Address./Address
       au@ page@
      )
     ) TYPE%bundle!disk.GenericDisk_v.Address.
   ))
   :qid
   internal_bundle!disk.GenericDisk_v.Address./Address_constructor_definition
   :skolemid
   skolem_internal_bundle!disk.GenericDisk_v.Address./Address_constructor_definition
)))
(assert
 (forall ((x@ bundle!disk.GenericDisk_v.Address.)) (!
   (= (bundle!disk.GenericDisk_v.Address./Address/au x@) (bundle!disk.GenericDisk_v.Address./Address/?au
     x@
   ))
   :pattern ((bundle!disk.GenericDisk_v.Address./Address/au x@))
   :qid
   internal_bundle!disk.GenericDisk_v.Address./Address/au_accessor_definition
   :skolemid
   skolem_internal_bundle!disk.GenericDisk_v.Address./Address/au_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.)
    (<= 0 (bundle!disk.GenericDisk_v.Address./Address/au (%Poly%bundle!disk.GenericDisk_v.Address.
       x@
   ))))
   :pattern ((bundle!disk.GenericDisk_v.Address./Address/au (%Poly%bundle!disk.GenericDisk_v.Address.
      x@
     )
    ) (has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.)
   )
   :qid
   internal_bundle!disk.GenericDisk_v.Address./Address/au_invariant_definition
   :skolemid
   skolem_internal_bundle!disk.GenericDisk_v.Address./Address/au_invariant_definition
)))
(assert
 (forall ((x@ bundle!disk.GenericDisk_v.Address.)) (!
   (= (bundle!disk.GenericDisk_v.Address./Address/page x@) (bundle!disk.GenericDisk_v.Address./Address/?page
     x@
   ))
   :pattern ((bundle!disk.GenericDisk_v.Address./Address/page x@))
   :qid
   internal_bundle!disk.GenericDisk_v.Address./Address/page_accessor_definition
   :skolemid
   skolem_internal_bundle!disk.GenericDisk_v.Address./Address/page_accessor_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.)
    (<= 0 (bundle!disk.GenericDisk_v.Address./Address/page (%Poly%bundle!disk.GenericDisk_v.Address.
       x@
   ))))
   :pattern ((bundle!disk.GenericDisk_v.Address./Address/page (%Poly%bundle!disk.GenericDisk_v.Address.
      x@
     )
    ) (has_type x@ TYPE%bundle!disk.GenericDisk_v.Address.)
   )
   :qid
   internal_bundle!disk.GenericDisk_v.Address./Address/page_invariant_definition
   :skolemid
   skolem_internal_bundle!disk.GenericDisk_v.Address./Address/page_invariant_definition
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

;; Function-Decl vstd::map::impl&%0::empty
(declare-fun vstd!map.impl&%0.empty.? (Type Type Type Type) Poly)

;; Function-Decl vstd::map::impl&%0::dom
(declare-fun vstd!map.impl&%0.dom.? (Type Type Type Type Poly) Poly)

;; Function-Decl vstd::map::impl&%0::index
(declare-fun vstd!map.impl&%0.index.? (Type Type Type Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::spec_index
(declare-fun vstd!map.impl&%0.spec_index.? (Type Type Type Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::insert
(declare-fun vstd!map.impl&%0.insert.? (Type Type Type Type Poly Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::remove
(declare-fun vstd!map.impl&%0.remove.? (Type Type Type Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::contains_key
(declare-fun vstd!map.impl&%0.contains_key.? (Type Type Type Type Poly Poly) Bool)

;; Function-Decl vstd::map::impl&%0::le
(declare-fun vstd!map.impl&%0.le.? (Type Type Type Type Poly Poly) Bool)

;; Function-Decl vstd::map::check_argument_is_map
(declare-fun vstd!map.check_argument_is_map.? (Type Type Type Type Poly) Poly)

;; Function-Decl vstd::option::impl&%1::spec_unwrap
(declare-fun vstd!option.impl&%1.spec_unwrap.? (Type Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::empty
(declare-fun vstd!set.impl&%0.empty.? (Type Type) Poly)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Type Type Type Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::contains
(declare-fun vstd!set.impl&%0.contains.? (Type Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::subset_of
(declare-fun vstd!set.impl&%0.subset_of.? (Type Type Poly Poly) Bool)

;; Function-Decl vstd::set::impl&%0::insert
(declare-fun vstd!set.impl&%0.insert.? (Type Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::remove
(declare-fun vstd!set.impl&%0.remove.? (Type Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::union
(declare-fun vstd!set.impl&%0.union.? (Type Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::intersect
(declare-fun vstd!set.impl&%0.intersect.? (Type Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::difference
(declare-fun vstd!set.impl&%0.difference.? (Type Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::complement
(declare-fun vstd!set.impl&%0.complement.? (Type Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::finite
(declare-fun vstd!set.impl&%0.finite.? (Type Type Poly) Bool)

;; Function-Decl vstd::set::impl&%0::len
(declare-fun vstd!set.impl&%0.len.? (Type Type Poly) Int)

;; Function-Decl vstd::set::impl&%0::choose
(declare-fun vstd!set.impl&%0.choose.? (Type Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::mk_map
(declare-fun vstd!set.impl&%0.mk_map.? (Type Type Type Type Type Type Poly Poly) Poly)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::wf
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.wf.? (Poly) Bool)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::contains
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.contains.? (Poly Poly)
 Bool
)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::contains_exactly
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.? (Poly
  Poly
 ) Bool
)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::is_empty
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.? (Poly) Bool)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::can_follow
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.? (Poly Poly)
 Bool
)

;; Function-Decl bundle::coordination_layer::MsgHistory_v::impl&%0::can_concat
(declare-fun bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.? (Poly Poly)
 Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%0::wf
(declare-fun bundle!journal.LinkedJournal_v.impl&%0.wf.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%0::has_link
(declare-fun bundle!journal.LinkedJournal_v.impl&%0.has_link.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%0::cropped_prior
(declare-fun bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (Poly Poly) vstd!option.Option.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%0::contains_lsn
(declare-fun bundle!journal.LinkedJournal_v.impl&%0.contains_lsn.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::entries_wf
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::is_nondangling_pointer
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly
  Poly
 ) Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::nondangling_pointers
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? (Poly)
 Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::this_block_can_concat
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.? (Poly Poly)
 Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::blocks_can_concat
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::blocks_each_have_link
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.? (Poly)
 Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::block_in_bounds
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly Poly)
 Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::wf
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::valid_ranking
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::acyclic
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::the_ranking
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.the_ranking.? (Poly) vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::decodable
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::the_rank_of
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? (Poly Poly) Int)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::discard_old
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.discard_old.? (Poly Poly) bundle!journal.LinkedJournal_v.DiskView.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::is_sub_disk
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::is_sub_disk_with_newer_lsn
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.? (
  Poly Poly
 ) Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::build_tight
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly Poly) bundle!journal.LinkedJournal_v.DiskView.)
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? (Poly Poly Fuel)
 bundle!journal.LinkedJournal_v.DiskView.
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::representation
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.representation.? (Poly Poly) vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? (Poly Poly
  Fuel
 ) vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::can_crop
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.can_crop.? (Poly Poly Poly) Bool)
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? (Poly Poly Poly
  Fuel
 ) Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? (Poly Poly
  Poly
 ) vstd!option.Option.
)
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? (Poly
  Poly Poly Fuel
 ) vstd!option.Option.
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::iptr
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly Poly) vstd!option.Option.)
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.? (Poly Poly Fuel) vstd!option.Option.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::next
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.next.? (Poly Poly) vstd!option.Option.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%1::is_tight
(declare-fun bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::wf
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.wf.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::seq_start
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.seq_start.? (Poly) Int)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::seq_end
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.seq_end.? (Poly) Int)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::can_discard_to
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::discard_old
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.discard_old.? (Poly Poly) bundle!journal.LinkedJournal_v.TruncatedJournal.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::decodable
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.decodable.? (Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::can_crop
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.can_crop.? (Poly Poly) Bool)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::crop
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.crop.? (Poly Poly) bundle!journal.LinkedJournal_v.TruncatedJournal.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::append_record
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.append_record.? (Poly Poly Poly)
 bundle!journal.LinkedJournal_v.TruncatedJournal.
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::build_tight
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.build_tight.? (Poly) bundle!journal.LinkedJournal_v.TruncatedJournal.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::representation
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.representation.? (Poly) vstd!set.Set<bundle!disk.GenericDisk_v.Address.>.)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::disk_is_tight_wrt_representation
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.?
 (Poly) Bool
)

;; Function-Decl bundle::journal::LinkedJournal_v::impl&%2::mkfs
(declare-fun bundle!journal.LinkedJournal_v.impl&%2.mkfs.? (Poly) bundle!journal.LinkedJournal_v.TruncatedJournal.)

;; Function-Axioms vstd::map::impl&%0::empty
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type)) (!
   (has_type (vstd!map.impl&%0.empty.? K& K&. V& V&.) (TYPE%vstd!map.Map. K& V&))
   :pattern ((vstd!map.impl&%0.empty.? K& K&. V& V&.))
   :qid
   internal_vstd!map.impl&__0.empty.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.empty.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::mk_map
(assert
 (forall ((A& Type) (A&. Type) (V& Type) (V&. Type) (F& Type) (F&. Type) (self~2@ Poly)
   (f~4@ Poly)
  ) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type f~4@ F&)
    )
    (has_type (vstd!set.impl&%0.mk_map.? A& A&. V& V&. F& F&. self~2@ f~4@) (TYPE%vstd!map.Map.
      A& V&
   )))
   :pattern ((vstd!set.impl&%0.mk_map.? A& A&. V& V&. F& F&. self~2@ f~4@))
   :qid
   internal_vstd!set.impl&__0.mk_map.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.mk_map.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::complement
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%vstd!set.Set. A&))
    (has_type (vstd!set.impl&%0.complement.? A& A&. self~2@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.complement.? A& A&. self~2@))
   :qid
   internal_vstd!set.impl&__0.complement.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.complement.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::empty
(assert
 (forall ((A& Type) (A&. Type)) (!
   (has_type (vstd!set.impl&%0.empty.? A& A&.) (TYPE%vstd!set.Set. A&))
   :pattern ((vstd!set.impl&%0.empty.? A& A&.))
   :qid
   internal_vstd!set.impl&__0.empty.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.empty.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::new
(assert
 (forall ((A& Type) (A&. Type) (F& Type) (F&. Type) (f~2@ Poly)) (!
   (=>
    (has_type f~2@ F&)
    (has_type (vstd!set.impl&%0.new.? A& A&. F& F&. f~2@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.new.? A& A&. F& F&. f~2@))
   :qid
   internal_vstd!set.impl&__0.new.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.new.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::dom
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%vstd!map.Map. K& V&))
    (has_type (vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@) (TYPE%vstd!set.Set. K&))
   )
   :pattern ((vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@))
   :qid
   internal_vstd!map.impl&__0.dom.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.dom.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::index
(declare-fun req%vstd!map.impl&%0.index. (Type Type Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
   !
   (= (req%vstd!map.impl&%0.index. K& K&. V& V&. self~2@ key~4@) (=>
     %%global_location_label%%0
     (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@)
      key~4@
   )))
   :pattern ((req%vstd!map.impl&%0.index. K& K&. V& V&. self~2@ key~4@))
   :qid
   internal_req__vstd!map.impl&__0.index._definition
   :skolemid
   skolem_internal_req__vstd!map.impl&__0.index._definition
)))

;; Function-Axioms vstd::map::impl&%0::index
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
   !
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4@ K&)
    )
    (has_type (vstd!map.impl&%0.index.? K& K&. V& V&. self~2@ key~4@) V&)
   )
   :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. self~2@ key~4@))
   :qid
   internal_vstd!map.impl&__0.index.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.index.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::spec_index
(declare-fun req%vstd!map.impl&%0.spec_index. (Type Type Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
   !
   (= (req%vstd!map.impl&%0.spec_index. K& K&. V& V&. self~2@ key~4@) (=>
     %%global_location_label%%1
     (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@)
      key~4@
   )))
   :pattern ((req%vstd!map.impl&%0.spec_index. K& K&. V& V&. self~2@ key~4@))
   :qid
   internal_req__vstd!map.impl&__0.spec_index._definition
   :skolemid
   skolem_internal_req__vstd!map.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::map::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.spec_index.)
  (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
    !
    (= (vstd!map.impl&%0.spec_index.? K& K&. V& V&. self~2@ key~4@) (vstd!map.impl&%0.index.?
      K& K&. V& V&. self~2@ key~4@
    ))
    :pattern ((vstd!map.impl&%0.spec_index.? K& K&. V& V&. self~2@ key~4@))
    :qid
    internal_vstd!map.impl&__0.spec_index.?_definition
    :skolemid
    skolem_internal_vstd!map.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
   !
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4@ K&)
    )
    (has_type (vstd!map.impl&%0.spec_index.? K& K&. V& V&. self~2@ key~4@) V&)
   )
   :pattern ((vstd!map.impl&%0.spec_index.? K& K&. V& V&. self~2@ key~4@))
   :qid
   internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::insert
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly) (value~6@
    Poly
   )
  ) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4@ K&)
     (has_type value~6@ V&)
    )
    (has_type (vstd!map.impl&%0.insert.? K& K&. V& V&. self~2@ key~4@ value~6@) (TYPE%vstd!map.Map.
      K& V&
   )))
   :pattern ((vstd!map.impl&%0.insert.? K& K&. V& V&. self~2@ key~4@ value~6@))
   :qid
   internal_vstd!map.impl&__0.insert.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.insert.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::remove
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (key~4@ Poly)) (
   !
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4@ K&)
    )
    (has_type (vstd!map.impl&%0.remove.? K& K&. V& V&. self~2@ key~4@) (TYPE%vstd!map.Map.
      K& V&
   )))
   :pattern ((vstd!map.impl&%0.remove.? K& K&. V& V&. self~2@ key~4@))
   :qid
   internal_vstd!map.impl&__0.remove.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.impl&__0.remove.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::contains_key
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.contains_key.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.contains_key.)
  (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (k~4@ Poly)) (!
    (= (vstd!map.impl&%0.contains_key.? K& K&. V& V&. self~2@ k~4@) (vstd!set.impl&%0.contains.?
      K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@) k~4@
    ))
    :pattern ((vstd!map.impl&%0.contains_key.? K& K&. V& V&. self~2@ k~4@))
    :qid
    internal_vstd!map.impl&__0.contains_key.?_definition
    :skolemid
    skolem_internal_vstd!map.impl&__0.contains_key.?_definition
))))

;; Function-Axioms vstd::map::impl&%0::le
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.le.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.le.)
  (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (self~2@ Poly) (m2~4@ Poly)) (!
    (= (vstd!map.impl&%0.le.? K& K&. V& V&. self~2@ m2~4@) (forall ((k~12$ Poly)) (!
       (=>
        (has_type k~12$ K&)
        (=>
         (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. self~2@)
          k~12$
         )
         (and
          (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4@) k~12$)
          (= (vstd!map.impl&%0.index.? K& K&. V& V&. self~2@ k~12$) (vstd!map.impl&%0.index.?
            K& K&. V& V&. m2~4@ k~12$
       )))))
       :pattern ((vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&.
          self~2@
         ) k~12$
        ) (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4@)
         k~12$
       ))
       :qid
       user_vstd__map__impl&%0__le_0
       :skolemid
       skolem_user_vstd__map__impl&%0__le_0
    )))
    :pattern ((vstd!map.impl&%0.le.? K& K&. V& V&. self~2@ m2~4@))
    :qid
    internal_vstd!map.impl&__0.le.?_definition
    :skolemid
    skolem_internal_vstd!map.impl&__0.le.?_definition
))))

;; Function-Axioms vstd::set::impl&%0::subset_of
(assert
 (fuel_bool_default fuel%vstd!set.impl&%0.subset_of.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!set.impl&%0.subset_of.)
  (forall ((A& Type) (A&. Type) (self~2@ Poly) (s2~4@ Poly)) (!
    (= (vstd!set.impl&%0.subset_of.? A& A&. self~2@ s2~4@) (forall ((a~12$ Poly)) (!
       (=>
        (has_type a~12$ A&)
        (=>
         (vstd!set.impl&%0.contains.? A& A&. self~2@ a~12$)
         (vstd!set.impl&%0.contains.? A& A&. s2~4@ a~12$)
       ))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. self~2@ a~12$))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. s2~4@ a~12$))
       :qid
       user_vstd__set__impl&%0__subset_of_1
       :skolemid
       skolem_user_vstd__set__impl&%0__subset_of_1
    )))
    :pattern ((vstd!set.impl&%0.subset_of.? A& A&. self~2@ s2~4@))
    :qid
    internal_vstd!set.impl&__0.subset_of.?_definition
    :skolemid
    skolem_internal_vstd!set.impl&__0.subset_of.?_definition
))))

;; Function-Axioms vstd::map::axiom_map_empty
(declare-fun ens%vstd!map.axiom_map_empty. (Type Type Type Type) Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type)) (!
   (= (ens%vstd!map.axiom_map_empty. K& K&. V& V&.) (= (vstd!map.impl&%0.dom.? K& K&. V&
      V&. (vstd!map.impl&%0.empty.? K& K&. V& V&.)
     ) (vstd!set.impl&%0.empty.? K& K&.)
   ))
   :pattern ((ens%vstd!map.axiom_map_empty. K& K&. V& V&.))
   :qid
   internal_ens__vstd!map.axiom_map_empty._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_empty._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type)) (!
   (= (vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.empty.? K& K&. V& V&.))
    (vstd!set.impl&%0.empty.? K& K&.)
   )
   :pattern ((vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.empty.? K& K&. V&
      V&.
   )))
   :qid
   user_vstd__map__axiom_map_empty_2
   :skolemid
   skolem_user_vstd__map__axiom_map_empty_2
)))

;; Function-Axioms vstd::set::impl&%0::insert
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly) (a~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type a~4@ A&)
    )
    (has_type (vstd!set.impl&%0.insert.? A& A&. self~2@ a~4@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.insert.? A& A&. self~2@ a~4@))
   :qid
   internal_vstd!set.impl&__0.insert.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.insert.?_pre_post_definition
)))

;; Function-Axioms vstd::map::axiom_map_insert_domain
(declare-fun ens%vstd!map.axiom_map_insert_domain. (Type Type Type Type Poly Poly Poly)
 Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key~4@ Poly) (value~6@
    Poly
   )
  ) (!
   (= (ens%vstd!map.axiom_map_insert_domain. K& K&. V& V&. m~2@ key~4@ value~6@) (= (vstd!map.impl&%0.dom.?
      K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&. m~2@ key~4@ value~6@)
     ) (vstd!set.impl&%0.insert.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2@) key~4@)
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_domain. K& K&. V& V&. m~2@ key~4@ value~6@))
   :qid
   internal_ens__vstd!map.axiom_map_insert_domain._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_insert_domain._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2$ Poly) (key~4$ Poly) (value~6$
    Poly
   )
  ) (!
   (=>
    (and
     (has_type m~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4$ K&)
     (has_type value~6$ V&)
    )
    (= (vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&. m~2$
       key~4$ value~6$
      )
     ) (vstd!set.impl&%0.insert.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2$) key~4$)
   ))
   :pattern ((vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V&
      V&. m~2$ key~4$ value~6$
   )))
   :qid
   user_vstd__map__axiom_map_insert_domain_3
   :skolemid
   skolem_user_vstd__map__axiom_map_insert_domain_3
)))

;; Function-Axioms vstd::map::axiom_map_insert_same
(declare-fun ens%vstd!map.axiom_map_insert_same. (Type Type Type Type Poly Poly Poly)
 Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key~4@ Poly) (value~6@
    Poly
   )
  ) (!
   (= (ens%vstd!map.axiom_map_insert_same. K& K&. V& V&. m~2@ key~4@ value~6@) (= (vstd!map.impl&%0.index.?
      K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&. m~2@ key~4@ value~6@) key~4@
     ) value~6@
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_same. K& K&. V& V&. m~2@ key~4@ value~6@))
   :qid
   internal_ens__vstd!map.axiom_map_insert_same._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_insert_same._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2$ Poly) (key~4$ Poly) (value~6$
    Poly
   )
  ) (!
   (=>
    (and
     (has_type m~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4$ K&)
     (has_type value~6$ V&)
    )
    (= (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&.
       m~2$ key~4$ value~6$
      ) key~4$
     ) value~6$
   ))
   :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&.
      V& V&. m~2$ key~4$ value~6$
     ) key~4$
   ))
   :qid
   user_vstd__map__axiom_map_insert_same_4
   :skolemid
   skolem_user_vstd__map__axiom_map_insert_same_4
)))

;; Function-Specs vstd::map::axiom_map_insert_different
(declare-fun req%vstd!map.axiom_map_insert_different. (Type Type Type Type Poly Poly
  Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%2 Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key1~4@ Poly) (key2~6@
    Poly
   ) (value~8@ Poly)
  ) (!
   (= (req%vstd!map.axiom_map_insert_different. K& K&. V& V&. m~2@ key1~4@ key2~6@ value~8@)
    (and
     (=>
      %%global_location_label%%2
      (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2@) key1~4@)
     )
     (=>
      %%global_location_label%%3
      (not (= key1~4@ key2~6@))
   )))
   :pattern ((req%vstd!map.axiom_map_insert_different. K& K&. V& V&. m~2@ key1~4@ key2~6@
     value~8@
   ))
   :qid
   internal_req__vstd!map.axiom_map_insert_different._definition
   :skolemid
   skolem_internal_req__vstd!map.axiom_map_insert_different._definition
)))

;; Function-Axioms vstd::map::axiom_map_insert_different
(declare-fun ens%vstd!map.axiom_map_insert_different. (Type Type Type Type Poly Poly
  Poly Poly
 ) Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key1~4@ Poly) (key2~6@
    Poly
   ) (value~8@ Poly)
  ) (!
   (= (ens%vstd!map.axiom_map_insert_different. K& K&. V& V&. m~2@ key1~4@ key2~6@ value~8@)
    (= (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&.
       m~2@ key2~6@ value~8@
      ) key1~4@
     ) (vstd!map.impl&%0.index.? K& K&. V& V&. m~2@ key1~4@)
   ))
   :pattern ((ens%vstd!map.axiom_map_insert_different. K& K&. V& V&. m~2@ key1~4@ key2~6@
     value~8@
   ))
   :qid
   internal_ens__vstd!map.axiom_map_insert_different._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_insert_different._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2$ Poly) (key1~4$ Poly) (key2~6$
    Poly
   ) (value~8$ Poly)
  ) (!
   (=>
    (and
     (has_type m~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type key1~4$ K&)
     (has_type key2~6$ K&)
     (has_type value~8$ V&)
    )
    (=>
     (and
      (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2$) key1~4$)
      (not (= key1~4$ key2~6$))
     )
     (= (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&. V& V&.
        m~2$ key2~6$ value~8$
       ) key1~4$
      ) (vstd!map.impl&%0.index.? K& K&. V& V&. m~2$ key1~4$)
   )))
   :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.insert.? K& K&.
      V& V&. m~2$ key2~6$ value~8$
     ) key1~4$
   ))
   :qid
   user_vstd__map__axiom_map_insert_different_5
   :skolemid
   skolem_user_vstd__map__axiom_map_insert_different_5
)))

;; Function-Axioms vstd::set::impl&%0::remove
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly) (a~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type a~4@ A&)
    )
    (has_type (vstd!set.impl&%0.remove.? A& A&. self~2@ a~4@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.remove.? A& A&. self~2@ a~4@))
   :qid
   internal_vstd!set.impl&__0.remove.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.remove.?_pre_post_definition
)))

;; Function-Axioms vstd::map::axiom_map_remove_domain
(declare-fun ens%vstd!map.axiom_map_remove_domain. (Type Type Type Type Poly Poly)
 Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key~4@ Poly)) (!
   (= (ens%vstd!map.axiom_map_remove_domain. K& K&. V& V&. m~2@ key~4@) (= (vstd!map.impl&%0.dom.?
      K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&. V& V&. m~2@ key~4@)
     ) (vstd!set.impl&%0.remove.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2@) key~4@)
   ))
   :pattern ((ens%vstd!map.axiom_map_remove_domain. K& K&. V& V&. m~2@ key~4@))
   :qid
   internal_ens__vstd!map.axiom_map_remove_domain._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_remove_domain._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2$ Poly) (key~4$ Poly)) (!
   (=>
    (and
     (has_type m~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type key~4$ K&)
    )
    (= (vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&. V& V&. m~2$
       key~4$
      )
     ) (vstd!set.impl&%0.remove.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2$) key~4$)
   ))
   :pattern ((vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&. V&
      V&. m~2$ key~4$
   )))
   :qid
   user_vstd__map__axiom_map_remove_domain_6
   :skolemid
   skolem_user_vstd__map__axiom_map_remove_domain_6
)))

;; Function-Specs vstd::map::axiom_map_remove_different
(declare-fun req%vstd!map.axiom_map_remove_different. (Type Type Type Type Poly Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%4 Bool)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key1~4@ Poly) (key2~6@
    Poly
   )
  ) (!
   (= (req%vstd!map.axiom_map_remove_different. K& K&. V& V&. m~2@ key1~4@ key2~6@) (
     and
     (=>
      %%global_location_label%%4
      (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2@) key1~4@)
     )
     (=>
      %%global_location_label%%5
      (not (= key1~4@ key2~6@))
   )))
   :pattern ((req%vstd!map.axiom_map_remove_different. K& K&. V& V&. m~2@ key1~4@ key2~6@))
   :qid
   internal_req__vstd!map.axiom_map_remove_different._definition
   :skolemid
   skolem_internal_req__vstd!map.axiom_map_remove_different._definition
)))

;; Function-Axioms vstd::map::axiom_map_remove_different
(declare-fun ens%vstd!map.axiom_map_remove_different. (Type Type Type Type Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly) (key1~4@ Poly) (key2~6@
    Poly
   )
  ) (!
   (= (ens%vstd!map.axiom_map_remove_different. K& K&. V& V&. m~2@ key1~4@ key2~6@) (
     = (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&. V& V&.
       m~2@ key2~6@
      ) key1~4@
     ) (vstd!map.impl&%0.index.? K& K&. V& V&. m~2@ key1~4@)
   ))
   :pattern ((ens%vstd!map.axiom_map_remove_different. K& K&. V& V&. m~2@ key1~4@ key2~6@))
   :qid
   internal_ens__vstd!map.axiom_map_remove_different._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_remove_different._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2$ Poly) (key1~4$ Poly) (key2~6$
    Poly
   )
  ) (!
   (=>
    (and
     (has_type m~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type key1~4$ K&)
     (has_type key2~6$ K&)
    )
    (=>
     (and
      (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m~2$) key1~4$)
      (not (= key1~4$ key2~6$))
     )
     (= (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&. V& V&.
        m~2$ key2~6$
       ) key1~4$
      ) (vstd!map.impl&%0.index.? K& K&. V& V&. m~2$ key1~4$)
   )))
   :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!map.impl&%0.remove.? K& K&.
      V& V&. m~2$ key2~6$
     ) key1~4$
   ))
   :qid
   user_vstd__map__axiom_map_remove_different_7
   :skolemid
   skolem_user_vstd__map__axiom_map_remove_different_7
)))

;; Function-Axioms vstd::map::axiom_map_ext_equal
(declare-fun ens%vstd!map.axiom_map_ext_equal. (Type Type Type Type Poly Poly) Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m1~2@ Poly) (m2~4@ Poly)) (!
   (= (ens%vstd!map.axiom_map_ext_equal. K& K&. V& V&. m1~2@ m2~4@) (= (ext_eq false (TYPE%vstd!map.Map.
       K& V&
      ) (TYPE%vstd!map.Map. K&. V&.) m1~2@ m2~4@
     ) (and
      (ext_eq false (TYPE%vstd!set.Set. K&) (TYPE%vstd!set.Set. K&.) (vstd!map.impl&%0.dom.?
        K& K&. V& V&. m1~2@
       ) (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4@)
      )
      (forall ((k~47$ Poly)) (!
        (=>
         (has_type k~47$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m1~2@) k~47$)
          (= (vstd!map.impl&%0.index.? K& K&. V& V&. m1~2@ k~47$) (vstd!map.impl&%0.index.? K&
            K&. V& V&. m2~4@ k~47$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m1~2@ k~47$))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m2~4@ k~47$))
        :qid
        user_vstd__map__axiom_map_ext_equal_8
        :skolemid
        skolem_user_vstd__map__axiom_map_ext_equal_8
   )))))
   :pattern ((ens%vstd!map.axiom_map_ext_equal. K& K&. V& V&. m1~2@ m2~4@))
   :qid
   internal_ens__vstd!map.axiom_map_ext_equal._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_ext_equal._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m1~2$ Poly) (m2~4$ Poly)) (!
   (=>
    (and
     (has_type m1~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type m2~4$ (TYPE%vstd!map.Map. K& V&))
    )
    (= (ext_eq false (TYPE%vstd!map.Map. K& V&) (TYPE%vstd!map.Map. K&. V&.) m1~2$ m2~4$)
     (and
      (ext_eq false (TYPE%vstd!set.Set. K&) (TYPE%vstd!set.Set. K&.) (vstd!map.impl&%0.dom.?
        K& K&. V& V&. m1~2$
       ) (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4$)
      )
      (forall ((k~47$ Poly)) (!
        (=>
         (has_type k~47$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m1~2$) k~47$)
          (= (vstd!map.impl&%0.index.? K& K&. V& V&. m1~2$ k~47$) (vstd!map.impl&%0.index.? K&
            K&. V& V&. m2~4$ k~47$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m1~2$ k~47$))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m2~4$ k~47$))
        :qid
        user_vstd__map__axiom_map_ext_equal_9
        :skolemid
        skolem_user_vstd__map__axiom_map_ext_equal_9
   )))))
   :pattern ((ext_eq false (TYPE%vstd!map.Map. K& V&) (TYPE%vstd!map.Map. K&. V&.) m1~2$
     m2~4$
   ))
   :qid
   user_vstd__map__axiom_map_ext_equal_10
   :skolemid
   skolem_user_vstd__map__axiom_map_ext_equal_10
)))

;; Function-Axioms vstd::map::axiom_map_ext_equal_deep
(declare-fun ens%vstd!map.axiom_map_ext_equal_deep. (Type Type Type Type Poly Poly)
 Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m1~2@ Poly) (m2~4@ Poly)) (!
   (= (ens%vstd!map.axiom_map_ext_equal_deep. K& K&. V& V&. m1~2@ m2~4@) (= (ext_eq true
      (TYPE%vstd!map.Map. K& V&) (TYPE%vstd!map.Map. K&. V&.) m1~2@ m2~4@
     ) (and
      (ext_eq true (TYPE%vstd!set.Set. K&) (TYPE%vstd!set.Set. K&.) (vstd!map.impl&%0.dom.?
        K& K&. V& V&. m1~2@
       ) (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4@)
      )
      (forall ((k~47$ Poly)) (!
        (=>
         (has_type k~47$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m1~2@) k~47$)
          (ext_eq true V& V&. (vstd!map.impl&%0.index.? K& K&. V& V&. m1~2@ k~47$) (vstd!map.impl&%0.index.?
            K& K&. V& V&. m2~4@ k~47$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m1~2@ k~47$))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m2~4@ k~47$))
        :qid
        user_vstd__map__axiom_map_ext_equal_deep_11
        :skolemid
        skolem_user_vstd__map__axiom_map_ext_equal_deep_11
   )))))
   :pattern ((ens%vstd!map.axiom_map_ext_equal_deep. K& K&. V& V&. m1~2@ m2~4@))
   :qid
   internal_ens__vstd!map.axiom_map_ext_equal_deep._definition
   :skolemid
   skolem_internal_ens__vstd!map.axiom_map_ext_equal_deep._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m1~2$ Poly) (m2~4$ Poly)) (!
   (=>
    (and
     (has_type m1~2$ (TYPE%vstd!map.Map. K& V&))
     (has_type m2~4$ (TYPE%vstd!map.Map. K& V&))
    )
    (= (ext_eq true (TYPE%vstd!map.Map. K& V&) (TYPE%vstd!map.Map. K&. V&.) m1~2$ m2~4$)
     (and
      (ext_eq true (TYPE%vstd!set.Set. K&) (TYPE%vstd!set.Set. K&.) (vstd!map.impl&%0.dom.?
        K& K&. V& V&. m1~2$
       ) (vstd!map.impl&%0.dom.? K& K&. V& V&. m2~4$)
      )
      (forall ((k~47$ Poly)) (!
        (=>
         (has_type k~47$ K&)
         (=>
          (vstd!set.impl&%0.contains.? K& K&. (vstd!map.impl&%0.dom.? K& K&. V& V&. m1~2$) k~47$)
          (ext_eq true V& V&. (vstd!map.impl&%0.index.? K& K&. V& V&. m1~2$ k~47$) (vstd!map.impl&%0.index.?
            K& K&. V& V&. m2~4$ k~47$
        ))))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m1~2$ k~47$))
        :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. m2~4$ k~47$))
        :qid
        user_vstd__map__axiom_map_ext_equal_deep_12
        :skolemid
        skolem_user_vstd__map__axiom_map_ext_equal_deep_12
   )))))
   :pattern ((ext_eq true (TYPE%vstd!map.Map. K& V&) (TYPE%vstd!map.Map. K&. V&.) m1~2$
     m2~4$
   ))
   :qid
   user_vstd__map__axiom_map_ext_equal_deep_13
   :skolemid
   skolem_user_vstd__map__axiom_map_ext_equal_deep_13
)))

;; Function-Axioms vstd::map::check_argument_is_map
(assert
 (fuel_bool_default fuel%vstd!map.check_argument_is_map.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.check_argument_is_map.)
  (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly)) (!
    (= (vstd!map.check_argument_is_map.? K& K&. V& V&. m~2@) m~2@)
    :pattern ((vstd!map.check_argument_is_map.? K& K&. V& V&. m~2@))
    :qid
    internal_vstd!map.check_argument_is_map.?_definition
    :skolemid
    skolem_internal_vstd!map.check_argument_is_map.?_definition
))))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (m~2@ Poly)) (!
   (=>
    (has_type m~2@ (TYPE%vstd!map.Map. K& V&))
    (has_type (vstd!map.check_argument_is_map.? K& K&. V& V&. m~2@) (TYPE%vstd!map.Map.
      K& V&
   )))
   :pattern ((vstd!map.check_argument_is_map.? K& K&. V& V&. m~2@))
   :qid
   internal_vstd!map.check_argument_is_map.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!map.check_argument_is_map.?_pre_post_definition
)))

;; Function-Specs vstd::option::impl&%1::spec_unwrap
(declare-fun req%vstd!option.impl&%1.spec_unwrap. (Type Type Poly) Bool)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
   (= (req%vstd!option.impl&%1.spec_unwrap. A& A&. self~2@) (=>
     %%global_location_label%%6
     (is-vstd!option.Option./Some (%Poly%vstd!option.Option. self~2@))
   ))
   :pattern ((req%vstd!option.impl&%1.spec_unwrap. A& A&. self~2@))
   :qid
   internal_req__vstd!option.impl&__1.spec_unwrap._definition
   :skolemid
   skolem_internal_req__vstd!option.impl&__1.spec_unwrap._definition
)))

;; Function-Axioms vstd::option::impl&%1::spec_unwrap
(assert
 (fuel_bool_default fuel%vstd!option.impl&%1.spec_unwrap.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!option.impl&%1.spec_unwrap.)
  (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
    (= (vstd!option.impl&%1.spec_unwrap.? A& A&. self~2@) (vstd!option.Option./Some/_0
      (%Poly%vstd!option.Option. self~2@)
    ))
    :pattern ((vstd!option.impl&%1.spec_unwrap.? A& A&. self~2@))
    :qid
    internal_vstd!option.impl&__1.spec_unwrap.?_definition
    :skolemid
    skolem_internal_vstd!option.impl&__1.spec_unwrap.?_definition
))))
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%vstd!option.Option. A&))
    (has_type (vstd!option.impl&%1.spec_unwrap.? A& A&. self~2@) A&)
   )
   :pattern ((vstd!option.impl&%1.spec_unwrap.? A& A&. self~2@))
   :qid
   internal_vstd!option.impl&__1.spec_unwrap.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!option.impl&__1.spec_unwrap.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::len
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%vstd!set.Set. A&))
    (<= 0 (vstd!set.impl&%0.len.? A& A&. self~2@))
   )
   :pattern ((vstd!set.impl&%0.len.? A& A&. self~2@))
   :qid
   internal_vstd!set.impl&__0.len.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.len.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::union
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly) (s2~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type s2~4@ (TYPE%vstd!set.Set. A&))
    )
    (has_type (vstd!set.impl&%0.union.? A& A&. self~2@ s2~4@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.union.? A& A&. self~2@ s2~4@))
   :qid
   internal_vstd!set.impl&__0.union.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.union.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::intersect
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly) (s2~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type s2~4@ (TYPE%vstd!set.Set. A&))
    )
    (has_type (vstd!set.impl&%0.intersect.? A& A&. self~2@ s2~4@) (TYPE%vstd!set.Set. A&))
   )
   :pattern ((vstd!set.impl&%0.intersect.? A& A&. self~2@ s2~4@))
   :qid
   internal_vstd!set.impl&__0.intersect.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.intersect.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::difference
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly) (s2~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ (TYPE%vstd!set.Set. A&))
     (has_type s2~4@ (TYPE%vstd!set.Set. A&))
    )
    (has_type (vstd!set.impl&%0.difference.? A& A&. self~2@ s2~4@) (TYPE%vstd!set.Set.
      A&
   )))
   :pattern ((vstd!set.impl&%0.difference.? A& A&. self~2@ s2~4@))
   :qid
   internal_vstd!set.impl&__0.difference.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.difference.?_pre_post_definition
)))

;; Function-Axioms vstd::set::impl&%0::choose
(assert
 (fuel_bool_default fuel%vstd!set.impl&%0.choose.)
)
(declare-fun %%choose%%0 (Type Type Type Poly Type Type Poly) Poly)
(assert
 (forall ((%%hole%%0 Type) (%%hole%%1 Type) (%%hole%%2 Type) (%%hole%%3 Poly) (%%hole%%4
    Type
   ) (%%hole%%5 Type) (%%hole%%6 Poly)
  ) (!
   (=>
    (exists ((a~10$ Poly)) (!
      (and
       (has_type a~10$ %%hole%%0)
       (vstd!set.impl&%0.contains.? %%hole%%1 %%hole%%2 %%hole%%3 a~10$)
      )
      :pattern ((vstd!set.impl&%0.contains.? %%hole%%4 %%hole%%5 %%hole%%6 a~10$))
      :qid
      user_vstd__set__impl&%0__choose_14
      :skolemid
      skolem_user_vstd__set__impl&%0__choose_14
    ))
    (exists ((a~10$ Poly)) (!
      (and
       (and
        (has_type a~10$ %%hole%%0)
        (vstd!set.impl&%0.contains.? %%hole%%1 %%hole%%2 %%hole%%3 a~10$)
       )
       (= (%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5 %%hole%%6)
        a~10$
      ))
      :pattern ((vstd!set.impl&%0.contains.? %%hole%%4 %%hole%%5 %%hole%%6 a~10$))
   )))
   :pattern ((%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
     %%hole%%6
)))))
(assert
 (=>
  (fuel_bool fuel%vstd!set.impl&%0.choose.)
  (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
    (= (vstd!set.impl&%0.choose.? A& A&. self~2@) (as_type (%%choose%%0 A& A& A&. self~2@
       A& A&. self~2@
      ) A&
    ))
    :pattern ((vstd!set.impl&%0.choose.? A& A&. self~2@))
    :qid
    internal_vstd!set.impl&__0.choose.?_definition
    :skolemid
    skolem_internal_vstd!set.impl&__0.choose.?_definition
))))
(assert
 (forall ((A& Type) (A&. Type) (self~2@ Poly)) (!
   (=>
    (has_type self~2@ (TYPE%vstd!set.Set. A&))
    (has_type (vstd!set.impl&%0.choose.? A& A&. self~2@) A&)
   )
   :pattern ((vstd!set.impl&%0.choose.? A& A&. self~2@))
   :qid
   internal_vstd!set.impl&__0.choose.?_pre_post_definition
   :skolemid
   skolem_internal_vstd!set.impl&__0.choose.?_pre_post_definition
)))

;; Function-Axioms vstd::set::axiom_set_empty
(declare-fun ens%vstd!set.axiom_set_empty. (Type Type Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (a~2@ Poly)) (!
   (= (ens%vstd!set.axiom_set_empty. A& A&. a~2@) (not (vstd!set.impl&%0.contains.? A&
      A&. (vstd!set.impl&%0.empty.? A& A&.) a~2@
   )))
   :pattern ((ens%vstd!set.axiom_set_empty. A& A&. a~2@))
   :qid
   internal_ens__vstd!set.axiom_set_empty._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_empty._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (a~2$ Poly)) (!
   (=>
    (has_type a~2$ A&)
    (not (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.empty.? A& A&.) a~2$))
   )
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.empty.? A& A&.) a~2$))
   :qid
   user_vstd__set__axiom_set_empty_15
   :skolemid
   skolem_user_vstd__set__axiom_set_empty_15
)))

;; Function-Axioms vstd::set::axiom_set_new
(declare-fun ens%vstd!set.axiom_set_new. (Type Type %%Function%% Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (f~2@ %%Function%%) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_new. A& A&. f~2@ a~4@) (= (vstd!set.impl&%0.contains.? A&
      A&. (vstd!set.impl&%0.new.? A& A&. (TYPE%fun%1. A& BOOL) (TYPE%fun%1. A&. BOOL) (Poly%fun%1.
        f~2@
       )
      ) a~4@
     ) (%B (%%apply%%0 f~2@ a~4@))
   ))
   :pattern ((ens%vstd!set.axiom_set_new. A& A&. f~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_new._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_new._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (f~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type f~2$ (TYPE%fun%1. A& BOOL))
     (has_type a~4$ A&)
    )
    (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.new.? A& A&. (TYPE%fun%1. A&
        BOOL
       ) (TYPE%fun%1. A&. BOOL) f~2$
      ) a~4$
     ) (%B (%%apply%%0 (%Poly%fun%1. f~2$) a~4$))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.new.? A& A&. (TYPE%fun%1.
       A& BOOL
      ) (TYPE%fun%1. A&. BOOL) f~2$
     ) a~4$
   ))
   :qid
   user_vstd__set__axiom_set_new_16
   :skolemid
   skolem_user_vstd__set__axiom_set_new_16
)))

;; Function-Axioms vstd::set::axiom_set_insert_same
(declare-fun ens%vstd!set.axiom_set_insert_same. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_same. A& A&. s~2@ a~4@) (vstd!set.impl&%0.contains.?
     A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2@ a~4@) a~4@
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_same. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_insert_same._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_insert_same._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a~4$) a~4$)
   )
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$
      a~4$
     ) a~4$
   ))
   :qid
   user_vstd__set__axiom_set_insert_same_17
   :skolemid
   skolem_user_vstd__set__axiom_set_insert_same_17
)))

;; Function-Specs vstd::set::axiom_set_insert_different
(declare-fun req%vstd!set.axiom_set_insert_different. (Type Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%7 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a1~4@ Poly) (a2~6@ Poly)) (!
   (= (req%vstd!set.axiom_set_insert_different. A& A&. s~2@ a1~4@ a2~6@) (=>
     %%global_location_label%%7
     (not (= a1~4@ a2~6@))
   ))
   :pattern ((req%vstd!set.axiom_set_insert_different. A& A&. s~2@ a1~4@ a2~6@))
   :qid
   internal_req__vstd!set.axiom_set_insert_different._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_insert_different._definition
)))

;; Function-Axioms vstd::set::axiom_set_insert_different
(declare-fun ens%vstd!set.axiom_set_insert_different. (Type Type Poly Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a1~4@ Poly) (a2~6@ Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_different. A& A&. s~2@ a1~4@ a2~6@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2@ a2~6@) a1~4@
     ) (vstd!set.impl&%0.contains.? A& A&. s~2@ a1~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_different. A& A&. s~2@ a1~4@ a2~6@))
   :qid
   internal_ens__vstd!set.axiom_set_insert_different._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_insert_different._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a1~4$ Poly) (a2~6$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a1~4$ A&)
     (has_type a2~6$ A&)
    )
    (=>
     (not (= a1~4$ a2~6$))
     (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a2~6$)
       a1~4$
      ) (vstd!set.impl&%0.contains.? A& A&. s~2$ a1~4$)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$
      a2~6$
     ) a1~4$
   ))
   :qid
   user_vstd__set__axiom_set_insert_different_18
   :skolemid
   skolem_user_vstd__set__axiom_set_insert_different_18
)))

;; Function-Axioms vstd::set::axiom_set_remove_same
(declare-fun ens%vstd!set.axiom_set_remove_same. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_same. A& A&. s~2@ a~4@) (not (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2@ a~4@) a~4@
   )))
   :pattern ((ens%vstd!set.axiom_set_remove_same. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_remove_same._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_remove_same._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (not (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$ a~4$)
      a~4$
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$
      a~4$
     ) a~4$
   ))
   :qid
   user_vstd__set__axiom_set_remove_same_19
   :skolemid
   skolem_user_vstd__set__axiom_set_remove_same_19
)))

;; Function-Specs vstd::set::axiom_set_remove_different
(declare-fun req%vstd!set.axiom_set_remove_different. (Type Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a1~4@ Poly) (a2~6@ Poly)) (!
   (= (req%vstd!set.axiom_set_remove_different. A& A&. s~2@ a1~4@ a2~6@) (=>
     %%global_location_label%%8
     (not (= a1~4@ a2~6@))
   ))
   :pattern ((req%vstd!set.axiom_set_remove_different. A& A&. s~2@ a1~4@ a2~6@))
   :qid
   internal_req__vstd!set.axiom_set_remove_different._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_remove_different._definition
)))

;; Function-Axioms vstd::set::axiom_set_remove_different
(declare-fun ens%vstd!set.axiom_set_remove_different. (Type Type Poly Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a1~4@ Poly) (a2~6@ Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_different. A& A&. s~2@ a1~4@ a2~6@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2@ a2~6@) a1~4@
     ) (vstd!set.impl&%0.contains.? A& A&. s~2@ a1~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_remove_different. A& A&. s~2@ a1~4@ a2~6@))
   :qid
   internal_ens__vstd!set.axiom_set_remove_different._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_remove_different._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a1~4$ Poly) (a2~6$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a1~4$ A&)
     (has_type a2~6$ A&)
    )
    (=>
     (not (= a1~4$ a2~6$))
     (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$ a2~6$)
       a1~4$
      ) (vstd!set.impl&%0.contains.? A& A&. s~2$ a1~4$)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$
      a2~6$
     ) a1~4$
   ))
   :qid
   user_vstd__set__axiom_set_remove_different_20
   :skolemid
   skolem_user_vstd__set__axiom_set_remove_different_20
)))

;; Function-Axioms vstd::set::axiom_set_union
(declare-fun ens%vstd!set.axiom_set_union. (Type Type Poly Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly) (a~6@ Poly)) (!
   (= (ens%vstd!set.axiom_set_union. A& A&. s1~2@ s2~4@ a~6@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2@ s2~4@) a~6@
     ) (or
      (vstd!set.impl&%0.contains.? A& A&. s1~2@ a~6@)
      (vstd!set.impl&%0.contains.? A& A&. s2~4@ a~6@)
   )))
   :pattern ((ens%vstd!set.axiom_set_union. A& A&. s1~2@ s2~4@ a~6@))
   :qid
   internal_ens__vstd!set.axiom_set_union._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_union._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly) (a~6$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
     (has_type a~6$ A&)
    )
    (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2$ s2~4$)
      a~6$
     ) (or
      (vstd!set.impl&%0.contains.? A& A&. s1~2$ a~6$)
      (vstd!set.impl&%0.contains.? A& A&. s2~4$ a~6$)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2$
      s2~4$
     ) a~6$
   ))
   :qid
   user_vstd__set__axiom_set_union_21
   :skolemid
   skolem_user_vstd__set__axiom_set_union_21
)))

;; Function-Axioms vstd::set::axiom_set_intersect
(declare-fun ens%vstd!set.axiom_set_intersect. (Type Type Poly Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly) (a~6@ Poly)) (!
   (= (ens%vstd!set.axiom_set_intersect. A& A&. s1~2@ s2~4@ a~6@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2@ s2~4@) a~6@
     ) (and
      (vstd!set.impl&%0.contains.? A& A&. s1~2@ a~6@)
      (vstd!set.impl&%0.contains.? A& A&. s2~4@ a~6@)
   )))
   :pattern ((ens%vstd!set.axiom_set_intersect. A& A&. s1~2@ s2~4@ a~6@))
   :qid
   internal_ens__vstd!set.axiom_set_intersect._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_intersect._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly) (a~6$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
     (has_type a~6$ A&)
    )
    (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2$ s2~4$)
      a~6$
     ) (and
      (vstd!set.impl&%0.contains.? A& A&. s1~2$ a~6$)
      (vstd!set.impl&%0.contains.? A& A&. s2~4$ a~6$)
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2$
      s2~4$
     ) a~6$
   ))
   :qid
   user_vstd__set__axiom_set_intersect_22
   :skolemid
   skolem_user_vstd__set__axiom_set_intersect_22
)))

;; Function-Axioms vstd::set::axiom_set_difference
(declare-fun ens%vstd!set.axiom_set_difference. (Type Type Poly Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly) (a~6@ Poly)) (!
   (= (ens%vstd!set.axiom_set_difference. A& A&. s1~2@ s2~4@ a~6@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.difference.? A& A&. s1~2@ s2~4@) a~6@
     ) (and
      (vstd!set.impl&%0.contains.? A& A&. s1~2@ a~6@)
      (not (vstd!set.impl&%0.contains.? A& A&. s2~4@ a~6@))
   )))
   :pattern ((ens%vstd!set.axiom_set_difference. A& A&. s1~2@ s2~4@ a~6@))
   :qid
   internal_ens__vstd!set.axiom_set_difference._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_difference._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly) (a~6$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
     (has_type a~6$ A&)
    )
    (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.difference.? A& A&. s1~2$ s2~4$)
      a~6$
     ) (and
      (vstd!set.impl&%0.contains.? A& A&. s1~2$ a~6$)
      (not (vstd!set.impl&%0.contains.? A& A&. s2~4$ a~6$))
   )))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.difference.? A& A&.
      s1~2$ s2~4$
     ) a~6$
   ))
   :qid
   user_vstd__set__axiom_set_difference_23
   :skolemid
   skolem_user_vstd__set__axiom_set_difference_23
)))

;; Function-Axioms vstd::set::axiom_set_complement
(declare-fun ens%vstd!set.axiom_set_complement. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_complement. A& A&. s~2@ a~4@) (= (vstd!set.impl&%0.contains.?
      A& A&. (vstd!set.impl&%0.complement.? A& A&. s~2@) a~4@
     ) (not (vstd!set.impl&%0.contains.? A& A&. s~2@ a~4@))
   ))
   :pattern ((ens%vstd!set.axiom_set_complement. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_complement._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_complement._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (= (vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.complement.? A& A&. s~2$)
      a~4$
     ) (not (vstd!set.impl&%0.contains.? A& A&. s~2$ a~4$))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. (vstd!set.impl&%0.complement.? A& A&.
      s~2$
     ) a~4$
   ))
   :qid
   user_vstd__set__axiom_set_complement_24
   :skolemid
   skolem_user_vstd__set__axiom_set_complement_24
)))

;; Function-Axioms vstd::set::axiom_set_ext_equal
(declare-fun ens%vstd!set.axiom_set_ext_equal. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_ext_equal. A& A&. s1~2@ s2~4@) (= (ext_eq false (TYPE%vstd!set.Set.
       A&
      ) (TYPE%vstd!set.Set. A&.) s1~2@ s2~4@
     ) (forall ((a~32$ Poly)) (!
       (=>
        (has_type a~32$ A&)
        (= (vstd!set.impl&%0.contains.? A& A&. s1~2@ a~32$) (vstd!set.impl&%0.contains.? A&
          A&. s2~4@ a~32$
       )))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. s1~2@ a~32$))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. s2~4@ a~32$))
       :qid
       user_vstd__set__axiom_set_ext_equal_25
       :skolemid
       skolem_user_vstd__set__axiom_set_ext_equal_25
   ))))
   :pattern ((ens%vstd!set.axiom_set_ext_equal. A& A&. s1~2@ s2~4@))
   :qid
   internal_ens__vstd!set.axiom_set_ext_equal._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_ext_equal._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
    )
    (= (ext_eq false (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2$ s2~4$) (forall
      ((a~32$ Poly)) (!
       (=>
        (has_type a~32$ A&)
        (= (vstd!set.impl&%0.contains.? A& A&. s1~2$ a~32$) (vstd!set.impl&%0.contains.? A&
          A&. s2~4$ a~32$
       )))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. s1~2$ a~32$))
       :pattern ((vstd!set.impl&%0.contains.? A& A&. s2~4$ a~32$))
       :qid
       user_vstd__set__axiom_set_ext_equal_26
       :skolemid
       skolem_user_vstd__set__axiom_set_ext_equal_26
   ))))
   :pattern ((ext_eq false (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2$ s2~4$))
   :qid
   user_vstd__set__axiom_set_ext_equal_27
   :skolemid
   skolem_user_vstd__set__axiom_set_ext_equal_27
)))

;; Function-Axioms vstd::set::axiom_set_ext_equal_deep
(declare-fun ens%vstd!set.axiom_set_ext_equal_deep. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_ext_equal_deep. A& A&. s1~2@ s2~4@) (= (ext_eq true (TYPE%vstd!set.Set.
       A&
      ) (TYPE%vstd!set.Set. A&.) s1~2@ s2~4@
     ) (ext_eq false (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2@ s2~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_ext_equal_deep. A& A&. s1~2@ s2~4@))
   :qid
   internal_ens__vstd!set.axiom_set_ext_equal_deep._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_ext_equal_deep._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
    )
    (= (ext_eq true (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2$ s2~4$) (ext_eq
      false (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2$ s2~4$
   )))
   :pattern ((ext_eq true (TYPE%vstd!set.Set. A&) (TYPE%vstd!set.Set. A&.) s1~2$ s2~4$))
   :qid
   user_vstd__set__axiom_set_ext_equal_deep_28
   :skolemid
   skolem_user_vstd__set__axiom_set_ext_equal_deep_28
)))

;; Function-Axioms vstd::set::axiom_mk_map_domain
(declare-fun ens%vstd!set.axiom_mk_map_domain. (Type Type Type Type Poly %%Function%%)
 Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (s~2@ Poly) (f~4@ %%Function%%))
  (!
   (= (ens%vstd!set.axiom_mk_map_domain. K& K&. V& V&. s~2@ f~4@) (= (vstd!map.impl&%0.dom.?
      K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&. V& V&. (TYPE%fun%1. K& V&) (TYPE%fun%1.
        K&. V&.
       ) s~2@ (Poly%fun%1. f~4@)
      )
     ) s~2@
   ))
   :pattern ((ens%vstd!set.axiom_mk_map_domain. K& K&. V& V&. s~2@ f~4@))
   :qid
   internal_ens__vstd!set.axiom_mk_map_domain._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_mk_map_domain._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (s~2$ Poly) (f~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. K&))
     (has_type f~4$ (TYPE%fun%1. K& V&))
    )
    (= (vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&. V& V&. (TYPE%fun%1.
        K& V&
       ) (TYPE%fun%1. K&. V&.) s~2$ f~4$
      )
     ) s~2$
   ))
   :pattern ((vstd!map.impl&%0.dom.? K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&. V&
      V&. (TYPE%fun%1. K& V&) (TYPE%fun%1. K&. V&.) s~2$ f~4$
   )))
   :qid
   user_vstd__set__axiom_mk_map_domain_29
   :skolemid
   skolem_user_vstd__set__axiom_mk_map_domain_29
)))

;; Function-Specs vstd::set::axiom_mk_map_index
(declare-fun req%vstd!set.axiom_mk_map_index. (Type Type Type Type Poly %%Function%%
  Poly
 ) Bool
)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (s~2@ Poly) (f~4@ %%Function%%)
   (key~6@ Poly)
  ) (!
   (= (req%vstd!set.axiom_mk_map_index. K& K&. V& V&. s~2@ f~4@ key~6@) (=>
     %%global_location_label%%9
     (vstd!set.impl&%0.contains.? K& K&. s~2@ key~6@)
   ))
   :pattern ((req%vstd!set.axiom_mk_map_index. K& K&. V& V&. s~2@ f~4@ key~6@))
   :qid
   internal_req__vstd!set.axiom_mk_map_index._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_mk_map_index._definition
)))

;; Function-Axioms vstd::set::axiom_mk_map_index
(declare-fun ens%vstd!set.axiom_mk_map_index. (Type Type Type Type Poly %%Function%%
  Poly
 ) Bool
)
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (s~2@ Poly) (f~4@ %%Function%%)
   (key~6@ Poly)
  ) (!
   (= (ens%vstd!set.axiom_mk_map_index. K& K&. V& V&. s~2@ f~4@ key~6@) (= (vstd!map.impl&%0.index.?
      K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&. V& V&. (TYPE%fun%1. K& V&) (TYPE%fun%1.
        K&. V&.
       ) s~2@ (Poly%fun%1. f~4@)
      ) key~6@
     ) (%%apply%%0 f~4@ key~6@)
   ))
   :pattern ((ens%vstd!set.axiom_mk_map_index. K& K&. V& V&. s~2@ f~4@ key~6@))
   :qid
   internal_ens__vstd!set.axiom_mk_map_index._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_mk_map_index._definition
)))
(assert
 (forall ((K& Type) (K&. Type) (V& Type) (V&. Type) (s~2$ Poly) (f~4$ Poly) (key~6$ Poly))
  (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. K&))
     (has_type f~4$ (TYPE%fun%1. K& V&))
     (has_type key~6$ K&)
    )
    (=>
     (vstd!set.impl&%0.contains.? K& K&. s~2$ key~6$)
     (= (vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&. V& V&.
        (TYPE%fun%1. K& V&) (TYPE%fun%1. K&. V&.) s~2$ f~4$
       ) key~6$
      ) (%%apply%%0 (%Poly%fun%1. f~4$) key~6$)
   )))
   :pattern ((vstd!map.impl&%0.index.? K& K&. V& V&. (vstd!set.impl&%0.mk_map.? K& K&.
      V& V&. (TYPE%fun%1. K& V&) (TYPE%fun%1. K&. V&.) s~2$ f~4$
     ) key~6$
   ))
   :qid
   user_vstd__set__axiom_mk_map_index_30
   :skolemid
   skolem_user_vstd__set__axiom_mk_map_index_30
)))

;; Function-Axioms vstd::set::axiom_set_empty_finite
(declare-fun ens%vstd!set.axiom_set_empty_finite. (Type Type) Bool)
(assert
 (forall ((A& Type) (A&. Type)) (!
   (= (ens%vstd!set.axiom_set_empty_finite. A& A&.) (vstd!set.impl&%0.finite.? A& A&.
     (vstd!set.impl&%0.empty.? A& A&.)
   ))
   :pattern ((ens%vstd!set.axiom_set_empty_finite. A& A&.))
   :qid
   internal_ens__vstd!set.axiom_set_empty_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_empty_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type)) (!
   (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.empty.? A& A&.))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.empty.? A& A&.)))
   :qid
   user_vstd__set__axiom_set_empty_finite_31
   :skolemid
   skolem_user_vstd__set__axiom_set_empty_finite_31
)))

;; Function-Specs vstd::set::axiom_set_insert_finite
(declare-fun req%vstd!set.axiom_set_insert_finite. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%10 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_insert_finite. A& A&. s~2@ a~4@) (=>
     %%global_location_label%%10
     (vstd!set.impl&%0.finite.? A& A&. s~2@)
   ))
   :pattern ((req%vstd!set.axiom_set_insert_finite. A& A&. s~2@ a~4@))
   :qid
   internal_req__vstd!set.axiom_set_insert_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_insert_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_insert_finite
(declare-fun ens%vstd!set.axiom_set_insert_finite. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_finite. A& A&. s~2@ a~4@) (vstd!set.impl&%0.finite.?
     A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2@ a~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_insert_finite. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_insert_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_insert_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A& A&. s~2$)
     (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a~4$))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a~4$)))
   :qid
   user_vstd__set__axiom_set_insert_finite_32
   :skolemid
   skolem_user_vstd__set__axiom_set_insert_finite_32
)))

;; Function-Specs vstd::set::axiom_set_remove_finite
(declare-fun req%vstd!set.axiom_set_remove_finite. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%11 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_remove_finite. A& A&. s~2@ a~4@) (=>
     %%global_location_label%%11
     (vstd!set.impl&%0.finite.? A& A&. s~2@)
   ))
   :pattern ((req%vstd!set.axiom_set_remove_finite. A& A&. s~2@ a~4@))
   :qid
   internal_req__vstd!set.axiom_set_remove_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_remove_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_remove_finite
(declare-fun ens%vstd!set.axiom_set_remove_finite. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_finite. A& A&. s~2@ a~4@) (vstd!set.impl&%0.finite.?
     A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2@ a~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_remove_finite. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_remove_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_remove_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A& A&. s~2$)
     (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$ a~4$))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$ a~4$)))
   :qid
   user_vstd__set__axiom_set_remove_finite_33
   :skolemid
   skolem_user_vstd__set__axiom_set_remove_finite_33
)))

;; Function-Specs vstd::set::axiom_set_union_finite
(declare-fun req%vstd!set.axiom_set_union_finite. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%12 Bool)
(declare-const %%global_location_label%%13 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_union_finite. A& A&. s1~2@ s2~4@) (and
     (=>
      %%global_location_label%%12
      (vstd!set.impl&%0.finite.? A& A&. s1~2@)
     )
     (=>
      %%global_location_label%%13
      (vstd!set.impl&%0.finite.? A& A&. s2~4@)
   )))
   :pattern ((req%vstd!set.axiom_set_union_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_req__vstd!set.axiom_set_union_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_union_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_union_finite
(declare-fun ens%vstd!set.axiom_set_union_finite. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_union_finite. A& A&. s1~2@ s2~4@) (vstd!set.impl&%0.finite.?
     A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2@ s2~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_union_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_ens__vstd!set.axiom_set_union_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_union_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
    )
    (=>
     (and
      (vstd!set.impl&%0.finite.? A& A&. s1~2$)
      (vstd!set.impl&%0.finite.? A& A&. s2~4$)
     )
     (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2$ s2~4$))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.union.? A& A&. s1~2$ s2~4$)))
   :qid
   user_vstd__set__axiom_set_union_finite_34
   :skolemid
   skolem_user_vstd__set__axiom_set_union_finite_34
)))

;; Function-Specs vstd::set::axiom_set_intersect_finite
(declare-fun req%vstd!set.axiom_set_intersect_finite. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%14 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_intersect_finite. A& A&. s1~2@ s2~4@) (=>
     %%global_location_label%%14
     (or
      (vstd!set.impl&%0.finite.? A& A&. s1~2@)
      (vstd!set.impl&%0.finite.? A& A&. s2~4@)
   )))
   :pattern ((req%vstd!set.axiom_set_intersect_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_req__vstd!set.axiom_set_intersect_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_intersect_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_intersect_finite
(declare-fun ens%vstd!set.axiom_set_intersect_finite. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_intersect_finite. A& A&. s1~2@ s2~4@) (vstd!set.impl&%0.finite.?
     A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2@ s2~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_intersect_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_ens__vstd!set.axiom_set_intersect_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_intersect_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
    )
    (=>
     (or
      (vstd!set.impl&%0.finite.? A& A&. s1~2$)
      (vstd!set.impl&%0.finite.? A& A&. s2~4$)
     )
     (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2$ s2~4$))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.intersect.? A& A&. s1~2$
      s2~4$
   )))
   :qid
   user_vstd__set__axiom_set_intersect_finite_35
   :skolemid
   skolem_user_vstd__set__axiom_set_intersect_finite_35
)))

;; Function-Specs vstd::set::axiom_set_difference_finite
(declare-fun req%vstd!set.axiom_set_difference_finite. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%15 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_difference_finite. A& A&. s1~2@ s2~4@) (=>
     %%global_location_label%%15
     (vstd!set.impl&%0.finite.? A& A&. s1~2@)
   ))
   :pattern ((req%vstd!set.axiom_set_difference_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_req__vstd!set.axiom_set_difference_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_difference_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_difference_finite
(declare-fun ens%vstd!set.axiom_set_difference_finite. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s1~2@ Poly) (s2~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_difference_finite. A& A&. s1~2@ s2~4@) (vstd!set.impl&%0.finite.?
     A& A&. (vstd!set.impl&%0.difference.? A& A&. s1~2@ s2~4@)
   ))
   :pattern ((ens%vstd!set.axiom_set_difference_finite. A& A&. s1~2@ s2~4@))
   :qid
   internal_ens__vstd!set.axiom_set_difference_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_difference_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s1~2$ Poly) (s2~4$ Poly)) (!
   (=>
    (and
     (has_type s1~2$ (TYPE%vstd!set.Set. A&))
     (has_type s2~4$ (TYPE%vstd!set.Set. A&))
    )
    (=>
     (vstd!set.impl&%0.finite.? A& A&. s1~2$)
     (vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.difference.? A& A&. s1~2$ s2~4$))
   ))
   :pattern ((vstd!set.impl&%0.finite.? A& A&. (vstd!set.impl&%0.difference.? A& A&. s1~2$
      s2~4$
   )))
   :qid
   user_vstd__set__axiom_set_difference_finite_36
   :skolemid
   skolem_user_vstd__set__axiom_set_difference_finite_36
)))

;; Function-Specs vstd::set::axiom_set_choose_finite
(declare-fun req%vstd!set.axiom_set_choose_finite. (Type Type Poly) Bool)
(declare-const %%global_location_label%%16 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly)) (!
   (= (req%vstd!set.axiom_set_choose_finite. A& A&. s~2@) (=>
     %%global_location_label%%16
     (not (vstd!set.impl&%0.finite.? A& A&. s~2@))
   ))
   :pattern ((req%vstd!set.axiom_set_choose_finite. A& A&. s~2@))
   :qid
   internal_req__vstd!set.axiom_set_choose_finite._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_choose_finite._definition
)))

;; Function-Axioms vstd::set::axiom_set_choose_finite
(declare-fun ens%vstd!set.axiom_set_choose_finite. (Type Type Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly)) (!
   (= (ens%vstd!set.axiom_set_choose_finite. A& A&. s~2@) (vstd!set.impl&%0.contains.?
     A& A&. s~2@ (vstd!set.impl&%0.choose.? A& A&. s~2@)
   ))
   :pattern ((ens%vstd!set.axiom_set_choose_finite. A& A&. s~2@))
   :qid
   internal_ens__vstd!set.axiom_set_choose_finite._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_choose_finite._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly)) (!
   (=>
    (has_type s~2$ (TYPE%vstd!set.Set. A&))
    (=>
     (not (vstd!set.impl&%0.finite.? A& A&. s~2$))
     (vstd!set.impl&%0.contains.? A& A&. s~2$ (vstd!set.impl&%0.choose.? A& A&. s~2$))
   ))
   :pattern ((vstd!set.impl&%0.contains.? A& A&. s~2$ (vstd!set.impl&%0.choose.? A& A&.
      s~2$
   )))
   :qid
   user_vstd__set__axiom_set_choose_finite_37
   :skolemid
   skolem_user_vstd__set__axiom_set_choose_finite_37
)))

;; Function-Axioms vstd::set::axiom_set_empty_len
(declare-fun ens%vstd!set.axiom_set_empty_len. (Type Type) Bool)
(assert
 (forall ((A& Type) (A&. Type)) (!
   (= (ens%vstd!set.axiom_set_empty_len. A& A&.) (= (vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.empty.?
       A& A&.
      )
     ) 0
   ))
   :pattern ((ens%vstd!set.axiom_set_empty_len. A& A&.))
   :qid
   internal_ens__vstd!set.axiom_set_empty_len._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_empty_len._definition
)))
(assert
 (forall ((A& Type) (A&. Type)) (!
   (= (vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.empty.? A& A&.)) 0)
   :pattern ((vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.empty.? A& A&.)))
   :qid
   user_vstd__set__axiom_set_empty_len_38
   :skolemid
   skolem_user_vstd__set__axiom_set_empty_len_38
)))

;; Function-Specs vstd::set::axiom_set_insert_len
(declare-fun req%vstd!set.axiom_set_insert_len. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%17 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_insert_len. A& A&. s~2@ a~4@) (=>
     %%global_location_label%%17
     (vstd!set.impl&%0.finite.? A& A&. s~2@)
   ))
   :pattern ((req%vstd!set.axiom_set_insert_len. A& A&. s~2@ a~4@))
   :qid
   internal_req__vstd!set.axiom_set_insert_len._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_insert_len._definition
)))

;; Function-Axioms vstd::set::axiom_set_insert_len
(declare-fun ens%vstd!set.axiom_set_insert_len. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_insert_len. A& A&. s~2@ a~4@) (= (vstd!set.impl&%0.len.?
      A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2@ a~4@)
     ) (+ (vstd!set.impl&%0.len.? A& A&. s~2@) (ite
       (vstd!set.impl&%0.contains.? A& A&. s~2@ a~4@)
       0
       1
   ))))
   :pattern ((ens%vstd!set.axiom_set_insert_len. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_insert_len._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_insert_len._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A& A&. s~2$)
     (= (vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a~4$)) (+
       (vstd!set.impl&%0.len.? A& A&. s~2$) (ite
        (vstd!set.impl&%0.contains.? A& A&. s~2$ a~4$)
        0
        1
   )))))
   :pattern ((vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.insert.? A& A&. s~2$ a~4$)))
   :qid
   user_vstd__set__axiom_set_insert_len_39
   :skolemid
   skolem_user_vstd__set__axiom_set_insert_len_39
)))

;; Function-Specs vstd::set::axiom_set_remove_len
(declare-fun req%vstd!set.axiom_set_remove_len. (Type Type Poly Poly) Bool)
(declare-const %%global_location_label%%18 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (req%vstd!set.axiom_set_remove_len. A& A&. s~2@ a~4@) (=>
     %%global_location_label%%18
     (vstd!set.impl&%0.finite.? A& A&. s~2@)
   ))
   :pattern ((req%vstd!set.axiom_set_remove_len. A& A&. s~2@ a~4@))
   :qid
   internal_req__vstd!set.axiom_set_remove_len._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_remove_len._definition
)))

;; Function-Axioms vstd::set::axiom_set_remove_len
(declare-fun ens%vstd!set.axiom_set_remove_len. (Type Type Poly Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly) (a~4@ Poly)) (!
   (= (ens%vstd!set.axiom_set_remove_len. A& A&. s~2@ a~4@) (= (vstd!set.impl&%0.len.?
      A& A&. s~2@
     ) (+ (vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2@ a~4@))
      (ite
       (vstd!set.impl&%0.contains.? A& A&. s~2@ a~4@)
       1
       0
   ))))
   :pattern ((ens%vstd!set.axiom_set_remove_len. A& A&. s~2@ a~4@))
   :qid
   internal_ens__vstd!set.axiom_set_remove_len._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_remove_len._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly) (a~4$ Poly)) (!
   (=>
    (and
     (has_type s~2$ (TYPE%vstd!set.Set. A&))
     (has_type a~4$ A&)
    )
    (=>
     (vstd!set.impl&%0.finite.? A& A&. s~2$)
     (= (vstd!set.impl&%0.len.? A& A&. s~2$) (+ (vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.remove.?
         A& A&. s~2$ a~4$
        )
       ) (ite
        (vstd!set.impl&%0.contains.? A& A&. s~2$ a~4$)
        1
        0
   )))))
   :pattern ((vstd!set.impl&%0.len.? A& A&. (vstd!set.impl&%0.remove.? A& A&. s~2$ a~4$)))
   :qid
   user_vstd__set__axiom_set_remove_len_40
   :skolemid
   skolem_user_vstd__set__axiom_set_remove_len_40
)))

;; Function-Specs vstd::set::axiom_set_choose_len
(declare-fun req%vstd!set.axiom_set_choose_len. (Type Type Poly) Bool)
(declare-const %%global_location_label%%19 Bool)
(declare-const %%global_location_label%%20 Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly)) (!
   (= (req%vstd!set.axiom_set_choose_len. A& A&. s~2@) (and
     (=>
      %%global_location_label%%19
      (vstd!set.impl&%0.finite.? A& A&. s~2@)
     )
     (=>
      %%global_location_label%%20
      (not (= (vstd!set.impl&%0.len.? A& A&. s~2@) 0))
   )))
   :pattern ((req%vstd!set.axiom_set_choose_len. A& A&. s~2@))
   :qid
   internal_req__vstd!set.axiom_set_choose_len._definition
   :skolemid
   skolem_internal_req__vstd!set.axiom_set_choose_len._definition
)))

;; Function-Axioms vstd::set::axiom_set_choose_len
(declare-fun ens%vstd!set.axiom_set_choose_len. (Type Type Poly) Bool)
(assert
 (forall ((A& Type) (A&. Type) (s~2@ Poly)) (!
   (= (ens%vstd!set.axiom_set_choose_len. A& A&. s~2@) (vstd!set.impl&%0.contains.? A&
     A&. s~2@ (vstd!set.impl&%0.choose.? A& A&. s~2@)
   ))
   :pattern ((ens%vstd!set.axiom_set_choose_len. A& A&. s~2@))
   :qid
   internal_ens__vstd!set.axiom_set_choose_len._definition
   :skolemid
   skolem_internal_ens__vstd!set.axiom_set_choose_len._definition
)))
(assert
 (forall ((A& Type) (A&. Type) (s~2$ Poly)) (!
   (=>
    (has_type s~2$ (TYPE%vstd!set.Set. A&))
    (=>
     (and
      (vstd!set.impl&%0.finite.? A& A&. s~2$)
      (not (= (vstd!set.impl&%0.len.? A& A&. s~2$) 0))
     )
     (vstd!set.impl&%0.contains.? A& A&. s~2$ (vstd!set.impl&%0.choose.? A& A&. s~2$))
   ))
   :pattern ((vstd!set.impl&%0.len.? A& A&. s~2$) (vstd!set.impl&%0.contains.? A& A&.
     s~2$ (vstd!set.impl&%0.choose.? A& A&. s~2$)
   ))
   :qid
   user_vstd__set__axiom_set_choose_len_41
   :skolemid
   skolem_user_vstd__set__axiom_set_choose_len_41
)))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::contains
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains.)
  (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.contains.? self~2@ lsn~4@) (and
      (<= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
         self~2@
        )
       ) (%I lsn~4@)
      )
      (< (%I lsn~4@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end
        (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. self~2@)
    ))))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.contains.? self~2@ lsn~4@))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.contains.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.contains.?_definition
))))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::contains_exactly
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.)
  (forall ((self~2@ Poly) (lsns~4@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.? self~2@ lsns~4@)
     (forall ((lsn~12$ Poly)) (!
       (=>
        (has_type lsn~12$ NAT)
        (= (vstd!set.impl&%0.contains.? NAT NAT lsns~4@ lsn~12$) (bundle!coordination_layer.MsgHistory_v.impl&%0.contains.?
          self~2@ lsn~12$
       )))
       :pattern ((vstd!set.impl&%0.contains.? NAT NAT lsns~4@ lsn~12$))
       :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.contains.? self~2@ lsn~12$))
       :qid
       user_bundle__coordination_layer__MsgHistory_v__impl&%0__contains_exactly_42
       :skolemid
       skolem_user_bundle__coordination_layer__MsgHistory_v__impl&%0__contains_exactly_42
    )))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.? self~2@
      lsns~4@
    ))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.contains_exactly.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.contains_exactly.?_definition
))))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::wf
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.wf.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.wf.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.wf.? self~2@) (and
      (<= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
         self~2@
        )
       ) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
         self~2@
      )))
      (bundle!coordination_layer.MsgHistory_v.impl&%0.contains_exactly.? self~2@ (vstd!map.impl&%0.dom.?
        NAT NAT TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage. TYPE%bundle!coordination_layer.MsgHistory_v.KeyedMessage.
        (Poly%vstd!map.Map<nat./bundle!coordination_layer.MsgHistory_v.KeyedMessage.>. (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/msgs
          (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. self~2@)
    ))))))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.wf.? self~2@))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.wf.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.wf.?_definition
))))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::can_follow
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.)
  (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.? self~2@ lsn~4@) (=
      (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
        self~2@
       )
      ) (%I lsn~4@)
    ))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.? self~2@ lsn~4@))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.can_follow.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.can_follow.?_definition
))))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::can_concat
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.)
  (forall ((self~2@ Poly) (other~4@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.? self~2@ other~4@)
     (bundle!coordination_layer.MsgHistory_v.impl&%0.can_follow.? other~4@ (I (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end
        (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. self~2@)
    ))))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.? self~2@ other~4@))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.can_concat.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.can_concat.?_definition
))))

;; Function-Axioms bundle::coordination_layer::MsgHistory_v::impl&%0::is_empty
(assert
 (fuel_bool_default fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.? self~2@) (= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
       (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. self~2@)
      ) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
        self~2@
    ))))
    :pattern ((bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.? self~2@))
    :qid
    internal_bundle!coordination_layer.MsgHistory_v.impl&__0.is_empty.?_definition
    :skolemid
    skolem_internal_bundle!coordination_layer.MsgHistory_v.impl&__0.is_empty.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%0::wf
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%0.wf.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%0.wf.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%0.wf.? self~2@) (and
      (bundle!coordination_layer.MsgHistory_v.impl&%0.wf.? (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
        (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
          self~2@
      ))))
      (not (bundle!coordination_layer.MsgHistory_v.impl&%0.is_empty.? (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
         (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
           self~2@
    )))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%0.wf.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__0.wf.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__0.wf.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::entries_wf
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.entries_wf.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.entries_wf.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? self~2@) (forall ((addr~10$ Poly))
      (!
       (=>
        (has_type addr~10$ TYPE%bundle!disk.GenericDisk_v.Address.)
        (=>
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
           )))
          ) addr~10$
         )
         (bundle!journal.LinkedJournal_v.impl&%0.wf.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
            ))
           ) addr~10$
       ))))
       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
          )))
         ) addr~10$
       ))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__entries_wf_43
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__entries_wf_43
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.entries_wf.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.entries_wf.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::is_nondangling_pointer
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? self~2@ ptr~4@)
     (=>
      (is-vstd!option.Option./Some (%Poly%vstd!option.Option. ptr~4@))
      (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
       (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
        )))
       ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. ptr~4@))
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? self~2@
      ptr~4@
    ))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.is_nondangling_pointer.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.is_nondangling_pointer.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%0::cropped_prior
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.)
  (forall ((self~2@ Poly) (boundary_lsn~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? self~2@ boundary_lsn~4@)
     (ite
      (< (%I boundary_lsn~4@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
        (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
          (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
            self~2@
      ))))))
      (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/prior_rec (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
        self~2@
      ))
      vstd!option.Option./None
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? self~2@ boundary_lsn~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__0.cropped_prior.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__0.cropped_prior.?_definition
))))
(assert
 (forall ((self~2@ Poly) (boundary_lsn~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
     (has_type boundary_lsn~4@ NAT)
    )
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
       self~2@ boundary_lsn~4@
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? self~2@ boundary_lsn~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__0.cropped_prior.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__0.cropped_prior.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::nondangling_pointers
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? self~2@) (forall
      ((addr~10$ Poly)) (!
       (=>
        (has_type addr~10$ TYPE%bundle!disk.GenericDisk_v.Address.)
        (=>
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
           )))
          ) addr~10$
         )
         (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? self~2@ (Poly%vstd!option.Option.
           (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
              ))
             ) addr~10$
            ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
               self~2@
       ))))))))
       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
          )))
         ) addr~10$
       ))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__nondangling_pointers_44
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__nondangling_pointers_44
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.nondangling_pointers.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.nondangling_pointers.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::this_block_can_concat
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.)
  (forall ((self~2@ Poly) (addr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.? self~2@ addr~4@)
     (let
      ((head~14$ (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (vstd!map.impl&%0.index.?
          TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
           ))
          ) addr~4@
      ))))
      (let
       ((next_ptr~24$ (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (Poly%bundle!journal.LinkedJournal_v.JournalRecord.
           head~14$
          ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
       ))))))
       (=>
        (is-vstd!option.Option./Some next_ptr~24$)
        (bundle!coordination_layer.MsgHistory_v.impl&%0.can_concat.? (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
          (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
            (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
              ))
             ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                next_ptr~24$
          ))))))
         ) (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
           (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%bundle!journal.LinkedJournal_v.JournalRecord.
             head~14$
    )))))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.? self~2@ addr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.this_block_can_concat.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.this_block_can_concat.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::blocks_can_concat
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat. (Poly)
 Bool
)
(declare-const %%global_location_label%%21 Bool)
(declare-const %%global_location_label%%22 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat. self~2@) (and
     (=>
      %%global_location_label%%21
      (bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? self~2@)
     )
     (=>
      %%global_location_label%%22
      (bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? self~2@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat. self~2@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.blocks_can_concat._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.blocks_can_concat._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::blocks_can_concat
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.? self~2@) (forall ((addr~25$
        Poly
       )
      ) (!
       (=>
        (has_type addr~25$ TYPE%bundle!disk.GenericDisk_v.Address.)
        (=>
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
           )))
          ) addr~25$
         )
         (bundle!journal.LinkedJournal_v.impl&%1.this_block_can_concat.? self~2@ addr~25$)
       ))
       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
          )))
         ) addr~25$
       ))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__blocks_can_concat_45
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__blocks_can_concat_45
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.blocks_can_concat.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.blocks_can_concat.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%0::has_link
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%0.has_link.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%0.has_link.)
  (forall ((self~2@ Poly) (boundary_lsn~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%0.has_link.? self~2@ boundary_lsn~4@) (=>
      (< (%I boundary_lsn~4@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start
        (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
          (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
            self~2@
      ))))))
      (is-vstd!option.Option./Some (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
        self~2@ boundary_lsn~4@
    ))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%0.has_link.? self~2@ boundary_lsn~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__0.has_link.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__0.has_link.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::blocks_each_have_link
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.? self~2@) (forall
      ((addr~10$ Poly)) (!
       (=>
        (has_type addr~10$ TYPE%bundle!disk.GenericDisk_v.Address.)
        (=>
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
           )))
          ) addr~10$
         )
         (bundle!journal.LinkedJournal_v.impl&%0.has_link.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
            ))
           ) addr~10$
          ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
       ))))))
       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
          )))
         ) addr~10$
       ))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__blocks_each_have_link_46
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__blocks_each_have_link_46
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.blocks_each_have_link.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.blocks_each_have_link.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::wf
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.wf.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.wf.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@) (and
      (and
       (and
        (bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? self~2@)
        (bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? self~2@)
       )
       (bundle!journal.LinkedJournal_v.impl&%1.blocks_can_concat.? self~2@)
      )
      (bundle!journal.LinkedJournal_v.impl&%1.blocks_each_have_link.? self~2@)
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.wf.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.wf.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::block_in_bounds
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? self~2@ ptr~4@) (and
      (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? self~2@ ptr~4@)
      (=>
       (is-vstd!option.Option./Some (%Poly%vstd!option.Option. ptr~4@))
       (< (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
         )
        ) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
          (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
            (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
              TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 self~2@
               ))
              ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. ptr~4@))
    ))))))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? self~2@ ptr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.block_in_bounds.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.block_in_bounds.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::wf
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.wf.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.wf.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.wf.? self~2@) (and
      (and
       (bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
           self~2@
       ))))
       (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
           self~2@
         ))
        ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
          (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
      ))))
      (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
        ))
       ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
         (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
    )))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.wf.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.wf.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.wf.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::seq_end
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.seq_end. (Poly) Bool)
(declare-const %%global_location_label%%23 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.seq_end. self~2@) (=>
     %%global_location_label%%23
     (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
         self~2@
       ))
      ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
        (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
   )))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.seq_end. self~2@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.seq_end._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.seq_end._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::seq_end
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_end.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_end.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@) (ite
      (is-vstd!option.Option./None (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
        (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
      ))
      (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
        (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
          (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
      ))))
      (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
        (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
          (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
            TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
             (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
               (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
                 (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
             ))))
            ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
               (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
                 self~2@
    )))))))))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.seq_end.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.seq_end.?_definition
))))
(assert
 (forall ((self~2@ Poly)) (!
   (=>
    (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (<= 0 (bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@))
   )
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.seq_end.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.seq_end.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::valid_ranking
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking. (Poly Poly)
 Bool
)
(declare-const %%global_location_label%%24 Bool)
(assert
 (forall ((self~2@ Poly) (ranking~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking. self~2@ ranking~4@)
    (=>
     %%global_location_label%%24
     (bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@)
   ))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking. self~2@ ranking~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.valid_ranking._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.valid_ranking._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::valid_ranking
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.)
  (forall ((self~2@ Poly) (ranking~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? self~2@ ranking~4@) (and
      (vstd!set.impl&%0.subset_of.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
       (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
        )))
       ) (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        NAT NAT ranking~4@
      ))
      (forall ((addr~35$ Poly)) (!
        (=>
         (has_type addr~35$ TYPE%bundle!disk.GenericDisk_v.Address.)
         (=>
          (and
           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
             )))
            ) addr~35$
           )
           (is-vstd!option.Option./Some (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
             (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 self~2@
               ))
              ) addr~35$
             ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
          ))))))
          (< (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             NAT NAT ranking~4@ (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
                  TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                  TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                   (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                     self~2@
                   ))
                  ) addr~35$
                 ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                    self~2@
            ))))))))
           ) (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             NAT NAT ranking~4@ addr~35$
        )))))
        :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
           )))
          ) addr~35$
        ))
        :qid
        user_bundle__journal__LinkedJournal_v__impl&%1__valid_ranking_47
        :skolemid
        skolem_user_bundle__journal__LinkedJournal_v__impl&%1__valid_ranking_47
    ))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? self~2@ ranking~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.valid_ranking.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.valid_ranking.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::acyclic
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.acyclic. (Poly) Bool)
(declare-const %%global_location_label%%25 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.acyclic. self~2@) (=>
     %%global_location_label%%25
     (bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@)
   ))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.acyclic. self~2@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.acyclic._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.acyclic._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::acyclic
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.acyclic.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.acyclic.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@) (exists ((ranking~21$ Poly))
      (!
       (and
        (has_type ranking~21$ (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT))
        (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? self~2@ ranking~21$)
       )
       :pattern ((bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? self~2@ ranking~21$))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__acyclic_48
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__acyclic_48
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.acyclic.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.acyclic.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::decodable
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.decodable.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.decodable.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.decodable.? self~2@) (and
      (bundle!journal.LinkedJournal_v.impl&%2.wf.? self~2@)
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
    ))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.decodable.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.decodable.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.decodable.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::decodable
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.decodable.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.decodable.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@) (and
      (bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@)
      (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? self~2@ ptr~4@)
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.decodable.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.decodable.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::can_crop
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.can_crop. (Poly Poly Poly)
 Bool
)
(declare-const %%global_location_label%%26 Bool)
(declare-const %%global_location_label%%27 Bool)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.can_crop. self~2@ root~4@ depth~6@)
    (and
     (=>
      %%global_location_label%%26
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     )
     (=>
      %%global_location_label%%27
      (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? self~2@ root~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.can_crop. self~2@ root~4@ depth~6@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.can_crop._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.can_crop._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::can_crop
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.can_crop.)
)
(declare-const fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.can_crop. Fuel)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ root~4@ depth~6@
     fuel%@
    ) (bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ root~4@ depth~6@
     zero
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ root~4@ depth~6@
     fuel%@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop._fuel_to_zero_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop._fuel_to_zero_definition
)))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ root~4@ depth~6@
     (succ fuel%@)
    ) (=>
     (< 0 (%I depth~6@))
     (and
      (is-vstd!option.Option./Some (%Poly%vstd!option.Option. root~4@))
      (bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ (Poly%vstd!option.Option.
        (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             self~2@
           ))
          ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. root~4@))
         ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
            self~2@
        ))))
       ) (I (nClip (- (%I depth~6@) 1))) fuel%@
   ))))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.? self~2@ root~4@ depth~6@
     (succ fuel%@)
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop._fuel_to_body_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.can_crop.)
  (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.can_crop.? self~2@ root~4@ depth~6@) (bundle!journal.LinkedJournal_v.impl&%1.rec%can_crop.?
      self~2@ root~4@ depth~6@ (succ fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.can_crop.)
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.can_crop.? self~2@ root~4@ depth~6@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.can_crop.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop. (Poly Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%28 Bool)
(declare-const %%global_location_label%%29 Bool)
(declare-const %%global_location_label%%30 Bool)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop. self~2@ root~4@
     depth~6@
    ) (and
     (=>
      %%global_location_label%%28
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     )
     (=>
      %%global_location_label%%29
      (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? self~2@ root~4@)
     )
     (=>
      %%global_location_label%%30
      (bundle!journal.LinkedJournal_v.impl&%1.can_crop.? self~2@ root~4@ depth~6@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop. self~2@ root~4@
     depth~6@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.)
)
(declare-const fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.
 Fuel
)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@ root~4@
     depth~6@ fuel%@
    ) (bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@ root~4@
     depth~6@ zero
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@
     root~4@ depth~6@ fuel%@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._fuel_to_zero_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._fuel_to_zero_definition
)))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@ root~4@
     depth~6@ (succ fuel%@)
    ) (ite
     (= (%I depth~6@) 0)
     (%Poly%vstd!option.Option. root~4@)
     (bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@ (Poly%vstd!option.Option.
       (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
         TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
          (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
            self~2@
          ))
         ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. root~4@))
        ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
       ))))
      ) (I (nClip (- (%I depth~6@) 1))) fuel%@
   )))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@
     root~4@ depth~6@ (succ fuel%@)
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._fuel_to_body_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.)
  (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? self~2@ root~4@ depth~6@)
     (bundle!journal.LinkedJournal_v.impl&%1.rec%pointer_after_crop.? self~2@ root~4@ depth~6@
      (succ fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.)
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? self~2@ root~4@
      depth~6@
    ))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop.?_definition
))))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (depth~6@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type root~4@ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
     (has_type depth~6@ NAT)
    )
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.?
       self~2@ root~4@ depth~6@
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? self~2@ root~4@
     depth~6@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::seq_start
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_start.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.seq_start.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.seq_start.? self~2@) (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
      (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
    ))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.seq_start.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.seq_start.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.seq_start.?_definition
))))
(assert
 (forall ((self~2@ Poly)) (!
   (=>
    (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (<= 0 (bundle!journal.LinkedJournal_v.impl&%2.seq_start.? self~2@))
   )
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.seq_start.? self~2@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.seq_start.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.seq_start.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::can_discard_to
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to. (Poly Poly)
 Bool
)
(declare-const %%global_location_label%%31 Bool)
(assert
 (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to. self~2@ lsn~4@) (=>
     %%global_location_label%%31
     (bundle!journal.LinkedJournal_v.impl&%2.wf.? self~2@)
   ))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to. self~2@ lsn~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.can_discard_to._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.can_discard_to._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::can_discard_to
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.)
  (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.? self~2@ lsn~4@) (and
      (<= (bundle!journal.LinkedJournal_v.impl&%2.seq_start.? self~2@) (%I lsn~4@))
      (<= (%I lsn~4@) (bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@))
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.? self~2@ lsn~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.can_discard_to.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.can_discard_to.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::the_ranking
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.the_ranking. (Poly) Bool)
(declare-const %%global_location_label%%32 Bool)
(declare-const %%global_location_label%%33 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.the_ranking. self~2@) (and
     (=>
      %%global_location_label%%32
      (bundle!journal.LinkedJournal_v.impl&%1.wf.? self~2@)
     )
     (=>
      %%global_location_label%%33
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.the_ranking. self~2@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.the_ranking._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.the_ranking._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::the_ranking
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.the_ranking.)
)
(declare-fun %%choose%%1 (Type Poly Poly) Poly)
(assert
 (forall ((%%hole%%0 Type) (%%hole%%1 Poly) (%%hole%%2 Poly)) (!
   (=>
    (exists ((ranking~25$ Poly)) (!
      (and
       (has_type ranking~25$ %%hole%%0)
       (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? %%hole%%1 ranking~25$)
      )
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? %%hole%%2 ranking~25$))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__the_ranking_49
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__the_ranking_49
    ))
    (exists ((ranking~25$ Poly)) (!
      (and
       (and
        (has_type ranking~25$ %%hole%%0)
        (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? %%hole%%1 ranking~25$)
       )
       (= (%%choose%%1 %%hole%%0 %%hole%%1 %%hole%%2) ranking~25$)
      )
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? %%hole%%2 ranking~25$))
   )))
   :pattern ((%%choose%%1 %%hole%%0 %%hole%%1 %%hole%%2))
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.the_ranking.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.? self~2@) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>.
      (as_type (%%choose%%1 (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT)
        self~2@ self~2@
       ) (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. NAT)
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.the_ranking.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.the_ranking.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.the_ranking.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::the_rank_of
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of. (Poly Poly) Bool)
(declare-const %%global_location_label%%34 Bool)
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of. self~2@ ptr~4@) (=>
     %%global_location_label%%34
     (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@)
   ))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of. self~2@ ptr~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.the_rank_of._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.the_rank_of._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::the_rank_of
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? self~2@ ptr~4@) (ite
      (and
       (is-vstd!option.Option./Some (%Poly%vstd!option.Option. ptr~4@))
       (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
      )
      (nClip (+ (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
            self~2@
           )
          ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. ptr~4@))
         )
        ) 1
      ))
      0
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? self~2@ ptr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.the_rank_of.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.the_rank_of.?_definition
))))
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type ptr~4@ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
    )
    (<= 0 (bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? self~2@ ptr~4@))
   )
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? self~2@ ptr~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.the_rank_of.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.the_rank_of.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::build_tight
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.build_tight. (Poly Poly) Bool)
(declare-const %%global_location_label%%35 Bool)
(declare-const %%global_location_label%%36 Bool)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight. self~2@ root~4@) (and
     (=>
      %%global_location_label%%35
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     )
     (=>
      %%global_location_label%%36
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.build_tight. self~2@ root~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.build_tight.)
)
(declare-const fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.build_tight. Fuel)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ root~4@ fuel%@)
    (bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ root~4@ zero)
   )
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ root~4@
     fuel%@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight._fuel_to_zero_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight._fuel_to_zero_definition
)))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (fuel%@ Fuel)) (!
   (=>
    (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
    (= (bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ root~4@ (succ fuel%@))
     (ite
      (not (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@))
      (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I 0)) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (vstd!map.impl&%0.empty.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
      )))
      (ite
       (is-vstd!option.Option./None (%Poly%vstd!option.Option. root~4@))
       (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
           (%Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
         ))
        ) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
         (vstd!map.impl&%0.empty.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
       )))
       (let
        ((addr~92$ (%Poly%bundle!disk.GenericDisk_v.Address. (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option.
             root~4@
        )))))
        (let
         ((tail~111$ (bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ (Poly%vstd!option.Option.
             (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
               TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
               TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                  self~2@
                ))
               ) (Poly%bundle!disk.GenericDisk_v.Address. addr~92$)
              ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 self~2@
             ))))
            ) fuel%@
         )))
         (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
             (%Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
           ))
          ) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (vstd!map.impl&%0.insert.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
             (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
               (Poly%bundle!journal.LinkedJournal_v.DiskView. tail~111$)
             ))
            ) (Poly%bundle!disk.GenericDisk_v.Address. addr~92$) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
              ))
             ) (Poly%bundle!disk.GenericDisk_v.Address. addr~92$)
   ))))))))))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.? self~2@ root~4@
     (succ fuel%@)
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight._fuel_to_body_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.build_tight.)
  (forall ((self~2@ Poly) (root~4@ Poly)) (!
    (=>
     (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     (= (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? self~2@ root~4@) (bundle!journal.LinkedJournal_v.impl&%1.rec%build_tight.?
       self~2@ root~4@ (succ fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.build_tight.)
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.build_tight.? self~2@ root~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight.?_definition
))))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type root~4@ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
       self~2@ root~4@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.DiskView.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.build_tight.? self~2@ root~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.build_tight.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::build_tight
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.build_tight.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.build_tight.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.build_tight.? self~2@) (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal
      (%Poly%vstd!option.Option. (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
         (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
       ))
      ) (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
          (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
            self~2@
          ))
         ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
           (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
    )))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.build_tight.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.build_tight.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.build_tight.?_definition
))))
(assert
 (forall ((self~2@ Poly)) (!
   (=>
    (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.build_tight.?
       self~2@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.build_tight.? self~2@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.build_tight.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.build_tight.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::discard_old
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.discard_old. (Poly Poly) Bool)
(declare-const %%global_location_label%%37 Bool)
(assert
 (forall ((self~2@ Poly) (new_boundary~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.discard_old. self~2@ new_boundary~4@)
    (=>
     %%global_location_label%%37
     (<= (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       )
      ) (%I new_boundary~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.discard_old. self~2@ new_boundary~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.discard_old._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.discard_old._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::discard_old
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.discard_old.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.discard_old.)
  (forall ((self~2@ Poly) (new_boundary~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.discard_old.? self~2@ new_boundary~4@)
     (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I new_boundary~4@) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
    ))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.discard_old.? self~2@ new_boundary~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.discard_old.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.discard_old.?_definition
))))
(assert
 (forall ((self~2@ Poly) (new_boundary~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type new_boundary~4@ NAT)
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.discard_old.?
       self~2@ new_boundary~4@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.DiskView.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.discard_old.? self~2@ new_boundary~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.discard_old.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.discard_old.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::discard_old
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.discard_old. (Poly Poly) Bool)
(declare-const %%global_location_label%%38 Bool)
(declare-const %%global_location_label%%39 Bool)
(assert
 (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.discard_old. self~2@ lsn~4@) (and
     (=>
      %%global_location_label%%38
      (bundle!journal.LinkedJournal_v.impl&%2.wf.? self~2@)
     )
     (=>
      %%global_location_label%%39
      (bundle!journal.LinkedJournal_v.impl&%2.can_discard_to.? self~2@ lsn~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.discard_old. self~2@ lsn~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.discard_old._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.discard_old._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::discard_old
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.discard_old.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.discard_old.)
  (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.discard_old.? self~2@ lsn~4@) (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal
      (%Poly%vstd!option.Option. (Poly%vstd!option.Option. (ite
         (= (bundle!journal.LinkedJournal_v.impl&%2.seq_end.? self~2@) (%I lsn~4@))
         vstd!option.Option./None
         (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
           self~2@
       ))))
      ) (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.impl&%1.discard_old.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
          (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
            self~2@
          ))
         ) lsn~4@
    )))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.discard_old.? self~2@ lsn~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.discard_old.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.discard_old.?_definition
))))
(assert
 (forall ((self~2@ Poly) (lsn~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
     (has_type lsn~4@ NAT)
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.discard_old.?
       self~2@ lsn~4@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.discard_old.? self~2@ lsn~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.discard_old.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.discard_old.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::append_record
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.append_record.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.append_record.)
  (forall ((self~2@ Poly) (addr~4@ Poly) (msgs~6@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.append_record.? self~2@ addr~4@ msgs~6@)
     (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal (%Poly%vstd!option.Option.
       (Poly%vstd!option.Option. (vstd!option.Option./Some addr~4@))
      ) (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (let
         ((tmp%%2$ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (vstd!map.impl&%0.insert.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
                  (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
              ))))
             ) addr~4@ (Poly%bundle!journal.LinkedJournal_v.JournalRecord. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord
               (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. msgs~6@) (%Poly%vstd!option.Option.
                (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
                  (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
         )))))))))
         (let
          ((tmp%%1$ (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
             (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
          )))
          (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
              (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
                tmp%%1$
            ))))
           ) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
             tmp%%2$
    )))))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.append_record.? self~2@ addr~4@ msgs~6@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.append_record.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.append_record.?_definition
))))
(assert
 (forall ((self~2@ Poly) (addr~4@ Poly) (msgs~6@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
     (has_type addr~4@ TYPE%bundle!disk.GenericDisk_v.Address.)
     (has_type msgs~6@ TYPE%bundle!coordination_layer.MsgHistory_v.MsgHistory.)
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.append_record.?
       self~2@ addr~4@ msgs~6@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.append_record.? self~2@ addr~4@ msgs~6@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.append_record.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.append_record.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::is_sub_disk
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.)
  (forall ((self~2@ Poly) (bigger~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? self~2@ bigger~4@) (and
      (= (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
         bigger~4@
        )
       ) (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
      )))
      (vstd!map.impl&%0.le.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
        ))
       ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          bigger~4@
    ))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? self~2@ bigger~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.is_sub_disk.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.is_sub_disk.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::iptr
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.iptr. (Poly Poly) Bool)
(declare-const %%global_location_label%%40 Bool)
(declare-const %%global_location_label%%41 Bool)
(declare-const %%global_location_label%%42 Bool)
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.iptr. self~2@ ptr~4@) (and
     (=>
      %%global_location_label%%40
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@)
     )
     (=>
      %%global_location_label%%41
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
     )
     (=>
      %%global_location_label%%42
      (and
       (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@)
       (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
   ))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.iptr. self~2@ ptr~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.iptr._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.iptr._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::iptr
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.iptr.)
)
(declare-const fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.iptr. Fuel)
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.? self~2@ ptr~4@ fuel%@) (bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.?
     self~2@ ptr~4@ zero
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.? self~2@ ptr~4@ fuel%@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.iptr._fuel_to_zero_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.iptr._fuel_to_zero_definition
)))
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly) (fuel%@ Fuel)) (!
   (=>
    (and
     (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@)
     (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
    )
    (= (bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.? self~2@ ptr~4@ (succ fuel%@))
     (ite
      (is-vstd!option.Option./None (%Poly%vstd!option.Option. ptr~4@))
      vstd!option.Option./None
      (let
       ((jr~71$ (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. (vstd!map.impl&%0.index.?
           TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
            ))
           ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. ptr~4@))
       ))))
       (vstd!option.Option./Some (Poly%bundle!journal.PagedJournal_v.JournalRecord. (bundle!journal.PagedJournal_v.JournalRecord./JournalRecord
          (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
            (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
              (Poly%bundle!journal.LinkedJournal_v.JournalRecord. jr~71$)
           )))
          ) (%Poly%vstd!option.Option. (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.?
             self~2@ (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
               (Poly%bundle!journal.LinkedJournal_v.JournalRecord. jr~71$) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
                 (%Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
              )))
             ) fuel%@
   ))))))))))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.? self~2@ ptr~4@ (succ fuel%@)))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.iptr._fuel_to_body_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.iptr._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.iptr.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (=>
     (and
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ ptr~4@)
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
     )
     (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? self~2@ ptr~4@) (bundle!journal.LinkedJournal_v.impl&%1.rec%iptr.?
       self~2@ ptr~4@ (succ fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.iptr.)
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.iptr.? self~2@ ptr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.iptr.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.iptr.?_definition
))))
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type ptr~4@ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
    )
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.iptr.? self~2@
       ptr~4@
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!journal.PagedJournal_v.JournalRecord.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.iptr.? self~2@ ptr~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.iptr.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.iptr.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::is_tight
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.is_tight.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.is_tight.)
  (forall ((self~2@ Poly) (root~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? self~2@ root~4@) (and
      (and
       (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
       (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
      )
      (forall ((other~24$ Poly)) (!
        (=>
         (has_type other~24$ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
         (=>
          (and
           (and
            (and
             (bundle!journal.LinkedJournal_v.impl&%1.decodable.? other~24$ root~4@)
             (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? other~24$)
            )
            (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? self~2@ root~4@) (bundle!journal.LinkedJournal_v.impl&%1.iptr.?
              other~24$ root~4@
           )))
           (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~24$ self~2@)
          )
          (= other~24$ self~2@)
        ))
        :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~24$ self~2@))
        :qid
        user_bundle__journal__LinkedJournal_v__impl&%1__is_tight_50
        :skolemid
        skolem_user_bundle__journal__LinkedJournal_v__impl&%1__is_tight_50
    ))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_tight.? self~2@ root~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.is_tight.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.is_tight.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::build_tight_builds_sub_disks
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option.) Bool
)
(declare-const %%global_location_label%%43 Bool)
(declare-const %%global_location_label%%44 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks. self~2@
     root~4@
    ) (and
     (=>
      %%global_location_label%%43
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%44
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
   )))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks.
     self~2@ root~4@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_builds_sub_disks._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_builds_sub_disks._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight_builds_sub_disks
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option.) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks. self~2@
     root~4@
    ) (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
      (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
      )
     ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
   ))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_builds_sub_disks.
     self~2@ root~4@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_builds_sub_disks._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_builds_sub_disks._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::build_tight_ensures
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(declare-const %%global_location_label%%45 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ root~4@)
    (=>
     %%global_location_label%%45
     (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       self~2@
      ) (Poly%vstd!option.Option. root~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@
     root~4@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ensures._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight_ensures
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ root~4@)
    (and
     (forall ((addr~31$ Poly)) (!
       (=>
        (has_type addr~31$ TYPE%bundle!disk.GenericDisk_v.Address.)
        (=>
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
                (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
                 root~4@
           ))))))
          ) addr~31$
         )
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
           )))
          ) addr~31$
       )))
       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
                root~4@
          ))))))
         ) addr~31$
       ))
       :qid
       user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_ensures_51
       :skolemid
       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_ensures_51
     ))
     (=>
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
      ))
      (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
         ) (Poly%vstd!option.Option. root~4@)
        )
       ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
   ))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@
     root~4@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ensures._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::next
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.next.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.next.)
  (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.next.? self~2@ ptr~4@) (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
      (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
        ))
       ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. ptr~4@))
      ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
    )))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.next.? self~2@ ptr~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.next.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.next.?_definition
))))
(assert
 (forall ((self~2@ Poly) (ptr~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
     (has_type ptr~4@ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
    )
    (has_type (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.next.? self~2@
       ptr~4@
      )
     ) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.)
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.next.? self~2@ ptr~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.next.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.next.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::build_tight_ranks
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(declare-const %%global_location_label%%46 Bool)
(declare-const %%global_location_label%%47 Bool)
(declare-const %%global_location_label%%48 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (ptr~4@ vstd!option.Option.))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. self~2@ ptr~4@)
    (and
     (=>
      %%global_location_label%%46
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. ptr~4@)
     ))
     (=>
      %%global_location_label%%47
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
     )))
     (=>
      %%global_location_label%%48
      (is-vstd!option.Option./Some ptr~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. self~2@ ptr~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ranks._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ranks._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight_ranks
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (ptr~4@ vstd!option.Option.))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. self~2@ ptr~4@)
    (forall ((addr~40$ Poly)) (!
      (=>
       (has_type addr~40$ TYPE%bundle!disk.GenericDisk_v.Address.)
       (=>
        (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
                (bundle!journal.LinkedJournal_v.impl&%1.next.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                  self~2@
                 ) (Poly%vstd!option.Option. ptr~4@)
          )))))))
         ) addr~40$
        )
        (and
         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
             (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
           ))
          ) addr~40$
         )
         (< (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
             )
            ) addr~40$
           )
          ) (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
             )
            ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
               ptr~4@
      )))))))))
      :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
         (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
          (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
            (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
               (bundle!journal.LinkedJournal_v.impl&%1.next.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                 self~2@
                ) (Poly%vstd!option.Option. ptr~4@)
         )))))))
        ) addr~40$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_ranks_52
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_ranks_52
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ranks. self~2@ ptr~4@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ranks._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_ranks._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::build_tight_shape
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(declare-const %%global_location_label%%49 Bool)
(declare-const %%global_location_label%%50 Bool)
(declare-const %%global_location_label%%51 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@)
    (and
     (=>
      %%global_location_label%%49
      (is-vstd!option.Option./Some root~4@)
     )
     (=>
      %%global_location_label%%50
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%51
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
   )))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_shape._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.build_tight_shape._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight_shape
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@)
    (= (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       self~2@
      ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
        (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
         (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
          (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
            (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
          ))
         ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
            root~4@
         )))
        ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
      )))))
     ) (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
         (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
       ))))
      ) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
       (vstd!map.impl&%0.remove.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
             (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
              root~4@
         )))))
        ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
           root~4@
   ))))))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_shape._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_shape._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::sub_disk_transitive_auto
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.sub_disk_transitive_auto.
 (Int) Bool
)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.sub_disk_transitive_auto. no%param@)
    (forall ((a~14$ Poly) (b~16$ Poly) (c~18$ Poly)) (!
      (=>
       (and
        (has_type a~14$ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
        (has_type b~16$ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
        (has_type c~18$ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
       )
       (=>
        (and
         (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? a~14$ b~16$)
         (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? b~16$ c~18$)
        )
        (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? a~14$ c~18$)
      ))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? a~14$ b~16$) (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.?
        b~16$ c~18$
      ))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? a~14$ b~16$) (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.?
        b~16$ c~18$
      ))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? a~14$ b~16$) (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.?
        a~14$ c~18$
      ))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? b~16$ c~18$) (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.?
        a~14$ c~18$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__sub_disk_transitive_auto_53
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__sub_disk_transitive_auto_53
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.sub_disk_transitive_auto. no%param@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.sub_disk_transitive_auto._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.sub_disk_transitive_auto._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::iptr_ignores_extra_blocks
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.)
 Bool
)
(declare-const %%global_location_label%%52 Bool)
(declare-const %%global_location_label%%53 Bool)
(declare-const %%global_location_label%%54 Bool)
(declare-const %%global_location_label%%55 Bool)
(declare-const %%global_location_label%%56 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (ptr~4@ vstd!option.Option.)
   (big~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. self~2@ ptr~4@
     big~6@
    ) (and
     (=>
      %%global_location_label%%52
      (bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
     )))
     (=>
      %%global_location_label%%53
      (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. ptr~4@)
     ))
     (=>
      %%global_location_label%%54
      (bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~6@
     )))
     (=>
      %%global_location_label%%55
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~6@
     )))
     (=>
      %%global_location_label%%56
      (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%bundle!journal.LinkedJournal_v.DiskView. big~6@)
   ))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. self~2@
     ptr~4@ big~6@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.iptr_ignores_extra_blocks._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.iptr_ignores_extra_blocks._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::iptr_ignores_extra_blocks
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.)
 Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (ptr~4@ vstd!option.Option.)
   (big~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. self~2@ ptr~4@
     big~6@
    ) (and
     (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       self~2@
     ))
     (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. ptr~4@)
      ) (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~6@
       ) (Poly%vstd!option.Option. ptr~4@)
   ))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. self~2@
     ptr~4@ big~6@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.iptr_ignores_extra_blocks._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.iptr_ignores_extra_blocks._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::tight_sub_disk
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.
 ) Bool
)
(declare-const %%global_location_label%%57 Bool)
(declare-const %%global_location_label%%58 Bool)
(declare-const %%global_location_label%%59 Bool)
(declare-const %%global_location_label%%60 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (tight~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ root~4@ tight~6@)
    (and
     (=>
      %%global_location_label%%57
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%58
      (= tight~6@ (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
        ) (Poly%vstd!option.Option. root~4@)
     )))
     (=>
      %%global_location_label%%59
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
     )))
     (=>
      %%global_location_label%%60
      (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        tight~6@
       ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
   ))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ root~4@
     tight~6@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.tight_sub_disk._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.tight_sub_disk._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::tight_sub_disk
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (tight~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ root~4@ tight~6@)
    (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
      tight~6@
     ) (Poly%vstd!option.Option. root~4@)
   ))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ root~4@
     tight~6@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.tight_sub_disk._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.tight_sub_disk._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::tight_interp
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.
 ) Bool
)
(declare-const %%global_location_label%%61 Bool)
(declare-const %%global_location_label%%62 Bool)
(declare-const %%global_location_label%%63 Bool)
(assert
 (forall ((big~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (tight~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. big~2@ root~4@ tight~6@)
    (and
     (=>
      %%global_location_label%%61
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%62
      (= tight~6@ (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         big~2@
        ) (Poly%vstd!option.Option. root~4@)
     )))
     (=>
      %%global_location_label%%63
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~2@
   )))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. big~2@ root~4@
     tight~6@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.tight_interp._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.tight_interp._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::tight_interp
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option. bundle!journal.LinkedJournal_v.DiskView.
 ) Bool
)
(assert
 (forall ((big~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (tight~6@ bundle!journal.LinkedJournal_v.DiskView.)
  ) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. big~2@ root~4@ tight~6@)
    (and
     (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       tight~6@
      ) (Poly%bundle!journal.LinkedJournal_v.DiskView. big~2@)
     )
     (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       tight~6@
      ) (Poly%vstd!option.Option. root~4@)
     )
     (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        tight~6@
       ) (Poly%vstd!option.Option. root~4@)
      ) (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        big~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       tight~6@
   ))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.tight_interp. big~2@ root~4@
     tight~6@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.tight_interp._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.tight_interp._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%0::contains_lsn
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%0.contains_lsn.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%0.contains_lsn.)
  (forall ((self~2@ Poly) (boundary_lsn~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%0.contains_lsn.? self~2@ boundary_lsn~4@)
     (and
      (<= (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_start (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
         (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq
           (%Poly%bundle!journal.LinkedJournal_v.JournalRecord. self~2@)
        )))
       ) (%I boundary_lsn~4@)
      )
      (< (%I boundary_lsn~4@) (bundle!coordination_layer.MsgHistory_v.MsgHistory./MsgHistory/seq_end
        (%Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory. (Poly%bundle!coordination_layer.MsgHistory_v.MsgHistory.
          (bundle!journal.LinkedJournal_v.JournalRecord./JournalRecord/message_seq (%Poly%bundle!journal.LinkedJournal_v.JournalRecord.
            self~2@
    ))))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%0.contains_lsn.? self~2@ boundary_lsn~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__0.contains_lsn.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__0.contains_lsn.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::is_sub_disk_with_newer_lsn
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.)
  (forall ((self~2@ Poly) (bigger~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.? self~2@ bigger~4@)
     (and
      (<= (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
         bigger~4@
        )
       ) (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
      )))
      (vstd!map.impl&%0.le.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
        ))
       ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
          bigger~4@
    ))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk_with_newer_lsn.? self~2@
      bigger~4@
    ))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.is_sub_disk_with_newer_lsn.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.is_sub_disk_with_newer_lsn.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::build_tight_auto
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_auto. (bundle!journal.LinkedJournal_v.DiskView.)
 Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_auto. self~2@) (forall (
      (root~16$ Poly)
     ) (!
      (=>
       (has_type root~16$ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
       (=>
        (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
          self~2@
         ) root~16$
        )
        (and
         (forall ((addr~37$ Poly)) (!
           (=>
            (has_type addr~37$ TYPE%bundle!disk.GenericDisk_v.Address.)
            (=>
             (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
               TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
               (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                  (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
                    (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$
               )))))
              ) addr~37$
             )
             (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
               TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
               (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                  (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
               )))
              ) addr~37$
           )))
           :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.impl&%1.build_tight.?
                   (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$
              )))))
             ) addr~37$
           ))
           :qid
           user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_auto_54
           :skolemid
           skolem_user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_auto_54
         ))
         (=>
          (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
            self~2@
          ))
          (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
            (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
             ) root~16$
            )
           ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
      )))))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
        ) root~16$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_auto_55
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__build_tight_auto_55
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_auto. self~2@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_auto._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.build_tight_auto._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::representation
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.representation. (Poly Poly)
 Bool
)
(declare-const %%global_location_label%%64 Bool)
(declare-const %%global_location_label%%65 Bool)
(declare-const %%global_location_label%%66 Bool)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.representation. self~2@ root~4@) (and
     (=>
      %%global_location_label%%64
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     )
     (=>
      %%global_location_label%%65
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
     )
     (=>
      %%global_location_label%%66
      (and
       (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
       (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
   ))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.representation. self~2@ root~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.representation._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.representation._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::representation
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%1.representation.)
)
(declare-const fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.representation. Fuel)
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (fuel%@ Fuel)) (!
   (= (bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? self~2@ root~4@ fuel%@)
    (bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? self~2@ root~4@ zero)
   )
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? self~2@ root~4@
     fuel%@
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.representation._fuel_to_zero_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.representation._fuel_to_zero_definition
)))
(assert
 (forall ((self~2@ Poly) (root~4@ Poly) (fuel%@ Fuel)) (!
   (=>
    (and
     (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
     (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
    )
    (= (bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? self~2@ root~4@ (succ
       fuel%@
      )
     ) (%Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (ite
       (is-vstd!option.Option./None (%Poly%vstd!option.Option. root~4@))
       (vstd!set.impl&%0.empty.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.)
       (let
        ((addr~62$ (%Poly%bundle!disk.GenericDisk_v.Address. (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option.
             root~4@
        )))))
        (vstd!set.impl&%0.insert.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (bundle!journal.LinkedJournal_v.impl&%1.rec%representation.?
           self~2@ (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
             (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 self~2@
               ))
              ) (Poly%bundle!disk.GenericDisk_v.Address. addr~62$)
             ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                self~2@
            ))))
           ) fuel%@
          )
         ) (Poly%bundle!disk.GenericDisk_v.Address. addr~62$)
   ))))))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%1.rec%representation.? self~2@ root~4@
     (succ fuel%@)
   ))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__1.representation._fuel_to_body_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.representation._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%1.representation.)
  (forall ((self~2@ Poly) (root~4@ Poly)) (!
    (=>
     (and
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? self~2@ root~4@)
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? self~2@)
     )
     (= (bundle!journal.LinkedJournal_v.impl&%1.representation.? self~2@ root~4@) (bundle!journal.LinkedJournal_v.impl&%1.rec%representation.?
       self~2@ root~4@ (succ fuel_nat%bundle!journal.LinkedJournal_v.impl&%1.representation.)
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%1.representation.? self~2@ root~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__1.representation.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__1.representation.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::representation_ensures
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(declare-const %%global_location_label%%67 Bool)
(declare-const %%global_location_label%%68 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. self~2@ root~4@)
    (and
     (=>
      %%global_location_label%%67
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%68
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
   )))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. self~2@
     root~4@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.representation_ensures._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.representation_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::representation_ensures
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. (bundle!journal.LinkedJournal_v.DiskView.
  vstd!option.Option.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. self~2@ root~4@)
    (forall ((addr~35$ Poly)) (!
      (=>
       (has_type addr~35$ TYPE%bundle!disk.GenericDisk_v.Address.)
       (=>
        (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (bundle!journal.LinkedJournal_v.impl&%1.representation.?
           (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
            root~4@
          ))
         ) addr~35$
        )
        (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
             (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
          )))
         ) addr~35$
      )))
      :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (bundle!journal.LinkedJournal_v.impl&%1.representation.?
          (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
           root~4@
         ))
        ) addr~35$
      ))
      :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
        (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
         (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
          (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
            (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
         )))
        ) addr~35$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__representation_ensures_56
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__representation_ensures_56
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.representation_ensures. self~2@
     root~4@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.representation_ensures._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.representation_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::representation_auto
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.representation_auto. (bundle!journal.LinkedJournal_v.DiskView.)
 Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.representation_auto. self~2@) (forall
     ((root~16$ Poly)) (!
      (=>
       (has_type root~16$ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
       (=>
        (and
         (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
          ) root~16$
         )
         (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
        )))
        (forall ((addr~40$ Poly)) (!
          (=>
           (has_type addr~40$ TYPE%bundle!disk.GenericDisk_v.Address.)
           (=>
            (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (bundle!journal.LinkedJournal_v.impl&%1.representation.?
               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$
              )
             ) addr~40$
            )
            (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                 (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
              )))
             ) addr~40$
          )))
          :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            (Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (bundle!journal.LinkedJournal_v.impl&%1.representation.?
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$
             )
            ) addr~40$
          ))
          :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
             )))
            ) addr~40$
          ))
          :qid
          user_bundle__journal__LinkedJournal_v__impl&%1__representation_auto_57
          :skolemid
          skolem_user_bundle__journal__LinkedJournal_v__impl&%1__representation_auto_57
      ))))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
        ) root~16$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__representation_auto_58
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__representation_auto_58
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.representation_auto. self~2@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.representation_auto._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.representation_auto._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop_ensures
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option. Int) Bool
)
(declare-const %%global_location_label%%69 Bool)
(declare-const %%global_location_label%%70 Bool)
(declare-const %%global_location_label%%71 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (depth~6@ Int)
  ) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures. self~2@
     root~4@ depth~6@
    ) (and
     (=>
      %%global_location_label%%69
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%70
      (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (=>
      %%global_location_label%%71
      (bundle!journal.LinkedJournal_v.impl&%1.can_crop.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@) (I depth~6@)
   ))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures. self~2@
     root~4@ depth~6@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_ensures._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop_ensures
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures.
 (bundle!journal.LinkedJournal_v.DiskView. vstd!option.Option. Int) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.) (root~4@ vstd!option.Option.)
   (depth~6@ Int)
  ) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures. self~2@
     root~4@ depth~6@
    ) (and
     (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       self~2@
      ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.?
        (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
         root~4@
        ) (I depth~6@)
     )))
     (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
       self~2@
      ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.?
        (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) (Poly%vstd!option.Option.
         root~4@
        ) (I depth~6@)
   )))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_ensures. self~2@
     root~4@ depth~6@
   ))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_ensures._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%1::pointer_after_crop_auto
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_auto. (
  bundle!journal.LinkedJournal_v.DiskView.
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.DiskView.)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_auto. self~2@) (
     forall ((root~16$ Poly) (depth~18$ Poly)) (!
      (=>
       (and
        (has_type root~16$ (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
        (has_type depth~18$ NAT)
       )
       (=>
        (and
         (and
          (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
            self~2@
           ) root~16$
          )
          (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
            self~2@
           ) root~16$
         ))
         (bundle!journal.LinkedJournal_v.impl&%1.can_crop.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
          ) root~16$ depth~18$
        ))
        (and
         (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
          ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.?
            (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$ depth~18$
         )))
         (bundle!journal.LinkedJournal_v.impl&%1.block_in_bounds.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
           self~2@
          ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.?
            (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) root~16$ depth~18$
      ))))))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
         self~2@
        ) root~16$ depth~18$
      ))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%1__pointer_after_crop_auto_59
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__pointer_after_crop_auto_59
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop_auto. self~2@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_auto._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__1.pointer_after_crop_auto._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::can_crop
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.can_crop.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.can_crop.)
  (forall ((self~2@ Poly) (depth~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.can_crop.? self~2@ depth~4@) (and
      (bundle!journal.LinkedJournal_v.impl&%2.decodable.? self~2@)
      (bundle!journal.LinkedJournal_v.impl&%1.can_crop.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
        ))
       ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
         (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
        )
       ) depth~4@
    )))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.can_crop.? self~2@ depth~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.can_crop.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.can_crop.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::crop
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.crop. (Poly Poly) Bool)
(declare-const %%global_location_label%%72 Bool)
(assert
 (forall ((self~2@ Poly) (depth~4@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.crop. self~2@ depth~4@) (=>
     %%global_location_label%%72
     (bundle!journal.LinkedJournal_v.impl&%2.can_crop.? self~2@ depth~4@)
   ))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.crop. self~2@ depth~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.crop._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.crop._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::crop
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.crop.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.crop.)
  (forall ((self~2@ Poly) (depth~4@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.crop.? self~2@ depth~4@) (let
      ((ptr~30$ (bundle!journal.LinkedJournal_v.impl&%1.pointer_after_crop.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
          (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
            self~2@
          ))
         ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
           (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
          )
         ) depth~4@
      )))
      (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal (%Poly%vstd!option.Option.
        (Poly%vstd!option.Option. ptr~30$)
       ) (%Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
         (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
           self~2@
    )))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.crop.? self~2@ depth~4@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.crop.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.crop.?_definition
))))
(assert
 (forall ((self~2@ Poly) (depth~4@ Poly)) (!
   (=>
    (and
     (has_type self~2@ TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.)
     (has_type depth~4@ NAT)
    )
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.crop.?
       self~2@ depth~4@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.crop.? self~2@ depth~4@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.crop.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.crop.?_pre_post_definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::crop_ensures
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. (bundle!journal.LinkedJournal_v.TruncatedJournal.
  Int
 ) Bool
)
(declare-const %%global_location_label%%73 Bool)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.TruncatedJournal.) (depth~4@ Int))
  (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. self~2@ depth~4@) (=>
     %%global_location_label%%73
     (bundle!journal.LinkedJournal_v.impl&%2.can_crop.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
       self~2@
      ) (I depth~4@)
   )))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. self~2@ depth~4@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.crop_ensures._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.crop_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::crop_ensures
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. (bundle!journal.LinkedJournal_v.TruncatedJournal.
  Int
 ) Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.TruncatedJournal.) (depth~4@ Int))
  (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. self~2@ depth~4@) (bundle!journal.LinkedJournal_v.impl&%2.wf.?
     (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.crop.?
       (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@) (I depth~4@)
   ))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%2.crop_ensures. self~2@ depth~4@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__2.crop_ensures._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__2.crop_ensures._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::crop_auto
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%2.crop_auto. (bundle!journal.LinkedJournal_v.TruncatedJournal.)
 Bool
)
(assert
 (forall ((self~2@ bundle!journal.LinkedJournal_v.TruncatedJournal.)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%2.crop_auto. self~2@) (forall ((depth~16$
       Poly
      )
     ) (!
      (=>
       (has_type depth~16$ NAT)
       (=>
        (bundle!journal.LinkedJournal_v.impl&%2.can_crop.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
         ) depth~16$
        )
        (bundle!journal.LinkedJournal_v.impl&%2.wf.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          (bundle!journal.LinkedJournal_v.impl&%2.crop.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
            self~2@
           ) depth~16$
      )))))
      :pattern ((bundle!journal.LinkedJournal_v.impl&%2.wf.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
         (bundle!journal.LinkedJournal_v.impl&%2.crop.? (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
           self~2@
          ) depth~16$
      ))))
      :qid
      user_bundle__journal__LinkedJournal_v__impl&%2__crop_auto_60
      :skolemid
      skolem_user_bundle__journal__LinkedJournal_v__impl&%2__crop_auto_60
   )))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%2.crop_auto. self~2@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__2.crop_auto._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__2.crop_auto._definition
)))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::representation
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.representation. (Poly) Bool)
(declare-const %%global_location_label%%74 Bool)
(declare-const %%global_location_label%%75 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.representation. self~2@) (and
     (=>
      %%global_location_label%%74
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
        ))
       ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
         (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
     ))))
     (=>
      %%global_location_label%%75
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
   )))))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.representation. self~2@))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.representation._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.representation._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::representation
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.representation.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.representation.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.representation.? self~2@) (bundle!journal.LinkedJournal_v.impl&%1.representation.?
      (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
        (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
       )
      ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
        (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
    ))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.representation.? self~2@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.representation.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.representation.?_definition
))))

;; Function-Specs bundle::journal::LinkedJournal_v::impl&%2::disk_is_tight_wrt_representation
(declare-fun req%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.
 (Poly) Bool
)
(declare-const %%global_location_label%%76 Bool)
(declare-const %%global_location_label%%77 Bool)
(assert
 (forall ((self~2@ Poly)) (!
   (= (req%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation. self~2@)
    (and
     (=>
      %%global_location_label%%76
      (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
        ))
       ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/freshest_rec
         (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
     ))))
     (=>
      %%global_location_label%%77
      (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal.
          self~2@
   )))))))
   :pattern ((req%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.
     self~2@
   ))
   :qid
   internal_req__bundle!journal.LinkedJournal_v.impl&__2.disk_is_tight_wrt_representation._definition
   :skolemid
   skolem_internal_req__bundle!journal.LinkedJournal_v.impl&__2.disk_is_tight_wrt_representation._definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::disk_is_tight_wrt_representation
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.)
  (forall ((self~2@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.? self~2@)
     (= (%Poly%vstd!set.Set<bundle!disk.GenericDisk_v.Address.>. (vstd!map.impl&%0.dom.?
        TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
           (Poly%bundle!journal.LinkedJournal_v.DiskView. (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal/disk_view
             (%Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. self~2@)
       ))))))
      ) (bundle!journal.LinkedJournal_v.impl&%2.representation.? self~2@)
    ))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.disk_is_tight_wrt_representation.?
      self~2@
    ))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.disk_is_tight_wrt_representation.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.disk_is_tight_wrt_representation.?_definition
))))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::mkfs
(assert
 (fuel_bool_default fuel%bundle!journal.LinkedJournal_v.impl&%2.mkfs.)
)
(assert
 (=>
  (fuel_bool fuel%bundle!journal.LinkedJournal_v.impl&%2.mkfs.)
  (forall ((no%param@ Poly)) (!
    (= (bundle!journal.LinkedJournal_v.impl&%2.mkfs.? no%param@) (bundle!journal.LinkedJournal_v.TruncatedJournal./TruncatedJournal
      (%Poly%vstd!option.Option. (Poly%vstd!option.Option. vstd!option.Option./None)) (
       %Poly%bundle!journal.LinkedJournal_v.DiskView. (Poly%bundle!journal.LinkedJournal_v.DiskView.
        (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I 0)) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
          (vstd!map.impl&%0.empty.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
    )))))))
    :pattern ((bundle!journal.LinkedJournal_v.impl&%2.mkfs.? no%param@))
    :qid
    internal_bundle!journal.LinkedJournal_v.impl&__2.mkfs.?_definition
    :skolemid
    skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.mkfs.?_definition
))))
(assert
 (forall ((no%param@ Poly)) (!
   (=>
    (has_type no%param@ INT)
    (has_type (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.mkfs.?
       no%param@
      )
     ) TYPE%bundle!journal.LinkedJournal_v.TruncatedJournal.
   ))
   :pattern ((bundle!journal.LinkedJournal_v.impl&%2.mkfs.? no%param@))
   :qid
   internal_bundle!journal.LinkedJournal_v.impl&__2.mkfs.?_pre_post_definition
   :skolemid
   skolem_internal_bundle!journal.LinkedJournal_v.impl&__2.mkfs.?_pre_post_definition
)))

;; Function-Axioms bundle::journal::LinkedJournal_v::impl&%2::mkfs_ensures
(declare-fun ens%bundle!journal.LinkedJournal_v.impl&%2.mkfs_ensures. (Int) Bool)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%bundle!journal.LinkedJournal_v.impl&%2.mkfs_ensures. no%param@) (bundle!journal.LinkedJournal_v.impl&%2.decodable.?
     (Poly%bundle!journal.LinkedJournal_v.TruncatedJournal. (bundle!journal.LinkedJournal_v.impl&%2.mkfs.?
       (I 0)
   ))))
   :pattern ((ens%bundle!journal.LinkedJournal_v.impl&%2.mkfs_ensures. no%param@))
   :qid
   internal_ens__bundle!journal.LinkedJournal_v.impl&__2.mkfs_ensures._definition
   :skolemid
   skolem_internal_ens__bundle!journal.LinkedJournal_v.impl&__2.mkfs_ensures._definition
)))

;; Function-Def bundle::journal::LinkedJournal_v::impl&%1::tight_sub_disk
(push)
 (declare-const self~2@ bundle!journal.LinkedJournal_v.DiskView.)
 (declare-const root~4@ vstd!option.Option.)
 (declare-const tight~6@ bundle!journal.LinkedJournal_v.DiskView.)
 (declare-const tmp%1@ Bool)
 (declare-const other~165@ Poly)
 (declare-const tmp%2@ Bool)
 (declare-const tmp%3@ Bool)
 (declare-const tmp%4@ Bool)
 (declare-const tmp%5@ Bool)
 (declare-const tmp%6@ Bool)
 (declare-const tmp%7@ Bool)
 (declare-const addr~329@ Poly)
 (declare-const tmp%8@ Bool)
 (declare-const tmp%9@ Bool)
 (declare-const tmp%10@ Bool)
 (declare-const tmp%11@ Bool)
 (declare-const tmp%12@ Bool)
 (declare-const tmp%13@ Bool)
 (declare-const tmp%14@ Bool)
 (declare-const tmp%15@ Bool)
 (declare-const tmp%16@ Bool)
 (declare-const tmp%17@ Bool)
 (declare-const tmp%18@ Bool)
 (declare-const tmp%19@ Bool)
 (declare-const tmp%20@ Bool)
 (declare-const tmp%21@ Bool)
 (declare-const tmp%22@ Bool)
 (declare-const tmp%23@ Bool)
 (declare-const tmp%24@ Bool)
 (declare-const aprior~465@ vstd!option.Option.)
 (declare-const tmp%25@ Bool)
 (declare-const tmp%26@ Bool)
 (declare-const tmp%27@ Bool)
 (declare-const tmp%28@ Bool)
 (declare-const tmp%29@ Bool)
 (declare-const tmp%30@ Bool)
 (declare-const a~880@ Poly)
 (declare-const tmp%31@ Bool)
 (declare-const tmp%32@ Bool)
 (declare-const tmp%33@ Bool)
 (declare-const tmp%34@ Bool)
 (declare-const tmp%35@ Bool)
 (declare-const tmp%36@ Bool)
 (declare-const a~1027@ Poly)
 (declare-const key~1123@ Poly)
 (declare-const tmp%37@ Bool)
 (declare-const tmp%38@ Bool)
 (declare-const key~1298@ Poly)
 (declare-const tmp%39@ Bool)
 (declare-const tmp%40@ Bool)
 (declare-const other_inner~242@ bundle!journal.LinkedJournal_v.DiskView.)
 (declare-const m1~1089@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
 (declare-const m2~1100@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
 (declare-const m1~1264@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
 (declare-const m2~1275@ vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.)
 (declare-const tmp%41@ Bool)
 (declare-const tmp%42@ Bool)
 (declare-const tmp%43@ Bool)
 (declare-const next~97@ vstd!option.Option.)
 (declare-const inner~106@ bundle!journal.LinkedJournal_v.DiskView.)
 (declare-const tmp%44@ Bool)
 (declare-const tmp%45@ Bool)
 (declare-const tmp%46@ Bool)
 (declare-const tmp%47@ Bool)
 (declare-const other~1551@ Poly)
 (declare-const tmp%48@ Bool)
 (declare-const tmp%49@ Bool)
 (declare-const tmp%50@ Bool)
 (declare-const decrease%init0@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@) TYPE%bundle!journal.LinkedJournal_v.DiskView.)
 )
 (assert
  (has_type (Poly%vstd!option.Option. root~4@) (TYPE%vstd!option.Option. TYPE%bundle!disk.GenericDisk_v.Address.))
 )
 (assert
  (has_type (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@) TYPE%bundle!journal.LinkedJournal_v.DiskView.)
 )
 (assert
  (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
    self~2@
   ) (Poly%vstd!option.Option. root~4@)
 ))
 (assert
  (= tight~6@ (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
     self~2@
    ) (Poly%vstd!option.Option. root~4@)
 )))
 (assert
  (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
    self~2@
 )))
 (assert
  (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
    tight~6@
   ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
 ))
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 (declare-const %%switch_label%%2 Bool)
 (declare-const %%switch_label%%3 Bool)
 (declare-const %%switch_label%%4 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%0 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%1 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%2 Bool)
 ;; could not prove termination
 (declare-const %%location_label%%3 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 ;; assertion failed
 (declare-const %%location_label%%8 Bool)
 ;; assertion failed
 (declare-const %%location_label%%9 Bool)
 ;; assertion failed
 (declare-const %%location_label%%10 Bool)
 ;; assertion failed
 (declare-const %%location_label%%11 Bool)
 ;; assertion failed
 (declare-const %%location_label%%12 Bool)
 ;; assertion failed
 (declare-const %%location_label%%13 Bool)
 ;; assertion failed
 (declare-const %%location_label%%14 Bool)
 ;; assertion failed
 (declare-const %%location_label%%15 Bool)
 ;; assertion failed
 (declare-const %%location_label%%16 Bool)
 ;; assertion failed
 (declare-const %%location_label%%17 Bool)
 ;; assertion failed
 (declare-const %%location_label%%18 Bool)
 ;; assertion failed
 (declare-const %%location_label%%19 Bool)
 ;; assertion failed
 (declare-const %%location_label%%20 Bool)
 ;; assertion failed
 (declare-const %%location_label%%21 Bool)
 ;; assertion failed
 (declare-const %%location_label%%22 Bool)
 ;; assertion failed
 (declare-const %%location_label%%23 Bool)
 ;; assertion failed
 (declare-const %%location_label%%24 Bool)
 ;; assertion failed
 (declare-const %%location_label%%25 Bool)
 ;; assertion failed
 (declare-const %%location_label%%26 Bool)
 ;; assertion failed
 (declare-const %%location_label%%27 Bool)
 ;; assertion failed
 (declare-const %%location_label%%28 Bool)
 ;; assertion failed
 (declare-const %%location_label%%29 Bool)
 ;; assertion failed
 (declare-const %%location_label%%30 Bool)
 ;; assertion failed
 (declare-const %%location_label%%31 Bool)
 ;; assertion failed
 (declare-const %%location_label%%32 Bool)
 ;; assertion failed
 (declare-const %%location_label%%33 Bool)
 ;; assertion failed
 (declare-const %%location_label%%34 Bool)
 ;; assertion failed
 (declare-const %%location_label%%35 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%36 Bool)
 ;; assertion failed
 (declare-const %%location_label%%37 Bool)
 ;; assertion failed
 (declare-const %%location_label%%38 Bool)
 ;; assertion failed
 (declare-const %%location_label%%39 Bool)
 ;; assertion failed
 (declare-const %%location_label%%40 Bool)
 ;; assertion failed
 (declare-const %%location_label%%41 Bool)
 ;; assertion failed
 (declare-const %%location_label%%42 Bool)
 ;; assertion failed
 (declare-const %%location_label%%43 Bool)
 ;; assertion failed
 (declare-const %%location_label%%44 Bool)
 ;; assertion failed
 (declare-const %%location_label%%45 Bool)
 ;; assertion failed
 (declare-const %%location_label%%46 Bool)
 ;; assertion failed
 (declare-const %%location_label%%47 Bool)
 ;; assertion failed
 (declare-const %%location_label%%48 Bool)
 ;; assertion failed
 (declare-const %%location_label%%49 Bool)
 ;; assertion failed
 (declare-const %%location_label%%50 Bool)
 ;; assertion failed
 (declare-const %%location_label%%51 Bool)
 ;; assertion failed
 (declare-const %%location_label%%52 Bool)
 ;; assertion failed
 (declare-const %%location_label%%53 Bool)
 ;; assertion failed
 (declare-const %%location_label%%54 Bool)
 ;; assertion failed
 (declare-const %%location_label%%55 Bool)
 ;; assertion failed
 (declare-const %%location_label%%56 Bool)
 ;; assertion failed
 (declare-const %%location_label%%57 Bool)
 ;; assertion failed
 (declare-const %%location_label%%58 Bool)
 ;; postcondition not satisfied
 (declare-const %%location_label%%59 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= decrease%init0@ (bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
        self~2@
       ) (Poly%vstd!option.Option. root~4@)
     ))
     (and
      (=>
       %%location_label%%0
       (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ root~4@)
      )
      (=>
       (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ root~4@)
       (or
        (=>
         (is-vstd!option.Option./Some root~4@)
         (=>
          (= next~97@ (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
             TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
              ))
             ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                root~4@
             )))
            ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
          )))))
          (=>
           (= inner~106@ (bundle!journal.LinkedJournal_v.impl&%1.build_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
              self~2@
             ) (Poly%vstd!option.Option. next~97@)
           ))
           (and
            (=>
             %%location_label%%1
             (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ next~97@)
            )
            (=>
             (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_ensures. self~2@ next~97@)
             (and
              (=>
               %%location_label%%2
               (req%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@)
              )
              (=>
               (ens%bundle!journal.LinkedJournal_v.impl&%1.build_tight_shape. self~2@ root~4@)
               (and
                (=>
                 %%location_label%%3
                 (check_decrease_int (let
                   ((self~2!$ self~2@) (root~4!$ next~97@) (tight~6!$ inner~106@))
                   (bundle!journal.LinkedJournal_v.impl&%1.the_rank_of.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                     self~2!$
                    ) (Poly%vstd!option.Option. root~4!$)
                   )
                  ) decrease%init0@ false
                ))
                (and
                 (=>
                  %%location_label%%4
                  (req%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ next~97@ inner~106@)
                 )
                 (=>
                  (ens%bundle!journal.LinkedJournal_v.impl&%1.tight_sub_disk. self~2@ next~97@ inner~106@)
                  (=>
                   (= tmp%1@ (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                      tight~6@
                     ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                       (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                   ))))
                   (and
                    (=>
                     %%location_label%%5
                     tmp%1@
                    )
                    (=>
                     tmp%1@
                     (and
                      (and
                       (=>
                        (has_type other~165@ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
                        (=>
                         (and
                          (and
                           (and
                            (bundle!journal.LinkedJournal_v.impl&%1.decodable.? other~165@ (Poly%vstd!option.Option.
                              root~4@
                            ))
                            (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? other~165@)
                           )
                           (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                              tight~6@
                             ) (Poly%vstd!option.Option. root~4@)
                            ) (bundle!journal.LinkedJournal_v.impl&%1.iptr.? other~165@ (Poly%vstd!option.Option.
                              root~4@
                          ))))
                          (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~165@ (Poly%bundle!journal.LinkedJournal_v.DiskView.
                            tight~6@
                         )))
                         (=>
                          (= other_inner~242@ (bundle!journal.LinkedJournal_v.DiskView./DiskView (%I (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn
                               (%Poly%bundle!journal.LinkedJournal_v.DiskView. other~165@)
                             ))
                            ) (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                             (vstd!map.impl&%0.remove.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                 other~165@
                               ))
                              ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                 root~4@
                          )))))))
                          (=>
                           (= tmp%2@ (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                              inner~106@
                             ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                           ))))
                           (and
                            (=>
                             %%location_label%%6
                             tmp%2@
                            )
                            (=>
                             tmp%2@
                             (=>
                              (= tmp%3@ (bundle!journal.LinkedJournal_v.impl&%1.entries_wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                 other_inner~242@
                              )))
                              (and
                               (=>
                                %%location_label%%7
                                tmp%3@
                               )
                               (=>
                                tmp%3@
                                (=>
                                 (= tmp%4@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                    other_inner~242@
                                   ) other~165@
                                 ))
                                 (and
                                  (=>
                                   %%location_label%%8
                                   tmp%4@
                                  )
                                  (=>
                                   tmp%4@
                                   (=>
                                    (= tmp%5@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~165@ (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                       tight~6@
                                    )))
                                    (and
                                     (=>
                                      %%location_label%%9
                                      tmp%5@
                                     )
                                     (=>
                                      tmp%5@
                                      (=>
                                       (= tmp%6@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                          tight~6@
                                         ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                       ))
                                       (and
                                        (=>
                                         %%location_label%%10
                                         tmp%6@
                                        )
                                        (=>
                                         tmp%6@
                                         (=>
                                          (ens%bundle!journal.LinkedJournal_v.impl&%1.sub_disk_transitive_auto. 0)
                                          (=>
                                           (= tmp%7@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                              other_inner~242@
                                             ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                           ))
                                           (and
                                            (=>
                                             %%location_label%%11
                                             tmp%7@
                                            )
                                            (=>
                                             tmp%7@
                                             (and
                                              (=>
                                               (has_type addr~329@ TYPE%bundle!disk.GenericDisk_v.Address.)
                                               (=>
                                                (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                 (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                  TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                  (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                   (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                     (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                  )))
                                                 ) addr~329@
                                                )
                                                (=>
                                                 (= tmp%8@ (=>
                                                   (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                    (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                     )))
                                                    ) addr~329@
                                                   )
                                                   (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                    (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                     )))
                                                    ) addr~329@
                                                 )))
                                                 (and
                                                  (=>
                                                   %%location_label%%12
                                                   tmp%8@
                                                  )
                                                  (=>
                                                   tmp%8@
                                                   (=>
                                                    (= tmp%9@ (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                          (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                        ))
                                                       ) addr~329@
                                                      ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                          (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                        ))
                                                       ) addr~329@
                                                    )))
                                                    (and
                                                     (=>
                                                      %%location_label%%13
                                                      tmp%9@
                                                     )
                                                     (=>
                                                      tmp%9@
                                                      (=>
                                                       (= tmp%10@ (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                           TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                            ))
                                                           ) addr~329@
                                                          ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                             (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                          )))
                                                         ) (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                           TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                            ))
                                                           ) addr~329@
                                                          ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                             (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                       ))))))
                                                       (and
                                                        (=>
                                                         %%location_label%%14
                                                         tmp%10@
                                                        )
                                                        (=>
                                                         tmp%10@
                                                         (=>
                                                          (= aprior~465@ (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                             TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                              ))
                                                             ) addr~329@
                                                            ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                          )))))
                                                          (=>
                                                           (= tmp%11@ (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                             (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                 (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                              )))
                                                             ) addr~329@
                                                           ))
                                                           (and
                                                            (=>
                                                             %%location_label%%15
                                                             tmp%11@
                                                            )
                                                            (=>
                                                             tmp%11@
                                                             (=>
                                                              (= tmp%12@ (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                 self~2@
                                                                ) (Poly%vstd!option.Option. aprior~465@)
                                                              ))
                                                              (and
                                                               (=>
                                                                %%location_label%%16
                                                                tmp%12@
                                                               )
                                                               (=>
                                                                tmp%12@
                                                                (=>
                                                                 (= tmp%13@ (bundle!journal.LinkedJournal_v.impl&%1.wf.? other~165@))
                                                                 (and
                                                                  (=>
                                                                   %%location_label%%17
                                                                   tmp%13@
                                                                  )
                                                                  (=>
                                                                   tmp%13@
                                                                   (or
                                                                    (and
                                                                     (=>
                                                                      (= aprior~465@ root~4@)
                                                                      (or
                                                                       (and
                                                                        (=>
                                                                         (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                                            TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                             (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                             ))
                                                                            ) addr~329@
                                                                           ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                           )))
                                                                          ) root~4@
                                                                         )
                                                                         (=>
                                                                          (= tmp%14@ (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                             )))
                                                                            ) addr~329@
                                                                          ))
                                                                          (and
                                                                           (=>
                                                                            %%location_label%%18
                                                                            tmp%14@
                                                                           )
                                                                           (=>
                                                                            tmp%14@
                                                                            (=>
                                                                             (= tmp%15@ (> (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                 NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                                                                                   (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                  )
                                                                                 ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                                                                    (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                         (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                       ))
                                                                                      ) addr~329@
                                                                                     ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                ))))))))
                                                                               ) (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                 NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                                                                                   (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                  )
                                                                                 ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                                                                    root~4@
                                                                             )))))))
                                                                             (and
                                                                              (=>
                                                                               %%location_label%%19
                                                                               tmp%15@
                                                                              )
                                                                              (=>
                                                                               tmp%15@
                                                                               (=>
                                                                                (= tmp%16@ (< (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                                                                                      (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                     )
                                                                                    ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                                                                       (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                         TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                         TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                          (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                            (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                          ))
                                                                                         ) addr~329@
                                                                                        ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                   ))))))))
                                                                                  ) (%I (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    NAT NAT (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
                                                                                      (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                     )
                                                                                    ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                                                                       root~4@
                                                                                )))))))
                                                                                (and
                                                                                 (=>
                                                                                  %%location_label%%20
                                                                                  tmp%16@
                                                                                 )
                                                                                 (=>
                                                                                  tmp%16@
                                                                                  %%switch_label%%3
                                                                        ))))))))))
                                                                        (=>
                                                                         (not (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                                             TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                              ))
                                                                             ) addr~329@
                                                                            ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                            )))
                                                                           ) root~4@
                                                                         ))
                                                                         %%switch_label%%3
                                                                       ))
                                                                       (and
                                                                        (not %%switch_label%%3)
                                                                        (=>
                                                                         (= tmp%17@ (not (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                                              TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                 (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                               ))
                                                                              ) addr~329@
                                                                             ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                             )))
                                                                            ) root~4@
                                                                         )))
                                                                         (and
                                                                          (=>
                                                                           %%location_label%%21
                                                                           tmp%17@
                                                                          )
                                                                          (=>
                                                                           tmp%17@
                                                                           (=>
                                                                            (= tmp%18@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               other_inner~242@
                                                                              ) (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                            ))
                                                                            (and
                                                                             (=>
                                                                              %%location_label%%22
                                                                              tmp%18@
                                                                             )
                                                                             (=>
                                                                              tmp%18@
                                                                              (=>
                                                                               (= tmp%19@ (=>
                                                                                 (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                  (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                      (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                   )))
                                                                                  ) addr~329@
                                                                                 )
                                                                                 (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                  (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                      (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                   )))
                                                                                  ) addr~329@
                                                                               )))
                                                                               (and
                                                                                (=>
                                                                                 %%location_label%%23
                                                                                 tmp%19@
                                                                                )
                                                                                (=>
                                                                                 tmp%19@
                                                                                 (=>
                                                                                  (= tmp%20@ (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                      ))
                                                                                     ) addr~329@
                                                                                    ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                      ))
                                                                                     ) addr~329@
                                                                                  )))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%24
                                                                                    tmp%20@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%20@
                                                                                    (=>
                                                                                     (= tmp%21@ (not (= (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.? (vstd!map.impl&%0.index.?
                                                                                          TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                             (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                           ))
                                                                                          ) addr~329@
                                                                                         ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                            (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                         )))
                                                                                        ) root~4@
                                                                                     )))
                                                                                     (and
                                                                                      (=>
                                                                                       %%location_label%%25
                                                                                       tmp%21@
                                                                                      )
                                                                                      (=>
                                                                                       tmp%21@
                                                                                       (=>
                                                                                        (= tmp%22@ (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                           other_inner~242@
                                                                                          ) (Poly%vstd!option.Option. aprior~465@)
                                                                                        ))
                                                                                        (and
                                                                                         (=>
                                                                                          %%location_label%%26
                                                                                          tmp%22@
                                                                                         )
                                                                                         (=>
                                                                                          tmp%22@
                                                                                          %%switch_label%%2
                                                                     )))))))))))))))))))))
                                                                     (=>
                                                                      (not (= aprior~465@ root~4@))
                                                                      (=>
                                                                       (= tmp%23@ (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                          other_inner~242@
                                                                         ) (Poly%vstd!option.Option. aprior~465@)
                                                                       ))
                                                                       (and
                                                                        (=>
                                                                         %%location_label%%27
                                                                         tmp%23@
                                                                        )
                                                                        (=>
                                                                         tmp%23@
                                                                         %%switch_label%%2
                                                                    )))))
                                                                    (and
                                                                     (not %%switch_label%%2)
                                                                     (=>
                                                                      (= tmp%24@ (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                         other_inner~242@
                                                                        ) (Poly%vstd!option.Option. aprior~465@)
                                                                      ))
                                                                      (and
                                                                       (=>
                                                                        %%location_label%%28
                                                                        tmp%24@
                                                                       )
                                                                       (=>
                                                                        tmp%24@
                                                                        (=>
                                                                         %%location_label%%29
                                                                         (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                           other_inner~242@
                                                                          ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
                                                                            (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                              ))
                                                                             ) addr~329@
                                                                            ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                              )))))))))))))))))))))))))))))))))
                                              (=>
                                               (forall ((addr~329$ Poly)) (!
                                                 (=>
                                                  (has_type addr~329$ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                  (=>
                                                   (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                    (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                     )))
                                                    ) addr~329$
                                                   )
                                                   (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                     other_inner~242@
                                                    ) (Poly%vstd!option.Option. (bundle!journal.LinkedJournal_v.impl&%0.cropped_prior.?
                                                      (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                          (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                        ))
                                                       ) addr~329$
                                                      ) (I (bundle!journal.LinkedJournal_v.DiskView./DiskView/boundary_lsn (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                         (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                 ))))))))
                                                 :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                     (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                       (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                    )))
                                                   ) addr~329$
                                                 ))
                                                 :qid
                                                 user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_80
                                                 :skolemid
                                                 skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_80
                                               ))
                                               (=>
                                                (= tmp%25@ (bundle!journal.LinkedJournal_v.impl&%1.nondangling_pointers.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                   other_inner~242@
                                                )))
                                                (and
                                                 (=>
                                                  %%location_label%%30
                                                  tmp%25@
                                                 )
                                                 (=>
                                                  tmp%25@
                                                  (=>
                                                   (= tmp%26@ (bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                      other_inner~242@
                                                   )))
                                                   (and
                                                    (=>
                                                     %%location_label%%31
                                                     tmp%26@
                                                    )
                                                    (=>
                                                     tmp%26@
                                                     (or
                                                      (and
                                                       (=>
                                                        (is-vstd!option.Option./Some next~97@)
                                                        (=>
                                                         (= tmp%27@ (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                           (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                             (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                            )))
                                                           ) (vstd!option.Option./Some/_0 (%Poly%vstd!option.Option. (Poly%vstd!option.Option.
                                                              next~97@
                                                         )))))
                                                         (and
                                                          (=>
                                                           %%location_label%%32
                                                           tmp%27@
                                                          )
                                                          (=>
                                                           tmp%27@
                                                           %%switch_label%%1
                                                       ))))
                                                       (=>
                                                        (not (is-vstd!option.Option./Some next~97@))
                                                        %%switch_label%%1
                                                      ))
                                                      (and
                                                       (not %%switch_label%%1)
                                                       (=>
                                                        (= tmp%28@ (bundle!journal.LinkedJournal_v.impl&%1.is_nondangling_pointer.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                           other_inner~242@
                                                          ) (Poly%vstd!option.Option. next~97@)
                                                        ))
                                                        (and
                                                         (=>
                                                          %%location_label%%33
                                                          tmp%28@
                                                         )
                                                         (=>
                                                          tmp%28@
                                                          (=>
                                                           (= tmp%29@ (bundle!journal.LinkedJournal_v.impl&%1.wf.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                              other_inner~242@
                                                           )))
                                                           (and
                                                            (=>
                                                             %%location_label%%34
                                                             tmp%29@
                                                            )
                                                            (=>
                                                             tmp%29@
                                                             (=>
                                                              (= tmp%30@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                 other_inner~242@
                                                                ) (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                              ))
                                                              (and
                                                               (=>
                                                                %%location_label%%35
                                                                tmp%30@
                                                               )
                                                               (=>
                                                                tmp%30@
                                                                (and
                                                                 (=>
                                                                  %%location_label%%36
                                                                  (req%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. other_inner~242@
                                                                   next~97@ inner~106@
                                                                 ))
                                                                 (=>
                                                                  (ens%bundle!journal.LinkedJournal_v.impl&%1.iptr_ignores_extra_blocks. other_inner~242@
                                                                   next~97@ inner~106@
                                                                  )
                                                                  (and
                                                                   (=>
                                                                    (has_type a~880@ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                    (=>
                                                                     (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                      (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                       TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                       (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                        (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                          (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                       )))
                                                                      ) a~880@
                                                                     )
                                                                     (=>
                                                                      (= tmp%31@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                         other_inner~242@
                                                                        ) other~165@
                                                                      ))
                                                                      (and
                                                                       (=>
                                                                        %%location_label%%37
                                                                        tmp%31@
                                                                       )
                                                                       (=>
                                                                        tmp%31@
                                                                        (=>
                                                                         (= tmp%32@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~165@ (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                            tight~6@
                                                                         )))
                                                                         (and
                                                                          (=>
                                                                           %%location_label%%38
                                                                           tmp%32@
                                                                          )
                                                                          (=>
                                                                           tmp%32@
                                                                           (=>
                                                                            (= tmp%33@ (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               tight~6@
                                                                              ) (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
                                                                            ))
                                                                            (and
                                                                             (=>
                                                                              %%location_label%%39
                                                                              tmp%33@
                                                                             )
                                                                             (=>
                                                                              tmp%33@
                                                                              (=>
                                                                               (= tmp%34@ (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                 (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                  TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                  (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                   (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                     other~165@
                                                                                  )))
                                                                                 ) a~880@
                                                                               ))
                                                                               (and
                                                                                (=>
                                                                                 %%location_label%%40
                                                                                 tmp%34@
                                                                                )
                                                                                (=>
                                                                                 tmp%34@
                                                                                 (=>
                                                                                  (= tmp%35@ (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                        other~165@
                                                                                      ))
                                                                                     ) a~880@
                                                                                    ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                        (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                      ))
                                                                                     ) a~880@
                                                                                  )))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%41
                                                                                    tmp%35@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%35@
                                                                                    (=>
                                                                                     %%location_label%%42
                                                                                     (and
                                                                                      (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                       (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                                        )))
                                                                                       ) a~880@
                                                                                      )
                                                                                      (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                                         ))
                                                                                        ) a~880@
                                                                                       ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                         ))
                                                                                        ) a~880@
                                                                   )))))))))))))))))))))
                                                                   (=>
                                                                    (forall ((a~880$ Poly)) (!
                                                                      (=>
                                                                       (has_type a~880$ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                       (=>
                                                                        (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                           (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                             (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                          )))
                                                                         ) a~880$
                                                                        )
                                                                        (and
                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                           )))
                                                                          ) a~880$
                                                                         )
                                                                         (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                            ))
                                                                           ) a~880$
                                                                          ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                            (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                              (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                            ))
                                                                           ) a~880$
                                                                      )))))
                                                                      :pattern ((vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                         ))
                                                                        ) a~880$
                                                                      ))
                                                                      :pattern ((vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                        TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                         (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                           (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                         ))
                                                                        ) a~880$
                                                                      ))
                                                                      :qid
                                                                      user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_81
                                                                      :skolemid
                                                                      skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_81
                                                                    ))
                                                                    (=>
                                                                     (= tmp%36@ (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                        inner~106@
                                                                       ) (Poly%vstd!option.Option. next~97@)
                                                                     ))
                                                                     (and
                                                                      (=>
                                                                       %%location_label%%43
                                                                       tmp%36@
                                                                      )
                                                                      (=>
                                                                       tmp%36@
                                                                       (and
                                                                        (=>
                                                                         (has_type a~1027@ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                         (=>
                                                                          %%location_label%%44
                                                                          (=>
                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                             )))
                                                                            ) a~1027@
                                                                           )
                                                                           (and
                                                                            (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                 (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                              )))
                                                                             ) a~1027@
                                                                            )
                                                                            (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                 (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                               ))
                                                                              ) a~1027@
                                                                             ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                              TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                              (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                               (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                 (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                               ))
                                                                              ) a~1027@
                                                                        ))))))
                                                                        (=>
                                                                         (forall ((a~1027$ Poly)) (!
                                                                           (=>
                                                                            (has_type a~1027$ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                            (=>
                                                                             (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                              (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                               TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                               (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                  (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                               )))
                                                                              ) a~1027$
                                                                             )
                                                                             (and
                                                                              (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                               (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                 (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                   (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                )))
                                                                               ) a~1027$
                                                                              )
                                                                              (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                 (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                   (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                                 ))
                                                                                ) a~1027$
                                                                               ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                 (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                   (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                                 ))
                                                                                ) a~1027$
                                                                           )))))
                                                                           :pattern ((vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                              ))
                                                                             ) a~1027$
                                                                           ))
                                                                           :pattern ((vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                              ))
                                                                             ) a~1027$
                                                                           ))
                                                                           :qid
                                                                           user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_82
                                                                           :skolemid
                                                                           skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_82
                                                                         ))
                                                                         (=>
                                                                          (= m1~1089@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                             (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                               (Poly%bundle!journal.LinkedJournal_v.DiskView. other_inner~242@)
                                                                          )))))
                                                                          (=>
                                                                           (= m2~1100@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                              (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                (Poly%bundle!journal.LinkedJournal_v.DiskView. inner~106@)
                                                                           )))))
                                                                           (and
                                                                            (and
                                                                             (=>
                                                                              (has_type key~1123@ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                              (=>
                                                                               %%location_label%%45
                                                                               (and
                                                                                (and
                                                                                 (=>
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m1~1089@
                                                                                    )
                                                                                   ) key~1123@
                                                                                  )
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m2~1100@
                                                                                    )
                                                                                   ) key~1123@
                                                                                 ))
                                                                                 (=>
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m2~1100@
                                                                                    )
                                                                                   ) key~1123@
                                                                                  )
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m1~1089@
                                                                                    )
                                                                                   ) key~1123@
                                                                                )))
                                                                                (=>
                                                                                 (and
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m1~1089@
                                                                                    )
                                                                                   ) key~1123@
                                                                                  )
                                                                                  (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                    TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     m2~1100@
                                                                                    )
                                                                                   ) key~1123@
                                                                                 ))
                                                                                 (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    m1~1089@
                                                                                   ) key~1123@
                                                                                  ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    m2~1100@
                                                                                   ) key~1123@
                                                                             ))))))
                                                                             (=>
                                                                              (forall ((key~1123$ Poly)) (!
                                                                                (=>
                                                                                 (has_type key~1123$ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                                 (and
                                                                                  (and
                                                                                   (=>
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m1~1089@
                                                                                      )
                                                                                     ) key~1123$
                                                                                    )
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m2~1100@
                                                                                      )
                                                                                     ) key~1123$
                                                                                   ))
                                                                                   (=>
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m2~1100@
                                                                                      )
                                                                                     ) key~1123$
                                                                                    )
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m1~1089@
                                                                                      )
                                                                                     ) key~1123$
                                                                                  )))
                                                                                  (=>
                                                                                   (and
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m1~1089@
                                                                                      )
                                                                                     ) key~1123$
                                                                                    )
                                                                                    (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                      TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                      (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                       m2~1100@
                                                                                      )
                                                                                     ) key~1123$
                                                                                   ))
                                                                                   (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      m1~1089@
                                                                                     ) key~1123$
                                                                                    ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                     TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                     (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                      m2~1100@
                                                                                     ) key~1123$
                                                                                )))))
                                                                                :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                  (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                   TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    m1~1089@
                                                                                   )
                                                                                  ) key~1123$
                                                                                ))
                                                                                :qid
                                                                                user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_83
                                                                                :skolemid
                                                                                skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_83
                                                                              ))
                                                                              (=>
                                                                               (= tmp%37@ (ext_eq false (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                  TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                 ) (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
                                                                                 (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                  m1~1089@
                                                                                 ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                  m2~1100@
                                                                               )))
                                                                               (and
                                                                                (=>
                                                                                 %%location_label%%46
                                                                                 tmp%37@
                                                                                )
                                                                                (=>
                                                                                 tmp%37@
                                                                                 (=>
                                                                                  %%location_label%%47
                                                                                  (= m1~1089@ m2~1100@)
                                                                            ))))))
                                                                            (=>
                                                                             (= m1~1089@ m2~1100@)
                                                                             (=>
                                                                              (= tmp%38@ (= other_inner~242@ inner~106@))
                                                                              (and
                                                                               (=>
                                                                                %%location_label%%48
                                                                                tmp%38@
                                                                               )
                                                                               (=>
                                                                                tmp%38@
                                                                                (=>
                                                                                 (= m1~1264@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                   (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                      other~165@
                                                                                 )))))
                                                                                 (=>
                                                                                  (= m2~1275@ (%Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                    (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                     (bundle!journal.LinkedJournal_v.DiskView./DiskView/entries (%Poly%bundle!journal.LinkedJournal_v.DiskView.
                                                                                       (Poly%bundle!journal.LinkedJournal_v.DiskView. tight~6@)
                                                                                  )))))
                                                                                  (and
                                                                                   (and
                                                                                    (=>
                                                                                     (has_type key~1298@ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                                     (=>
                                                                                      %%location_label%%49
                                                                                      (and
                                                                                       (and
                                                                                        (=>
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m1~1264@
                                                                                           )
                                                                                          ) key~1298@
                                                                                         )
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m2~1275@
                                                                                           )
                                                                                          ) key~1298@
                                                                                        ))
                                                                                        (=>
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m2~1275@
                                                                                           )
                                                                                          ) key~1298@
                                                                                         )
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m1~1264@
                                                                                           )
                                                                                          ) key~1298@
                                                                                       )))
                                                                                       (=>
                                                                                        (and
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m1~1264@
                                                                                           )
                                                                                          ) key~1298@
                                                                                         )
                                                                                         (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                           TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                           (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                            m2~1275@
                                                                                           )
                                                                                          ) key~1298@
                                                                                        ))
                                                                                        (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                           m1~1264@
                                                                                          ) key~1298@
                                                                                         ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                           m2~1275@
                                                                                          ) key~1298@
                                                                                    ))))))
                                                                                    (=>
                                                                                     (forall ((key~1298$ Poly)) (!
                                                                                       (=>
                                                                                        (has_type key~1298$ TYPE%bundle!disk.GenericDisk_v.Address.)
                                                                                        (and
                                                                                         (and
                                                                                          (=>
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m1~1264@
                                                                                             )
                                                                                            ) key~1298$
                                                                                           )
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m2~1275@
                                                                                             )
                                                                                            ) key~1298$
                                                                                          ))
                                                                                          (=>
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m2~1275@
                                                                                             )
                                                                                            ) key~1298$
                                                                                           )
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m1~1264@
                                                                                             )
                                                                                            ) key~1298$
                                                                                         )))
                                                                                         (=>
                                                                                          (and
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m1~1264@
                                                                                             )
                                                                                            ) key~1298$
                                                                                           )
                                                                                           (vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                             TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                             (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                              m2~1275@
                                                                                             )
                                                                                            ) key~1298$
                                                                                          ))
                                                                                          (= (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                             m1~1264@
                                                                                            ) key~1298$
                                                                                           ) (vstd!map.impl&%0.index.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                            TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                            (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                             m2~1275@
                                                                                            ) key~1298$
                                                                                       )))))
                                                                                       :pattern ((vstd!set.impl&%0.contains.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                         (vstd!map.impl&%0.dom.? TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                          TYPE%bundle!journal.LinkedJournal_v.JournalRecord. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                          (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                           m1~1264@
                                                                                          )
                                                                                         ) key~1298$
                                                                                       ))
                                                                                       :qid
                                                                                       user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_85
                                                                                       :skolemid
                                                                                       skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_85
                                                                                     ))
                                                                                     (=>
                                                                                      (= tmp%39@ (ext_eq false (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address.
                                                                                         TYPE%bundle!journal.LinkedJournal_v.JournalRecord.
                                                                                        ) (TYPE%vstd!map.Map. TYPE%bundle!disk.GenericDisk_v.Address. TYPE%bundle!journal.LinkedJournal_v.JournalRecord.)
                                                                                        (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                         m1~1264@
                                                                                        ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./bundle!journal.LinkedJournal_v.JournalRecord.>.
                                                                                         m2~1275@
                                                                                      )))
                                                                                      (and
                                                                                       (=>
                                                                                        %%location_label%%50
                                                                                        tmp%39@
                                                                                       )
                                                                                       (=>
                                                                                        tmp%39@
                                                                                        (=>
                                                                                         %%location_label%%51
                                                                                         (= m1~1264@ m2~1275@)
                                                                                   ))))))
                                                                                   (=>
                                                                                    (= m1~1264@ m2~1275@)
                                                                                    (=>
                                                                                     (= tmp%40@ (= (%Poly%bundle!journal.LinkedJournal_v.DiskView. other~165@) tight~6@))
                                                                                     (and
                                                                                      (=>
                                                                                       %%location_label%%52
                                                                                       tmp%40@
                                                                                      )
                                                                                      (=>
                                                                                       tmp%40@
                                                                                       (=>
                                                                                        %%location_label%%53
                                                                                        (= (%Poly%bundle!journal.LinkedJournal_v.DiskView. other~165@) tight~6@)
                       )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       (=>
                        (forall ((other~165$ Poly)) (!
                          (=>
                           (has_type other~165$ TYPE%bundle!journal.LinkedJournal_v.DiskView.)
                           (=>
                            (and
                             (and
                              (and
                               (bundle!journal.LinkedJournal_v.impl&%1.decodable.? other~165$ (Poly%vstd!option.Option.
                                 root~4@
                               ))
                               (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? other~165$)
                              )
                              (= (bundle!journal.LinkedJournal_v.impl&%1.iptr.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                 tight~6@
                                ) (Poly%vstd!option.Option. root~4@)
                               ) (bundle!journal.LinkedJournal_v.impl&%1.iptr.? other~165$ (Poly%vstd!option.Option.
                                 root~4@
                             ))))
                             (bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~165$ (Poly%bundle!journal.LinkedJournal_v.DiskView.
                               tight~6@
                            )))
                            (= (%Poly%bundle!journal.LinkedJournal_v.DiskView. other~165$) tight~6@)
                          ))
                          :pattern ((bundle!journal.LinkedJournal_v.impl&%1.is_sub_disk.? other~165$ (Poly%bundle!journal.LinkedJournal_v.DiskView.
                             tight~6@
                          )))
                          :qid
                          user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_87
                          :skolemid
                          skolem_user_bundle__journal__LinkedJournal_v__impl&%1__tight_sub_disk_87
                        ))
                        (=>
                         (= tmp%41@ (bundle!journal.LinkedJournal_v.impl&%1.decodable.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                            tight~6@
                           ) (Poly%vstd!option.Option. root~4@)
                         ))
                         (and
                          (=>
                           %%location_label%%54
                           tmp%41@
                          )
                          (=>
                           tmp%41@
                           (=>
                            (= tmp%42@ (bundle!journal.LinkedJournal_v.impl&%1.acyclic.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                               tight~6@
                            )))
                            (and
                             (=>
                              %%location_label%%55
                              tmp%42@
                             )
                             (=>
                              tmp%42@
                              (=>
                               %%location_label%%56
                               (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                                 tight~6@
                                ) (Poly%vstd!option.Option. root~4@)
                      ))))))))))
                      (=>
                       (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                         tight~6@
                        ) (Poly%vstd!option.Option. root~4@)
                       )
                       (=>
                        (= tmp%43@ (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
                           tight~6@
                          ) (Poly%vstd!option.Option. root~4@)
                        ))
                        (and
                         (=>
                          %%location_label%%57
                          tmp%43@
                         )
                         (=>
                          tmp%43@
                          %%switch_label%%0
        ))))))))))))))))))
        (and
         (not %%switch_label%%0)
         (=>
          (= tmp%50@ (bundle!journal.LinkedJournal_v.impl&%1.valid_ranking.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
             tight~6@
            ) (Poly%vstd!map.Map<bundle!disk.GenericDisk_v.Address./nat.>. (bundle!journal.LinkedJournal_v.impl&%1.the_ranking.?
              (Poly%bundle!journal.LinkedJournal_v.DiskView. self~2@)
          ))))
          (and
           (=>
            %%location_label%%58
            tmp%50@
           )
           (=>
            tmp%50@
            (=>
             %%location_label%%59
             (bundle!journal.LinkedJournal_v.impl&%1.is_tight.? (Poly%bundle!journal.LinkedJournal_v.DiskView.
               tight~6@
              ) (Poly%vstd!option.Option. root~4@)
 )))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)
