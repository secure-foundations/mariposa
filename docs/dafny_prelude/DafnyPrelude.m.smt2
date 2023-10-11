(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@Field_3928 0)
(declare-sort T@Box 0)
(declare-sort T@Field_29474 0)
(declare-sort T@Field_26410 0)
(declare-datatypes ((T@PolymorphicMapType_21225 0)) (((PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (Array T@Field_3928 T@Box)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (Array T@Field_29474 T@Box)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (Array T@Field_26410 T@Box)) ) ) ))
(declare-sort T@Ty 0)
(declare-fun TBool () T@Ty)
(declare-fun TChar () T@Ty)
(declare-fun TInt () T@Ty)
(declare-fun TReal () T@Ty)
(declare-fun TORDINAL () T@Ty)
(declare-sort T@TyTag 0)
(declare-fun TagBool () T@TyTag)
(declare-fun TagChar () T@TyTag)
(declare-fun TagInt () T@TyTag)
(declare-fun TagReal () T@TyTag)
(declare-fun TagORDINAL () T@TyTag)
(declare-fun TagSet () T@TyTag)
(declare-fun TagISet () T@TyTag)
(declare-fun TagMultiSet () T@TyTag)
(declare-fun TagSeq () T@TyTag)
(declare-fun TagMap () T@TyTag)
(declare-fun TagIMap () T@TyTag)
(declare-fun TagClass () T@TyTag)
(declare-sort T@ClassName 0)
(declare-fun class._System.int () T@ClassName)
(declare-fun class._System.bool () T@ClassName)
(declare-fun class._System.set () T@ClassName)
(declare-fun class._System.seq () T@ClassName)
(declare-fun class._System.multiset () T@ClassName)
(declare-fun alloc () T@Field_3928)
(declare-sort T@NameFamily 0)
(declare-fun allocName () T@NameFamily)
(declare-sort T@Map_20925_20926 0)
(declare-fun |Map#Disjoint_20925_20926| (T@Map_20925_20926 T@Map_20925_20926) Bool)
(declare-fun |Map#Domain_12638_12639| (T@Map_20925_20926) (Array T@Box Bool))
(declare-fun FDim_3928 (T@Field_3928) Int)
(declare-fun Tag (T@Ty) T@TyTag)
(declare-fun DeclName_3928 (T@Field_3928) T@NameFamily)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-sort T@ref 0)
(declare-fun $IsAlloc_1910 (Int T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun TBitvector (Int) T@Ty)
(declare-fun q@Real (Int) Real)
(declare-fun |MultiSet#Card_12631| ((Array T@Box Int)) Int)
(declare-fun |MultiSet#Difference_12631| ((Array T@Box Int) (Array T@Box Int)) (Array T@Box Int))
(declare-fun |MultiSet#Intersection_12631| ((Array T@Box Int) (Array T@Box Int)) (Array T@Box Int))
(declare-fun |MultiSet#Union_12631| ((Array T@Box Int) (Array T@Box Int)) (Array T@Box Int))
(declare-fun $HeapSucc ((Array T@ref T@PolymorphicMapType_21225) (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Unbox_926 (T@Box) Bool)
(declare-fun |ORD#Less| (T@Box T@Box) Bool)
(declare-sort T@Seq_20794 0)
(declare-fun |Seq#Contains_20794| (T@Seq_20794 T@Box) Bool)
(declare-fun |Seq#Build_13286| (T@Seq_20794 T@Box) T@Seq_20794)
(declare-fun |Map#Glue_13429_13432| ((Array T@Box Bool) (Array T@Box T@Box) T@Ty) T@Map_20925_20926)
(declare-fun |Map#Elements_12638_12639| (T@Map_20925_20926) (Array T@Box T@Box))
(declare-sort T@IMap_21069_21070 0)
(declare-fun |IMap#Domain_12649_12650| (T@IMap_21069_21070) (Array T@Box Bool))
(declare-fun |IMap#Glue_13507_13510| ((Array T@Box Bool) (Array T@Box T@Box) T@Ty) T@IMap_21069_21070)
(declare-fun |IMap#Elements_12649_12650| (T@IMap_21069_21070) (Array T@Box T@Box))
(declare-fun $Is_869 (Int T@Ty) Bool)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun |ORD#Minus| (T@Box T@Box) T@Box)
(declare-fun |ORD#FromNat| (Int) T@Box)
(declare-fun |ORD#Offset| (T@Box) Int)
(declare-fun |Seq#Empty_12631| () T@Seq_20794)
(declare-fun |Seq#Length_12635| (T@Seq_20794) Int)
(declare-fun |Seq#Drop_20794| (T@Seq_20794 Int) T@Seq_20794)
(declare-fun $Is_12584 ((Array T@Box Int) T@Ty) Bool)
(declare-fun TMultiSet (T@Ty) T@Ty)
(declare-fun $IsGoodMultiSet_12631 ((Array T@Box Int)) Bool)
(declare-fun |MultiSet#FromSeq_12631| (T@Seq_20794) (Array T@Box Int))
(declare-fun |Seq#Index_12635| (T@Seq_20794 Int) T@Box)
(declare-fun |Seq#Update_13347| (T@Seq_20794 Int T@Box) T@Seq_20794)
(declare-fun |Set#Union_17766| ((Array T@Box Bool) (Array T@Box Bool)) (Array T@Box Bool))
(declare-fun |Set#Intersection_17766| ((Array T@Box Bool) (Array T@Box Bool)) (Array T@Box Bool))
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun |Seq#Take_13347| (T@Seq_20794 Int) T@Seq_20794)
(declare-fun |Seq#Append_12631| (T@Seq_20794 T@Seq_20794) T@Seq_20794)
(declare-fun |Map#Card_20925_20926| (T@Map_20925_20926) Int)
(declare-fun |Map#Build_12638_12639| (T@Map_20925_20926 T@Box T@Box) T@Map_20925_20926)
(declare-fun |Set#Singleton_17766| (T@Box) (Array T@Box Bool))
(declare-fun |Seq#FromArray| ((Array T@ref T@PolymorphicMapType_21225) T@ref) T@Seq_20794)
(declare-fun _System.array.Length (T@ref) Int)
(declare-fun $Unbox_12809 (T@Box) T@Box)
(declare-fun IndexField (Int) T@Field_26410)
(declare-fun |Set#Card_17766| ((Array T@Box Bool)) Int)
(declare-fun |Map#Subtract_12638_12639| (T@Map_20925_20926 (Array T@Box Bool)) T@Map_20925_20926)
(declare-fun |IMap#Subtract_12649_12650| (T@IMap_21069_21070 (Array T@Box Bool)) T@IMap_21069_21070)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun $Is_12560 ((Array T@Box Bool) T@Ty) Bool)
(declare-fun TSet (T@Ty) T@Ty)
(declare-fun $IsBox_12550 (T@Box T@Ty) Bool)
(declare-fun TISet (T@Ty) T@Ty)
(declare-fun |Math#clip| (Int) Int)
(declare-fun $Is_20853 (T@Seq_20794 T@Ty) Bool)
(declare-fun TSeq (T@Ty) T@Ty)
(declare-sort T@HandleType 0)
(declare-fun |Seq#Create| (T@Ty (Array T@ref T@PolymorphicMapType_21225) Int T@HandleType) T@Seq_20794)
(declare-fun $IsGoodHeap ((Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $$Language$Dafny () Bool)
(declare-fun |Seq#Equal_20794| (T@Seq_20794 T@Seq_20794) Bool)
(declare-fun SetRef_to_SetBox ((Array T@ref Bool)) (Array T@Box Bool))
(declare-fun $Unbox_12740 (T@Box) T@ref)
(declare-fun |Seq#Rank_13371| (T@Seq_20794) Int)
(declare-fun MultiIndexField (T@Field_26410 Int) T@Field_26410)
(declare-fun FDim_12809 (T@Field_26410) Int)
(declare-fun |MultiSet#UnionOne_12631| ((Array T@Box Int) T@Box) (Array T@Box Int))
(declare-fun $IsGhostField_3928 (T@Field_3928) Bool)
(declare-fun $OneHeap () (Array T@ref T@PolymorphicMapType_21225))
(declare-sort T@DatatypeType 0)
(declare-fun DtRank (T@DatatypeType) Int)
(declare-fun $Unbox_13374 (T@Box) T@DatatypeType)
(declare-fun Apply1 (T@Ty T@Ty (Array T@ref T@PolymorphicMapType_21225) T@HandleType T@Box) T@Box)
(declare-fun $Box_552 (Int) T@Box)
(declare-fun $IsAllocBox_13729 (T@Box T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_12809 (T@Box) T@Box)
(declare-fun $IsAlloc_12448 (T@Box T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_12882 (T@ref) T@Box)
(declare-fun $IsAlloc_12882 (T@ref T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_12753 (T@DatatypeType) T@Box)
(declare-fun $IsAlloc_12753 (T@DatatypeType T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_21090 (T@IMap_21069_21070) T@Box)
(declare-fun $IsAlloc_24132 (T@IMap_21069_21070 T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_20946 (T@Map_20925_20926) T@Box)
(declare-fun $IsAlloc_23870 (T@Map_20925_20926 T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_20812 (T@Seq_20794) T@Box)
(declare-fun $IsAlloc_23682 (T@Seq_20794 T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_12581 ((Array T@Box Int)) T@Box)
(declare-fun $IsAlloc_12685 ((Array T@Box Int) T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_12565 ((Array T@Box Bool)) T@Box)
(declare-fun $IsAlloc_12673 ((Array T@Box Bool) T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-sort T@char 0)
(declare-fun $Box_12554 (T@char) T@Box)
(declare-fun $IsAlloc_12666 (T@char T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_926 (Bool) T@Box)
(declare-fun $IsAlloc_1948 (Bool T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $Box_594 (Real) T@Box)
(declare-fun $IsAlloc_1929 (Real T@Ty (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun |MultiSet#Empty_12631| () (Array T@Box Int))
(declare-fun |ORD#IsNat| (T@Box) Bool)
(declare-fun |ORD#Plus| (T@Box T@Box) T@Box)
(declare-fun |char#Minus| (T@char T@char) T@char)
(declare-fun |char#FromInt| (Int) T@char)
(declare-fun |char#ToInt| (T@char) Int)
(declare-fun |char#Plus| (T@char T@char) T@char)
(declare-fun |Map#Empty_20925_20926| () T@Map_20925_20926)
(declare-fun |Map#Values_12644_12645| (T@Map_20925_20926) (Array T@Box Bool))
(declare-fun |IMap#Empty_21069_21070| () T@IMap_21069_21070)
(declare-fun |IMap#Values_12655_12656| (T@IMap_21069_21070) (Array T@Box Bool))
(declare-fun |Set#Disjoint_17766| ((Array T@Box Bool) (Array T@Box Bool)) Bool)
(declare-fun |Set#Difference_17766| ((Array T@Box Bool) (Array T@Box Bool)) (Array T@Box Bool))
(declare-fun |Map#Items_12644_12645| (T@Map_20925_20926) (Array T@Box Bool))
(declare-fun _System.Tuple2._0 (T@DatatypeType) T@Box)
(declare-fun _System.Tuple2._1 (T@DatatypeType) T@Box)
(declare-fun |IMap#Items_12655_12656| (T@IMap_21069_21070) (Array T@Box Bool))
(declare-fun TMap (T@Ty T@Ty) T@Ty)
(declare-fun TIMap (T@Ty T@Ty) T@Ty)
(declare-fun |ORD#LessThanLimit| (T@Box T@Box) Bool)
(declare-fun |Map#Equal_20925_20926| (T@Map_20925_20926 T@Map_20925_20926) Bool)
(declare-fun |IMap#Equal_21069_21070| (T@IMap_21069_21070 T@IMap_21069_21070) Bool)
(declare-fun |Set#UnionOne_17766| ((Array T@Box Bool) T@Box) (Array T@Box Bool))
(declare-fun |ISet#Empty_18379| () (Array T@Box Bool))
(declare-fun q@Int (Real) Int)
(declare-fun LitInt (Int) Int)
(declare-fun LitReal (Real) Real)
(declare-fun Lit_13549 (T@Box) T@Box)
(declare-fun Lit_552 (Int) Int)
(declare-fun Lit_594 (Real) Real)
(declare-fun Lit_926 (Bool) Bool)
(declare-fun Lit_12554 (T@char) T@char)
(declare-fun Lit_12565 ((Array T@Box Bool)) (Array T@Box Bool))
(declare-fun Lit_12581 ((Array T@Box Int)) (Array T@Box Int))
(declare-fun Lit_20812 (T@Seq_20794) T@Seq_20794)
(declare-fun Lit_20946 (T@Map_20925_20926) T@Map_20925_20926)
(declare-fun Lit_21090 (T@IMap_21069_21070) T@IMap_21069_21070)
(declare-fun Lit_12753 (T@DatatypeType) T@DatatypeType)
(declare-fun Lit_12882 (T@ref) T@ref)
(declare-fun |#_System._tuple#2._#Make2| (T@Box T@Box) T@DatatypeType)
(declare-fun $Is_12448 (T@Box T@Ty) Bool)
(declare-fun $Is_12882 (T@ref T@Ty) Bool)
(declare-fun $Is_12753 (T@DatatypeType T@Ty) Bool)
(declare-fun $Is_21138 (T@IMap_21069_21070 T@Ty) Bool)
(declare-fun $Is_20994 (T@Map_20925_20926 T@Ty) Bool)
(declare-fun $Is_12555 (T@char T@Ty) Bool)
(declare-fun $Is_935 (Bool T@Ty) Bool)
(declare-fun $Is_902 (Real T@Ty) Bool)
(declare-fun |MultiSet#FromSet_12631| ((Array T@Box Bool)) (Array T@Box Int))
(declare-fun |Seq#Singleton_12635| (T@Box) T@Seq_20794)
(declare-fun |MultiSet#Singleton_12631| (T@Box) (Array T@Box Int))
(declare-fun $AlwaysAllocated (T@Ty) Bool)
(declare-fun Inv0_TMap (T@Ty) T@Ty)
(declare-fun Inv1_TMap (T@Ty) T@Ty)
(declare-fun Inv0_TIMap (T@Ty) T@Ty)
(declare-fun Inv1_TIMap (T@Ty) T@Ty)
(declare-fun Inv0_TBitvector (T@Ty) Int)
(declare-fun Inv0_TSet (T@Ty) T@Ty)
(declare-fun Inv0_TISet (T@Ty) T@Ty)
(declare-fun Inv0_TMultiSet (T@Ty) T@Ty)
(declare-fun Inv0_TSeq (T@Ty) T@Ty)
(declare-fun $Unbox_21073 (T@Box) T@IMap_21069_21070)
(declare-fun $Unbox_20929 (T@Box) T@Map_20925_20926)
(declare-fun $Unbox_20797 (T@Box) T@Seq_20794)
(declare-fun $Unbox_12581 (T@Box) (Array T@Box Int))
(declare-fun $Unbox_12560 (T@Box) (Array T@Box Bool))
(declare-fun $Unbox_12554 (T@Box) T@char)
(declare-fun $Unbox_893 (T@Box) Real)
(declare-fun $Unbox_860 (T@Box) Int)
(declare-fun IndexField_Inverse_12809 (T@Field_26410) Int)
(declare-fun |Map#Merge_12638_12639| (T@Map_20925_20926 T@Map_20925_20926) T@Map_20925_20926)
(declare-fun |IMap#Merge_12649_12650| (T@IMap_21069_21070 T@IMap_21069_21070) T@IMap_21069_21070)
(declare-fun |IMap#Build_12649_12650| (T@IMap_21069_21070 T@Box T@Box) T@IMap_21069_21070)
(declare-fun |Set#Empty_17766| () (Array T@Box Bool))
(declare-fun TypeTuple (T@ClassName T@ClassName) T@ClassName)
(declare-fun TypeTupleCar (T@ClassName) T@ClassName)
(declare-fun TypeTupleCdr (T@ClassName) T@ClassName)
(declare-fun MultiIndexField_Inverse0_12814 (T@Field_26410) T@Field_26410)
(declare-fun MultiIndexField_Inverse1_12814 (T@Field_26410) Int)
(declare-fun FieldOfDecl_3928 (T@ClassName T@NameFamily) T@Field_3928)
(declare-fun DeclType_3928 (T@Field_3928) T@ClassName)
(declare-fun |Seq#Build_inv0_13286| (T@Seq_20794) T@Seq_20794)
(declare-fun |Seq#Build_inv1_13286| (T@Seq_20794) T@Box)
(declare-fun BoxRank (T@Box) Int)
(declare-fun Tclass._System.object? () T@Ty)
(declare-fun |Seq#SameUntil_20794| (T@Seq_20794 T@Seq_20794 Int) Bool)
(declare-fun $HeapSuccGhost ((Array T@ref T@PolymorphicMapType_21225) (Array T@ref T@PolymorphicMapType_21225)) Bool)
(declare-fun $IsGhostField_26410 (T@Field_26410) Bool)
(declare-fun $IsGhostField_29474 (T@Field_29474) Bool)
(declare-fun Tclass._System.Tuple2 (T@Ty T@Ty) T@Ty)
(assert (and (distinct TBool TChar TInt TReal TORDINAL)(distinct TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass)(distinct class._System.int class._System.bool class._System.set class._System.seq class._System.multiset))
)
(assert (forall ((m T@Map_20925_20926) (|m'| T@Map_20925_20926) ) (! (= (|Map#Disjoint_20925_20926| m |m'|) (forall ((o T@Box) ) (!  (or (not (select (|Map#Domain_12638_12639| m) o)) (not (select (|Map#Domain_12638_12639| |m'|) o)))
 :qid |DafnyPreludebpl.1320:38|
 :skolemid |304|
 :pattern ( (select (|Map#Domain_12638_12639| m) o))
 :pattern ( (select (|Map#Domain_12638_12639| |m'|) o))
)))
 :qid |DafnyPreludebpl.1318:21|
 :skolemid |305|
 :pattern ( (|Map#Disjoint_20925_20926| m |m'|))
)))
(assert (= (FDim_3928 alloc) 0))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (= (DeclName_3928 alloc) allocName))
(assert (forall ((x Int) (y Int) ) (! (= (INTERNAL_div_boogie x y) (div x y))
 :qid |DafnyPreludebpl.1454:30|
 :skolemid |335|
 :pattern ( (INTERNAL_div_boogie x y))
)))
(assert (forall ((x@@0 Int) (y@@0 Int) ) (! (= (Div x@@0 y@@0) (div x@@0 y@@0))
 :qid |DafnyPreludebpl.1462:14|
 :skolemid |342|
 :pattern ( (Div x@@0 y@@0))
)))
(assert (forall ((v Int) (h (Array T@ref T@PolymorphicMapType_21225)) ) (! ($IsAlloc_1910 v (TBitvector 0) h)
 :qid |DafnyPreludebpl.293:15|
 :skolemid |65|
 :pattern ( ($IsAlloc_1910 v (TBitvector 0) h))
)))
(assert (forall ((x@@1 Int) ) (! (= (q@Real x@@1) (to_real x@@1))
 :qid |DafnyPreludebpl.577:15|
 :skolemid |113|
 :pattern ( (q@Real x@@1))
)))
(assert (forall ((a (Array T@Box Int)) (b (Array T@Box Int)) ) (!  (and (= (+ (+ (|MultiSet#Card_12631| (|MultiSet#Difference_12631| a b)) (|MultiSet#Card_12631| (|MultiSet#Difference_12631| b a))) (* 2 (|MultiSet#Card_12631| (|MultiSet#Intersection_12631| a b)))) (|MultiSet#Card_12631| (|MultiSet#Union_12631| a b))) (= (|MultiSet#Card_12631| (|MultiSet#Difference_12631| a b)) (- (|MultiSet#Card_12631| a) (|MultiSet#Card_12631| (|MultiSet#Intersection_12631| a b)))))
 :qid |DafnyPreludebpl.892:18|
 :skolemid |203|
 :pattern ( (|MultiSet#Card_12631| (|MultiSet#Difference_12631| a b)))
)))
(assert (forall ((h@@0 (Array T@ref T@PolymorphicMapType_21225)) (k (Array T@ref T@PolymorphicMapType_21225)) ) (!  (=> ($HeapSucc h@@0 k) (forall ((o@@0 T@ref) ) (!  (=> ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@0 o@@0)) alloc)) ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select k o@@0)) alloc)))
 :qid |DafnyPreludebpl.607:30|
 :skolemid |117|
 :pattern ( ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select k o@@0)) alloc)))
)))
 :qid |DafnyPreludebpl.606:15|
 :skolemid |118|
 :pattern ( ($HeapSucc h@@0 k))
)))
(assert (forall ((o@@1 T@Box) (p T@Box) (r T@Box) ) (!  (=> (and (|ORD#Less| o@@1 p) (|ORD#Less| p r)) (|ORD#Less| o@@1 r))
 :qid |DafnyPreludebpl.425:15|
 :skolemid |89|
 :pattern ( (|ORD#Less| o@@1 p) (|ORD#Less| p r))
 :pattern ( (|ORD#Less| o@@1 p) (|ORD#Less| o@@1 r))
)))
(assert (forall ((s T@Seq_20794) (v@@0 T@Box) (x@@2 T@Box) ) (! (= (|Seq#Contains_20794| (|Seq#Build_13286| s v@@0) x@@2)  (or (= v@@0 x@@2) (|Seq#Contains_20794| s x@@2)))
 :qid |DafnyPreludebpl.1042:18|
 :skolemid |240|
 :pattern ( (|Seq#Contains_20794| (|Seq#Build_13286| s v@@0) x@@2))
)))
(assert (forall ((a@@0 (Array T@Box Bool)) (b@@0 (Array T@Box T@Box)) (t T@Ty) ) (! (= (|Map#Domain_12638_12639| (|Map#Glue_13429_13432| a@@0 b@@0 t)) a@@0)
 :qid |DafnyPreludebpl.1255:21|
 :skolemid |289|
 :pattern ( (|Map#Domain_12638_12639| (|Map#Glue_13429_13432| a@@0 b@@0 t)))
)))
(assert (forall ((a@@1 (Array T@Box Bool)) (b@@1 (Array T@Box T@Box)) (t@@0 T@Ty) ) (! (= (|Map#Elements_12638_12639| (|Map#Glue_13429_13432| a@@1 b@@1 t@@0)) b@@1)
 :qid |DafnyPreludebpl.1258:21|
 :skolemid |290|
 :pattern ( (|Map#Elements_12638_12639| (|Map#Glue_13429_13432| a@@1 b@@1 t@@0)))
)))
(assert (forall ((a@@2 (Array T@Box Bool)) (b@@2 (Array T@Box T@Box)) (t@@1 T@Ty) ) (! (= (|IMap#Domain_12649_12650| (|IMap#Glue_13507_13510| a@@2 b@@2 t@@1)) a@@2)
 :qid |DafnyPreludebpl.1390:21|
 :skolemid |319|
 :pattern ( (|IMap#Domain_12649_12650| (|IMap#Glue_13507_13510| a@@2 b@@2 t@@1)))
)))
(assert (forall ((a@@3 (Array T@Box Bool)) (b@@3 (Array T@Box T@Box)) (t@@2 T@Ty) ) (! (= (|IMap#Elements_12649_12650| (|IMap#Glue_13507_13510| a@@3 b@@3 t@@2)) b@@3)
 :qid |DafnyPreludebpl.1393:21|
 :skolemid |320|
 :pattern ( (|IMap#Elements_12649_12650| (|IMap#Glue_13507_13510| a@@3 b@@3 t@@2)))
)))
(assert (forall ((v@@1 Int) ) (! ($Is_869 v@@1 (TBitvector 0))
 :qid |DafnyPreludebpl.234:15|
 :skolemid |44|
 :pattern ( ($Is_869 v@@1 (TBitvector 0)))
)))
(assert (forall ((a@@4 Int) (b@@4 Int) ) (!  (or (= (|Math#min| a@@4 b@@4) a@@4) (= (|Math#min| a@@4 b@@4) b@@4))
 :qid |DafnyPreludebpl.822:15|
 :skolemid |179|
 :pattern ( (|Math#min| a@@4 b@@4))
)))
(assert (forall ((o@@2 T@Box) (m@@0 Int) (n Int) ) (!  (=> (and (and (<= 0 m@@0) (<= 0 n)) (<= (+ m@@0 n) (|ORD#Offset| o@@2))) (= (|ORD#Minus| (|ORD#Minus| o@@2 (|ORD#FromNat| m@@0)) (|ORD#FromNat| n)) (|ORD#Minus| o@@2 (|ORD#FromNat| (+ m@@0 n)))))
 :qid |DafnyPreludebpl.464:15|
 :skolemid |97|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@2 (|ORD#FromNat| m@@0)) (|ORD#FromNat| n)))
)))
(assert (forall ((x@@3 T@Box) ) (!  (not (|Seq#Contains_20794| |Seq#Empty_12631| x@@3))
 :qid |DafnyPreludebpl.1033:18|
 :skolemid |238|
 :pattern ( (|Seq#Contains_20794| |Seq#Empty_12631| x@@3))
)))
(assert (= (|Seq#Length_12635| |Seq#Empty_12631|) 0))
(assert (forall ((s@@0 T@Seq_20794) (v@@2 T@Box) (n@@0 Int) ) (!  (=> (and (<= 0 n@@0) (<= n@@0 (|Seq#Length_12635| s@@0))) (= (|Seq#Drop_20794| (|Seq#Build_13286| s@@0 v@@2) n@@0) (|Seq#Build_13286| (|Seq#Drop_20794| s@@0 n@@0) v@@2)))
 :qid |DafnyPreludebpl.1147:18|
 :skolemid |266|
 :pattern ( (|Seq#Drop_20794| (|Seq#Build_13286| s@@0 v@@2) n@@0))
)))
(assert (forall ((v@@3 (Array T@Box Int)) (t0 T@Ty) ) (!  (=> ($Is_12584 v@@3 (TMultiSet t0)) ($IsGoodMultiSet_12631 v@@3))
 :qid |DafnyPreludebpl.248:15|
 :skolemid |51|
 :pattern ( ($Is_12584 v@@3 (TMultiSet t0)))
)))
(assert (forall ((s@@1 T@Seq_20794) ) (! ($IsGoodMultiSet_12631 (|MultiSet#FromSeq_12631| s@@1))
 :qid |DafnyPreludebpl.929:18|
 :skolemid |214|
 :pattern ( (|MultiSet#FromSeq_12631| s@@1))
)))
(assert (forall ((s@@2 T@Seq_20794) (i Int) (v@@4 T@Box) (n@@1 Int) ) (!  (=> (and (<= 0 n@@1) (< n@@1 (|Seq#Length_12635| s@@2))) (and (=> (= i n@@1) (= (|Seq#Index_12635| (|Seq#Update_13347| s@@2 i v@@4) n@@1) v@@4)) (=> (not (= i n@@1)) (= (|Seq#Index_12635| (|Seq#Update_13347| s@@2 i v@@4) n@@1) (|Seq#Index_12635| s@@2 n@@1)))))
 :qid |DafnyPreludebpl.1024:18|
 :skolemid |235|
 :pattern ( (|Seq#Index_12635| (|Seq#Update_13347| s@@2 i v@@4) n@@1))
)))
(assert (forall ((a@@5 (Array T@Box Bool)) (b@@5 (Array T@Box Bool)) ) (! (= (|Set#Union_17766| (|Set#Union_17766| a@@5 b@@5) b@@5) (|Set#Union_17766| a@@5 b@@5))
 :qid |DafnyPreludebpl.707:18|
 :skolemid |140|
 :pattern ( (|Set#Union_17766| (|Set#Union_17766| a@@5 b@@5) b@@5))
)))
(assert (forall ((a@@6 (Array T@Box Bool)) (b@@6 (Array T@Box Bool)) ) (! (= (|Set#Intersection_17766| (|Set#Intersection_17766| a@@6 b@@6) b@@6) (|Set#Intersection_17766| a@@6 b@@6))
 :qid |DafnyPreludebpl.711:18|
 :skolemid |142|
 :pattern ( (|Set#Intersection_17766| (|Set#Intersection_17766| a@@6 b@@6) b@@6))
)))
(assert (forall ((a@@7 (Array T@Box Int)) (b@@7 (Array T@Box Int)) ) (! (= (|MultiSet#Intersection_12631| (|MultiSet#Intersection_12631| a@@7 b@@7) b@@7) (|MultiSet#Intersection_12631| a@@7 b@@7))
 :qid |DafnyPreludebpl.881:18|
 :skolemid |199|
 :pattern ( (|MultiSet#Intersection_12631| (|MultiSet#Intersection_12631| a@@7 b@@7) b@@7))
)))
(assert (forall ((x@@4 Int) (y@@1 Int) ) (! (= (INTERNAL_lt_boogie x@@4 y@@1) (< x@@4 y@@1))
 :qid |DafnyPreludebpl.1456:51|
 :skolemid |337|
 :pattern ( (INTERNAL_lt_boogie x@@4 y@@1))
)))
(assert (forall ((x@@5 Int) (y@@2 Int) ) (! (= (INTERNAL_gt_boogie x@@5 y@@2) (> x@@5 y@@2))
 :qid |DafnyPreludebpl.1458:51|
 :skolemid |339|
 :pattern ( (INTERNAL_gt_boogie x@@5 y@@2))
)))
(assert (forall ((s@@3 T@Seq_20794) (t@@3 T@Seq_20794) (n@@2 Int) ) (!  (=> (= n@@2 (|Seq#Length_12635| s@@3)) (and (= (|Seq#Take_13347| (|Seq#Append_12631| s@@3 t@@3) n@@2) s@@3) (= (|Seq#Drop_20794| (|Seq#Append_12631| s@@3 t@@3) n@@2) t@@3)))
 :qid |DafnyPreludebpl.1096:18|
 :skolemid |255|
 :pattern ( (|Seq#Take_13347| (|Seq#Append_12631| s@@3 t@@3) n@@2))
 :pattern ( (|Seq#Drop_20794| (|Seq#Append_12631| s@@3 t@@3) n@@2))
)))
(assert (forall ((m@@1 T@Map_20925_20926) (u T@Box) (v@@5 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| m@@1) u) (= (|Map#Card_20925_20926| (|Map#Build_12638_12639| m@@1 u v@@5)) (|Map#Card_20925_20926| m@@1)))
 :qid |DafnyPreludebpl.1281:21|
 :skolemid |294|
 :pattern ( (|Map#Card_20925_20926| (|Map#Build_12638_12639| m@@1 u v@@5)))
)))
(assert (forall ((r@@0 T@Box) (o@@3 T@Box) ) (! (= (select (|Set#Singleton_17766| r@@0) o@@3) (= r@@0 o@@3))
 :qid |DafnyPreludebpl.672:18|
 :skolemid |128|
 :pattern ( (select (|Set#Singleton_17766| r@@0) o@@3))
)))
(assert (forall ((s@@4 T@Seq_20794) (x@@6 T@Box) ) (! (= (exists ((i@@0 Int) ) (!  (and (and (<= 0 i@@0) (< i@@0 (|Seq#Length_12635| s@@4))) (= x@@6 (|Seq#Index_12635| s@@4 i@@0)))
 :qid |DafnyPreludebpl.953:11|
 :skolemid |219|
 :pattern ( (|Seq#Index_12635| s@@4 i@@0))
)) (< 0 (select (|MultiSet#FromSeq_12631| s@@4) x@@6)))
 :qid |DafnyPreludebpl.952:18|
 :skolemid |220|
 :pattern ( (select (|MultiSet#FromSeq_12631| s@@4) x@@6))
)))
(assert (forall ((h@@1 (Array T@ref T@PolymorphicMapType_21225)) (a@@8 T@ref) (n0 Int) (n1 Int) ) (!  (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@8))) (= (|Seq#Take_13347| (|Seq#FromArray| h@@1 a@@8) n1) (|Seq#Build_13286| (|Seq#Take_13347| (|Seq#FromArray| h@@1 a@@8) n0) ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@1 a@@8)) (IndexField n0))))))
 :qid |DafnyPreludebpl.1143:15|
 :skolemid |265|
 :pattern ( (|Seq#Take_13347| (|Seq#FromArray| h@@1 a@@8) n0) (|Seq#Take_13347| (|Seq#FromArray| h@@1 a@@8) n1))
)))
(assert (forall ((a@@9 (Array T@Box Bool)) (b@@8 (Array T@Box Bool)) ) (! (= (+ (|Set#Card_17766| (|Set#Union_17766| a@@9 b@@8)) (|Set#Card_17766| (|Set#Intersection_17766| a@@9 b@@8))) (+ (|Set#Card_17766| a@@9) (|Set#Card_17766| b@@8)))
 :qid |DafnyPreludebpl.715:18|
 :skolemid |144|
 :pattern ( (|Set#Card_17766| (|Set#Union_17766| a@@9 b@@8)))
 :pattern ( (|Set#Card_17766| (|Set#Intersection_17766| a@@9 b@@8)))
)))
(assert (forall ((m@@2 T@Map_20925_20926) (s@@5 (Array T@Box Bool)) (u@@0 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| (|Map#Subtract_12638_12639| m@@2 s@@5)) u@@0) (= (select (|Map#Elements_12638_12639| (|Map#Subtract_12638_12639| m@@2 s@@5)) u@@0) (select (|Map#Elements_12638_12639| m@@2) u@@0)))
 :qid |DafnyPreludebpl.1301:21|
 :skolemid |299|
 :pattern ( (select (|Map#Elements_12638_12639| (|Map#Subtract_12638_12639| m@@2 s@@5)) u@@0))
)))
(assert (forall ((m@@3 T@IMap_21069_21070) (s@@6 (Array T@Box Bool)) (u@@1 T@Box) ) (!  (=> (select (|IMap#Domain_12649_12650| (|IMap#Subtract_12649_12650| m@@3 s@@6)) u@@1) (= (select (|IMap#Elements_12649_12650| (|IMap#Subtract_12649_12650| m@@3 s@@6)) u@@1) (select (|IMap#Elements_12649_12650| m@@3) u@@1)))
 :qid |DafnyPreludebpl.1442:21|
 :skolemid |331|
 :pattern ( (select (|IMap#Elements_12649_12650| (|IMap#Subtract_12649_12650| m@@3 s@@6)) u@@1))
)))
(assert (forall ((x@@7 Int) (y@@3 Int) ) (! (= (INTERNAL_mod_boogie x@@7 y@@3) (mod x@@7 y@@3))
 :qid |DafnyPreludebpl.1455:30|
 :skolemid |336|
 :pattern ( (INTERNAL_mod_boogie x@@7 y@@3))
)))
(assert (forall ((x@@8 Int) (y@@4 Int) ) (! (= (Mod x@@8 y@@4) (mod x@@8 y@@4))
 :qid |DafnyPreludebpl.1463:14|
 :skolemid |343|
 :pattern ( (Mod x@@8 y@@4))
)))
(assert (forall ((s@@7 T@Seq_20794) (i@@1 Int) (v@@6 T@Box) (n@@3 Int) ) (!  (=> (and (and (<= 0 n@@3) (<= n@@3 i@@1)) (< i@@1 (|Seq#Length_12635| s@@7))) (= (|Seq#Drop_20794| (|Seq#Update_13347| s@@7 i@@1 v@@6) n@@3) (|Seq#Update_13347| (|Seq#Drop_20794| s@@7 n@@3) (- i@@1 n@@3) v@@6)))
 :qid |DafnyPreludebpl.1136:18|
 :skolemid |263|
 :pattern ( (|Seq#Drop_20794| (|Seq#Update_13347| s@@7 i@@1 v@@6) n@@3))
)))
(assert (forall ((a@@10 (Array T@Box Int)) (b@@9 (Array T@Box Int)) (o@@4 T@Box) ) (! (= (select (|MultiSet#Union_12631| a@@10 b@@9) o@@4) (+ (select a@@10 o@@4) (select b@@9 o@@4)))
 :qid |DafnyPreludebpl.871:18|
 :skolemid |196|
 :pattern ( (select (|MultiSet#Union_12631| a@@10 b@@9) o@@4))
)))
(assert (forall ((x@@9 Int) (y@@5 Int) ) (! (= (INTERNAL_le_boogie x@@9 y@@5) (<= x@@9 y@@5))
 :qid |DafnyPreludebpl.1457:51|
 :skolemid |338|
 :pattern ( (INTERNAL_le_boogie x@@9 y@@5))
)))
(assert (forall ((x@@10 Int) (y@@6 Int) ) (! (= (INTERNAL_ge_boogie x@@10 y@@6) (>= x@@10 y@@6))
 :qid |DafnyPreludebpl.1459:51|
 :skolemid |340|
 :pattern ( (INTERNAL_ge_boogie x@@10 y@@6))
)))
(assert (forall ((s@@8 T@Seq_20794) (n@@4 Int) ) (!  (=> (= n@@4 0) (= (|Seq#Drop_20794| s@@8 n@@4) s@@8))
 :qid |DafnyPreludebpl.1166:18|
 :skolemid |271|
 :pattern ( (|Seq#Drop_20794| s@@8 n@@4))
)))
(assert (forall ((x@@11 Int) (y@@7 Int) ) (! (= (INTERNAL_sub_boogie x@@11 y@@7) (- x@@11 y@@7))
 :qid |DafnyPreludebpl.1452:30|
 :skolemid |333|
 :pattern ( (INTERNAL_sub_boogie x@@11 y@@7))
)))
(assert (forall ((x@@12 Int) (y@@8 Int) ) (! (= (Sub x@@12 y@@8) (- x@@12 y@@8))
 :qid |DafnyPreludebpl.1465:14|
 :skolemid |345|
 :pattern ( (Sub x@@12 y@@8))
)))
(assert (forall ((x@@13 Int) (y@@9 Int) ) (! (= (INTERNAL_add_boogie x@@13 y@@9) (+ x@@13 y@@9))
 :qid |DafnyPreludebpl.1451:30|
 :skolemid |332|
 :pattern ( (INTERNAL_add_boogie x@@13 y@@9))
)))
(assert (forall ((x@@14 Int) (y@@10 Int) ) (! (= (Add x@@14 y@@10) (+ x@@14 y@@10))
 :qid |DafnyPreludebpl.1464:14|
 :skolemid |344|
 :pattern ( (Add x@@14 y@@10))
)))
(assert (forall ((x@@15 Int) (y@@11 Int) ) (! (= (INTERNAL_mul_boogie x@@15 y@@11) (* x@@15 y@@11))
 :qid |DafnyPreludebpl.1453:30|
 :skolemid |334|
 :pattern ( (INTERNAL_mul_boogie x@@15 y@@11))
)))
(assert (forall ((x@@16 Int) (y@@12 Int) ) (! (= (Mul x@@16 y@@12) (* x@@16 y@@12))
 :qid |DafnyPreludebpl.1461:14|
 :skolemid |341|
 :pattern ( (Mul x@@16 y@@12))
)))
(assert (forall ((v@@7 (Array T@Box Bool)) (t0@@0 T@Ty) ) (! (= ($Is_12560 v@@7 (TSet t0@@0)) (forall ((bx T@Box) ) (!  (=> (select v@@7 bx) ($IsBox_12550 bx t0@@0))
 :qid |DafnyPreludebpl.238:11|
 :skolemid |45|
 :pattern ( (select v@@7 bx))
)))
 :qid |DafnyPreludebpl.236:15|
 :skolemid |46|
 :pattern ( ($Is_12560 v@@7 (TSet t0@@0)))
)))
(assert (forall ((v@@8 (Array T@Box Bool)) (t0@@1 T@Ty) ) (! (= ($Is_12560 v@@8 (TISet t0@@1)) (forall ((bx@@0 T@Box) ) (!  (=> (select v@@8 bx@@0) ($IsBox_12550 bx@@0 t0@@1))
 :qid |DafnyPreludebpl.242:11|
 :skolemid |47|
 :pattern ( (select v@@8 bx@@0))
)))
 :qid |DafnyPreludebpl.240:15|
 :skolemid |48|
 :pattern ( ($Is_12560 v@@8 (TISet t0@@1)))
)))
(assert (forall ((a@@11 Int) ) (!  (=> (<= 0 a@@11) (= (|Math#clip| a@@11) a@@11))
 :qid |DafnyPreludebpl.825:15|
 :skolemid |180|
 :pattern ( (|Math#clip| a@@11))
)))
(assert (forall ((s@@9 T@Seq_20794) (bx@@1 T@Box) (t@@4 T@Ty) ) (!  (=> (and ($Is_20853 s@@9 (TSeq t@@4)) ($IsBox_12550 bx@@1 t@@4)) ($Is_20853 (|Seq#Build_13286| s@@9 bx@@1) (TSeq t@@4)))
 :qid |DafnyPreludebpl.998:15|
 :skolemid |228|
 :pattern ( ($Is_20853 (|Seq#Build_13286| s@@9 bx@@1) (TSeq t@@4)))
)))
(assert (forall ((ty T@Ty) (heap (Array T@ref T@PolymorphicMapType_21225)) (len Int) (init T@HandleType) ) (!  (=> (and ($IsGoodHeap heap) (<= 0 len)) (= (|Seq#Length_12635| (|Seq#Create| ty heap len init)) len))
 :qid |DafnyPreludebpl.1002:15|
 :skolemid |229|
 :pattern ( (|Seq#Length_12635| (|Seq#Create| ty heap len init)))
)))
(assert $$Language$Dafny)
(assert (forall ((s@@10 T@Seq_20794) (n@@5 Int) (j Int) ) (!  (=> (and (and (<= 0 j) (< j n@@5)) (< j (|Seq#Length_12635| s@@10))) (= (|Seq#Index_12635| (|Seq#Take_13347| s@@10 n@@5) j) (|Seq#Index_12635| s@@10 j)))
 :qid |DafnyPreludebpl.1075:18|
 :weight 25
 :skolemid |251|
 :pattern ( (|Seq#Index_12635| (|Seq#Take_13347| s@@10 n@@5) j))
 :pattern ( (|Seq#Index_12635| s@@10 j) (|Seq#Take_13347| s@@10 n@@5))
)))
(assert (forall ((s@@11 T@Seq_20794) (n@@6 Int) ) (!  (=> (and (<= 0 n@@6) (<= n@@6 (|Seq#Length_12635| s@@11))) (= (|Seq#Length_12635| (|Seq#Drop_20794| s@@11 n@@6)) (- (|Seq#Length_12635| s@@11) n@@6)))
 :qid |DafnyPreludebpl.1083:18|
 :skolemid |252|
 :pattern ( (|Seq#Length_12635| (|Seq#Drop_20794| s@@11 n@@6)))
)))
(assert (forall ((m@@4 T@Map_20925_20926) (u@@2 T@Box) (v@@9 T@Box) ) (!  (=> (not (select (|Map#Domain_12638_12639| m@@4) u@@2)) (= (|Map#Card_20925_20926| (|Map#Build_12638_12639| m@@4 u@@2 v@@9)) (+ (|Map#Card_20925_20926| m@@4) 1)))
 :qid |DafnyPreludebpl.1283:21|
 :skolemid |295|
 :pattern ( (|Map#Card_20925_20926| (|Map#Build_12638_12639| m@@4 u@@2 v@@9)))
)))
(assert (forall ((s0 T@Seq_20794) (s1 T@Seq_20794) ) (! (= (|Seq#Equal_20794| s0 s1)  (and (= (|Seq#Length_12635| s0) (|Seq#Length_12635| s1)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length_12635| s0))) (= (|Seq#Index_12635| s0 j@@0) (|Seq#Index_12635| s1 j@@0)))
 :qid |DafnyPreludebpl.1061:13|
 :skolemid |245|
 :pattern ( (|Seq#Index_12635| s0 j@@0))
 :pattern ( (|Seq#Index_12635| s1 j@@0))
))))
 :qid |DafnyPreludebpl.1058:18|
 :skolemid |246|
 :pattern ( (|Seq#Equal_20794| s0 s1))
)))
(assert (forall ((a@@12 (Array T@Box Int)) (b@@10 (Array T@Box Int)) (o@@5 T@Box) ) (! (= (select (|MultiSet#Difference_12631| a@@12 b@@10) o@@5) (|Math#clip| (- (select a@@12 o@@5) (select b@@10 o@@5))))
 :qid |DafnyPreludebpl.888:18|
 :skolemid |201|
 :pattern ( (select (|MultiSet#Difference_12631| a@@12 b@@10) o@@5))
)))
(assert (forall ((s@@12 (Array T@ref Bool)) (bx@@2 T@Box) ) (! (= (select (SetRef_to_SetBox s@@12) bx@@2) (select s@@12 ($Unbox_12740 bx@@2)))
 :qid |DafnyPreludebpl.368:15|
 :skolemid |81|
 :pattern ( (select (SetRef_to_SetBox s@@12) bx@@2))
)))
(assert (forall ((s@@13 T@Seq_20794) (i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length_12635| s@@13))) (< (|Seq#Rank_13371| (|Seq#Take_13347| s@@13 i@@2)) (|Seq#Rank_13371| s@@13)))
 :qid |DafnyPreludebpl.1158:18|
 :skolemid |269|
 :pattern ( (|Seq#Rank_13371| (|Seq#Take_13347| s@@13 i@@2)))
)))
(assert (forall ((f T@Field_26410) (i@@3 Int) ) (! (= (FDim_12809 (MultiIndexField f i@@3)) (+ (FDim_12809 f) 1))
 :qid |DafnyPreludebpl.518:15|
 :skolemid |104|
 :pattern ( (MultiIndexField f i@@3))
)))
(assert (forall ((a@@13 (Array T@Box Int)) (x@@17 T@Box) ) (! (= (|MultiSet#Card_12631| (|MultiSet#UnionOne_12631| a@@13 x@@17)) (+ (|MultiSet#Card_12631| a@@13) 1))
 :qid |DafnyPreludebpl.865:18|
 :skolemid |195|
 :pattern ( (|MultiSet#Card_12631| (|MultiSet#UnionOne_12631| a@@13 x@@17)))
)))
(assert (forall ((s@@14 T@Seq_20794) (i@@4 Int) ) (!  (=> (and (< 0 i@@4) (<= i@@4 (|Seq#Length_12635| s@@14))) (< (|Seq#Rank_13371| (|Seq#Drop_20794| s@@14 i@@4)) (|Seq#Rank_13371| s@@14)))
 :qid |DafnyPreludebpl.1155:18|
 :skolemid |268|
 :pattern ( (|Seq#Rank_13371| (|Seq#Drop_20794| s@@14 i@@4)))
)))
(assert ($IsGhostField_3928 alloc))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((s@@15 T@Seq_20794) (v@@10 T@Box) ) (! (= (|Seq#Length_12635| (|Seq#Build_13286| s@@15 v@@10)) (+ 1 (|Seq#Length_12635| s@@15)))
 :qid |DafnyPreludebpl.990:18|
 :skolemid |226|
 :pattern ( (|Seq#Build_13286| s@@15 v@@10))
)))
(assert (forall ((s@@16 T@Seq_20794) (i@@5 Int) ) (!  (=> (and (<= 0 i@@5) (< i@@5 (|Seq#Length_12635| s@@16))) (< (DtRank ($Unbox_13374 (|Seq#Index_12635| s@@16 i@@5))) (|Seq#Rank_13371| s@@16)))
 :qid |DafnyPreludebpl.1152:15|
 :skolemid |267|
 :pattern ( (DtRank ($Unbox_13374 (|Seq#Index_12635| s@@16 i@@5))))
)))
(assert (forall ((ty@@0 T@Ty) (heap@@0 (Array T@ref T@PolymorphicMapType_21225)) (len@@0 Int) (init@@0 T@HandleType) (i@@6 Int) ) (!  (=> (and (and ($IsGoodHeap heap@@0) (<= 0 i@@6)) (< i@@6 len@@0)) (= (|Seq#Index_12635| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@6) (Apply1 TInt ty@@0 heap@@0 init@@0 ($Box_552 i@@6))))
 :qid |DafnyPreludebpl.1006:15|
 :skolemid |230|
 :pattern ( (|Seq#Index_12635| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@6))
)))
(assert (forall ((v@@11 T@Box) (t@@5 T@Ty) (h@@2 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12809 v@@11) t@@5 h@@2) ($IsAlloc_12448 v@@11 t@@5 h@@2))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12809 v@@11) t@@5 h@@2))
)))
(assert (forall ((v@@12 T@ref) (t@@6 T@Ty) (h@@3 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12882 v@@12) t@@6 h@@3) ($IsAlloc_12882 v@@12 t@@6 h@@3))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12882 v@@12) t@@6 h@@3))
)))
(assert (forall ((v@@13 T@DatatypeType) (t@@7 T@Ty) (h@@4 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12753 v@@13) t@@7 h@@4) ($IsAlloc_12753 v@@13 t@@7 h@@4))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12753 v@@13) t@@7 h@@4))
)))
(assert (forall ((v@@14 T@IMap_21069_21070) (t@@8 T@Ty) (h@@5 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_21090 v@@14) t@@8 h@@5) ($IsAlloc_24132 v@@14 t@@8 h@@5))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_21090 v@@14) t@@8 h@@5))
)))
(assert (forall ((v@@15 T@Map_20925_20926) (t@@9 T@Ty) (h@@6 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_20946 v@@15) t@@9 h@@6) ($IsAlloc_23870 v@@15 t@@9 h@@6))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_20946 v@@15) t@@9 h@@6))
)))
(assert (forall ((v@@16 T@Seq_20794) (t@@10 T@Ty) (h@@7 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_20812 v@@16) t@@10 h@@7) ($IsAlloc_23682 v@@16 t@@10 h@@7))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_20812 v@@16) t@@10 h@@7))
)))
(assert (forall ((v@@17 (Array T@Box Int)) (t@@11 T@Ty) (h@@8 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12581 v@@17) t@@11 h@@8) ($IsAlloc_12685 v@@17 t@@11 h@@8))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12581 v@@17) t@@11 h@@8))
)))
(assert (forall ((v@@18 (Array T@Box Bool)) (t@@12 T@Ty) (h@@9 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12565 v@@18) t@@12 h@@9) ($IsAlloc_12673 v@@18 t@@12 h@@9))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12565 v@@18) t@@12 h@@9))
)))
(assert (forall ((v@@19 T@char) (t@@13 T@Ty) (h@@10 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_12554 v@@19) t@@13 h@@10) ($IsAlloc_12666 v@@19 t@@13 h@@10))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_12554 v@@19) t@@13 h@@10))
)))
(assert (forall ((v@@20 Bool) (t@@14 T@Ty) (h@@11 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_926 v@@20) t@@14 h@@11) ($IsAlloc_1948 v@@20 t@@14 h@@11))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_926 v@@20) t@@14 h@@11))
)))
(assert (forall ((v@@21 Real) (t@@15 T@Ty) (h@@12 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_594 v@@21) t@@15 h@@12) ($IsAlloc_1929 v@@21 t@@15 h@@12))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_594 v@@21) t@@15 h@@12))
)))
(assert (forall ((v@@22 Int) (t@@16 T@Ty) (h@@13 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAllocBox_13729 ($Box_552 v@@22) t@@16 h@@13) ($IsAlloc_1910 v@@22 t@@16 h@@13))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox_13729 ($Box_552 v@@22) t@@16 h@@13))
)))
(assert (forall ((h@@14 (Array T@ref T@PolymorphicMapType_21225)) (k@@0 (Array T@ref T@PolymorphicMapType_21225)) (v@@23 T@ref) (t@@17 T@Ty) ) (!  (=> ($HeapSucc h@@14 k@@0) (=> ($IsAlloc_12882 v@@23 t@@17 h@@14) ($IsAlloc_12882 v@@23 t@@17 k@@0)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@14 k@@0) ($IsAlloc_12882 v@@23 t@@17 h@@14))
)))
(assert (forall ((h@@15 (Array T@ref T@PolymorphicMapType_21225)) (k@@1 (Array T@ref T@PolymorphicMapType_21225)) (v@@24 T@DatatypeType) (t@@18 T@Ty) ) (!  (=> ($HeapSucc h@@15 k@@1) (=> ($IsAlloc_12753 v@@24 t@@18 h@@15) ($IsAlloc_12753 v@@24 t@@18 k@@1)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@15 k@@1) ($IsAlloc_12753 v@@24 t@@18 h@@15))
)))
(assert (forall ((h@@16 (Array T@ref T@PolymorphicMapType_21225)) (k@@2 (Array T@ref T@PolymorphicMapType_21225)) (v@@25 T@IMap_21069_21070) (t@@19 T@Ty) ) (!  (=> ($HeapSucc h@@16 k@@2) (=> ($IsAlloc_24132 v@@25 t@@19 h@@16) ($IsAlloc_24132 v@@25 t@@19 k@@2)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@16 k@@2) ($IsAlloc_24132 v@@25 t@@19 h@@16))
)))
(assert (forall ((h@@17 (Array T@ref T@PolymorphicMapType_21225)) (k@@3 (Array T@ref T@PolymorphicMapType_21225)) (v@@26 T@Map_20925_20926) (t@@20 T@Ty) ) (!  (=> ($HeapSucc h@@17 k@@3) (=> ($IsAlloc_23870 v@@26 t@@20 h@@17) ($IsAlloc_23870 v@@26 t@@20 k@@3)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@17 k@@3) ($IsAlloc_23870 v@@26 t@@20 h@@17))
)))
(assert (forall ((h@@18 (Array T@ref T@PolymorphicMapType_21225)) (k@@4 (Array T@ref T@PolymorphicMapType_21225)) (v@@27 T@Seq_20794) (t@@21 T@Ty) ) (!  (=> ($HeapSucc h@@18 k@@4) (=> ($IsAlloc_23682 v@@27 t@@21 h@@18) ($IsAlloc_23682 v@@27 t@@21 k@@4)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@18 k@@4) ($IsAlloc_23682 v@@27 t@@21 h@@18))
)))
(assert (forall ((h@@19 (Array T@ref T@PolymorphicMapType_21225)) (k@@5 (Array T@ref T@PolymorphicMapType_21225)) (v@@28 (Array T@Box Int)) (t@@22 T@Ty) ) (!  (=> ($HeapSucc h@@19 k@@5) (=> ($IsAlloc_12685 v@@28 t@@22 h@@19) ($IsAlloc_12685 v@@28 t@@22 k@@5)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@19 k@@5) ($IsAlloc_12685 v@@28 t@@22 h@@19))
)))
(assert (forall ((h@@20 (Array T@ref T@PolymorphicMapType_21225)) (k@@6 (Array T@ref T@PolymorphicMapType_21225)) (v@@29 (Array T@Box Bool)) (t@@23 T@Ty) ) (!  (=> ($HeapSucc h@@20 k@@6) (=> ($IsAlloc_12673 v@@29 t@@23 h@@20) ($IsAlloc_12673 v@@29 t@@23 k@@6)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@20 k@@6) ($IsAlloc_12673 v@@29 t@@23 h@@20))
)))
(assert (forall ((h@@21 (Array T@ref T@PolymorphicMapType_21225)) (k@@7 (Array T@ref T@PolymorphicMapType_21225)) (v@@30 T@Box) (t@@24 T@Ty) ) (!  (=> ($HeapSucc h@@21 k@@7) (=> ($IsAlloc_12448 v@@30 t@@24 h@@21) ($IsAlloc_12448 v@@30 t@@24 k@@7)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@21 k@@7) ($IsAlloc_12448 v@@30 t@@24 h@@21))
)))
(assert (forall ((h@@22 (Array T@ref T@PolymorphicMapType_21225)) (k@@8 (Array T@ref T@PolymorphicMapType_21225)) (v@@31 T@char) (t@@25 T@Ty) ) (!  (=> ($HeapSucc h@@22 k@@8) (=> ($IsAlloc_12666 v@@31 t@@25 h@@22) ($IsAlloc_12666 v@@31 t@@25 k@@8)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@22 k@@8) ($IsAlloc_12666 v@@31 t@@25 h@@22))
)))
(assert (forall ((h@@23 (Array T@ref T@PolymorphicMapType_21225)) (k@@9 (Array T@ref T@PolymorphicMapType_21225)) (v@@32 Bool) (t@@26 T@Ty) ) (!  (=> ($HeapSucc h@@23 k@@9) (=> ($IsAlloc_1948 v@@32 t@@26 h@@23) ($IsAlloc_1948 v@@32 t@@26 k@@9)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@23 k@@9) ($IsAlloc_1948 v@@32 t@@26 h@@23))
)))
(assert (forall ((h@@24 (Array T@ref T@PolymorphicMapType_21225)) (k@@10 (Array T@ref T@PolymorphicMapType_21225)) (v@@33 Real) (t@@27 T@Ty) ) (!  (=> ($HeapSucc h@@24 k@@10) (=> ($IsAlloc_1929 v@@33 t@@27 h@@24) ($IsAlloc_1929 v@@33 t@@27 k@@10)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@24 k@@10) ($IsAlloc_1929 v@@33 t@@27 h@@24))
)))
(assert (forall ((h@@25 (Array T@ref T@PolymorphicMapType_21225)) (k@@11 (Array T@ref T@PolymorphicMapType_21225)) (v@@34 Int) (t@@28 T@Ty) ) (!  (=> ($HeapSucc h@@25 k@@11) (=> ($IsAlloc_1910 v@@34 t@@28 h@@25) ($IsAlloc_1910 v@@34 t@@28 k@@11)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@25 k@@11) ($IsAlloc_1910 v@@34 t@@28 h@@25))
)))
(assert (forall ((h@@26 (Array T@ref T@PolymorphicMapType_21225)) (k@@12 (Array T@ref T@PolymorphicMapType_21225)) (bx@@3 T@Box) (t@@29 T@Ty) ) (!  (=> ($HeapSucc h@@26 k@@12) (=> ($IsAllocBox_13729 bx@@3 t@@29 h@@26) ($IsAllocBox_13729 bx@@3 t@@29 k@@12)))
 :qid |DafnyPreludebpl.555:15|
 :skolemid |110|
 :pattern ( ($HeapSucc h@@26 k@@12) ($IsAllocBox_13729 bx@@3 t@@29 h@@26))
)))
(assert (forall ((s@@17 T@Seq_20794) (n@@7 Int) (j@@1 Int) ) (!  (=> (and (and (<= 0 n@@7) (<= 0 j@@1)) (< j@@1 (- (|Seq#Length_12635| s@@17) n@@7))) (= (|Seq#Index_12635| (|Seq#Drop_20794| s@@17 n@@7) j@@1) (|Seq#Index_12635| s@@17 (+ j@@1 n@@7))))
 :qid |DafnyPreludebpl.1085:18|
 :weight 25
 :skolemid |253|
 :pattern ( (|Seq#Index_12635| (|Seq#Drop_20794| s@@17 n@@7) j@@1))
)))
(assert (forall ((s@@18 (Array T@Box Int)) ) (!  (and (= (= (|MultiSet#Card_12631| s@@18) 0) (= s@@18 |MultiSet#Empty_12631|)) (=> (not (= (|MultiSet#Card_12631| s@@18) 0)) (exists ((x@@18 T@Box) ) (! (< 0 (select s@@18 x@@18))
 :qid |DafnyPreludebpl.845:38|
 :skolemid |187|
))))
 :qid |DafnyPreludebpl.843:18|
 :skolemid |188|
 :pattern ( (|MultiSet#Card_12631| s@@18))
)))
(assert (forall ((a@@14 (Array T@Box Int)) (b@@11 (Array T@Box Int)) (y@@13 T@Box) ) (!  (=> (<= (select a@@14 y@@13) (select b@@11 y@@13)) (= (select (|MultiSet#Difference_12631| a@@14 b@@11) y@@13) 0))
 :qid |DafnyPreludebpl.890:18|
 :skolemid |202|
 :pattern ( (|MultiSet#Difference_12631| a@@14 b@@11) (select b@@11 y@@13) (select a@@14 y@@13))
)))
(assert (forall ((o@@6 T@Box) (p@@0 T@Box) ) (!  (=> (and (|ORD#IsNat| p@@0) (<= (|ORD#Offset| p@@0) (|ORD#Offset| o@@6))) (and (= (|ORD#IsNat| (|ORD#Minus| o@@6 p@@0)) (|ORD#IsNat| o@@6)) (= (|ORD#Offset| (|ORD#Minus| o@@6 p@@0)) (- (|ORD#Offset| o@@6) (|ORD#Offset| p@@0)))))
 :qid |DafnyPreludebpl.449:15|
 :skolemid |94|
 :pattern ( (|ORD#Minus| o@@6 p@@0))
)))
(assert (forall ((a@@15 (Array T@Box Int)) (b@@12 (Array T@Box Int)) ) (! (= (|MultiSet#Card_12631| (|MultiSet#Union_12631| a@@15 b@@12)) (+ (|MultiSet#Card_12631| a@@15) (|MultiSet#Card_12631| b@@12)))
 :qid |DafnyPreludebpl.873:18|
 :skolemid |197|
 :pattern ( (|MultiSet#Card_12631| (|MultiSet#Union_12631| a@@15 b@@12)))
)))
(assert (forall ((s0@@0 T@Seq_20794) (s1@@0 T@Seq_20794) ) (! (= (|Seq#Length_12635| (|Seq#Append_12631| s0@@0 s1@@0)) (+ (|Seq#Length_12635| s0@@0) (|Seq#Length_12635| s1@@0)))
 :qid |DafnyPreludebpl.1012:18|
 :skolemid |231|
 :pattern ( (|Seq#Length_12635| (|Seq#Append_12631| s0@@0 s1@@0)))
)))
(assert (forall ((n@@8 Int) ) (!  (=> (<= 0 n@@8) (and (|ORD#IsNat| (|ORD#FromNat| n@@8)) (= (|ORD#Offset| (|ORD#FromNat| n@@8)) n@@8)))
 :qid |DafnyPreludebpl.410:15|
 :skolemid |85|
 :pattern ( (|ORD#FromNat| n@@8))
)))
(assert (forall ((ms (Array T@Box Int)) ) (! (= ($IsGoodMultiSet_12631 ms) (forall ((bx@@4 T@Box) ) (!  (and (<= 0 (select ms bx@@4)) (<= (select ms bx@@4) (|MultiSet#Card_12631| ms)))
 :qid |DafnyPreludebpl.834:11|
 :skolemid |182|
 :pattern ( (select ms bx@@4))
)))
 :qid |DafnyPreludebpl.832:18|
 :skolemid |183|
 :pattern ( ($IsGoodMultiSet_12631 ms))
)))
(assert (forall ((o@@7 T@Box) (p@@1 T@Box) ) (!  (and (or (= o@@7 (|ORD#Plus| o@@7 p@@1)) (|ORD#Less| o@@7 (|ORD#Plus| o@@7 p@@1))) (or (= p@@1 (|ORD#Plus| o@@7 p@@1)) (|ORD#Less| p@@1 (|ORD#Plus| o@@7 p@@1))))
 :qid |DafnyPreludebpl.441:15|
 :skolemid |92|
 :pattern ( (|ORD#Plus| o@@7 p@@1))
)))
(assert (forall ((a@@16 (Array T@Box Int)) (x@@19 T@Box) ) (! (= (select (|MultiSet#UnionOne_12631| a@@16 x@@19) x@@19) (+ (select a@@16 x@@19) 1))
 :qid |DafnyPreludebpl.857:18|
 :skolemid |192|
 :pattern ( (|MultiSet#UnionOne_12631| a@@16 x@@19))
)))
(assert (forall ((s@@19 T@Seq_20794) (i@@7 Int) (v@@35 T@Box) ) (!  (and (=> (= i@@7 (|Seq#Length_12635| s@@19)) (= (|Seq#Index_12635| (|Seq#Build_13286| s@@19 v@@35) i@@7) v@@35)) (=> (not (= i@@7 (|Seq#Length_12635| s@@19))) (= (|Seq#Index_12635| (|Seq#Build_13286| s@@19 v@@35) i@@7) (|Seq#Index_12635| s@@19 i@@7))))
 :qid |DafnyPreludebpl.993:18|
 :skolemid |227|
 :pattern ( (|Seq#Index_12635| (|Seq#Build_13286| s@@19 v@@35) i@@7))
)))
(assert (forall ((a@@17 T@char) (b@@13 T@char) ) (! (= (|char#Minus| a@@17 b@@13) (|char#FromInt| (- (|char#ToInt| a@@17) (|char#ToInt| b@@13))))
 :qid |DafnyPreludebpl.147:15|
 :skolemid |24|
 :pattern ( (|char#Minus| a@@17 b@@13))
)))
(assert (forall ((a@@18 T@char) (b@@14 T@char) ) (! (= (|char#Plus| a@@18 b@@14) (|char#FromInt| (+ (|char#ToInt| a@@18) (|char#ToInt| b@@14))))
 :qid |DafnyPreludebpl.142:15|
 :skolemid |23|
 :pattern ( (|char#Plus| a@@18 b@@14))
)))
(assert (forall ((a@@19 (Array T@Box Int)) (x@@20 T@Box) (y@@14 T@Box) ) (!  (=> (< 0 (select a@@19 y@@14)) (< 0 (select (|MultiSet#UnionOne_12631| a@@19 x@@20) y@@14)))
 :qid |DafnyPreludebpl.860:18|
 :skolemid |193|
 :pattern ( (|MultiSet#UnionOne_12631| a@@19 x@@20) (select a@@19 y@@14))
)))
(assert (forall ((m@@5 T@Map_20925_20926) ) (!  (or (= m@@5 |Map#Empty_20925_20926|) (exists ((k@@13 T@Box) ) (! (select (|Map#Domain_12638_12639| m@@5) k@@13)
 :qid |DafnyPreludebpl.1196:31|
 :skolemid |276|
)))
 :qid |DafnyPreludebpl.1194:21|
 :skolemid |277|
 :pattern ( (|Map#Domain_12638_12639| m@@5))
)))
(assert (forall ((m@@6 T@Map_20925_20926) ) (!  (or (= m@@6 |Map#Empty_20925_20926|) (exists ((v@@36 T@Box) ) (! (select (|Map#Values_12644_12645| m@@6) v@@36)
 :qid |DafnyPreludebpl.1199:31|
 :skolemid |278|
)))
 :qid |DafnyPreludebpl.1197:21|
 :skolemid |279|
 :pattern ( (|Map#Values_12644_12645| m@@6))
)))
(assert (forall ((m@@7 T@IMap_21069_21070) ) (!  (or (= m@@7 |IMap#Empty_21069_21070|) (exists ((k@@14 T@Box) ) (! (select (|IMap#Domain_12649_12650| m@@7) k@@14)
 :qid |DafnyPreludebpl.1336:32|
 :skolemid |306|
)))
 :qid |DafnyPreludebpl.1334:21|
 :skolemid |307|
 :pattern ( (|IMap#Domain_12649_12650| m@@7))
)))
(assert (forall ((m@@8 T@IMap_21069_21070) ) (!  (or (= m@@8 |IMap#Empty_21069_21070|) (exists ((v@@37 T@Box) ) (! (select (|IMap#Values_12655_12656| m@@8) v@@37)
 :qid |DafnyPreludebpl.1339:32|
 :skolemid |308|
)))
 :qid |DafnyPreludebpl.1337:21|
 :skolemid |309|
 :pattern ( (|IMap#Values_12655_12656| m@@8))
)))
(assert (forall ((a@@20 (Array T@Box Int)) (x@@21 T@Box) (o@@8 T@Box) ) (! (= (< 0 (select (|MultiSet#UnionOne_12631| a@@20 x@@21) o@@8))  (or (= o@@8 x@@21) (< 0 (select a@@20 o@@8))))
 :qid |DafnyPreludebpl.854:18|
 :skolemid |191|
 :pattern ( (select (|MultiSet#UnionOne_12631| a@@20 x@@21) o@@8))
)))
(assert (forall ((h@@27 (Array T@ref T@PolymorphicMapType_21225)) (a@@21 T@ref) ) (! (forall ((i@@8 Int) ) (!  (=> (and (<= 0 i@@8) (< i@@8 (|Seq#Length_12635| (|Seq#FromArray| h@@27 a@@21)))) (= (|Seq#Index_12635| (|Seq#FromArray| h@@27 a@@21) i@@8) ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@27 a@@21)) (IndexField i@@8)))))
 :qid |DafnyPreludebpl.1110:11|
 :skolemid |257|
 :pattern ( ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@27 a@@21)) (IndexField i@@8))))
 :pattern ( (|Seq#Index_12635| (|Seq#FromArray| h@@27 a@@21) i@@8))
))
 :qid |DafnyPreludebpl.1108:15|
 :skolemid |258|
 :pattern ( (|Seq#FromArray| h@@27 a@@21))
)))
(assert (forall ((v@@38 (Array T@Box Int)) (t0@@2 T@Ty) ) (! (= ($Is_12584 v@@38 (TMultiSet t0@@2)) (forall ((bx@@5 T@Box) ) (!  (=> (< 0 (select v@@38 bx@@5)) ($IsBox_12550 bx@@5 t0@@2))
 :qid |DafnyPreludebpl.246:11|
 :skolemid |49|
 :pattern ( (select v@@38 bx@@5))
)))
 :qid |DafnyPreludebpl.244:15|
 :skolemid |50|
 :pattern ( ($Is_12584 v@@38 (TMultiSet t0@@2)))
)))
(assert (forall ((s0@@1 T@Seq_20794) (s1@@1 T@Seq_20794) (x@@22 T@Box) ) (! (= (|Seq#Contains_20794| (|Seq#Append_12631| s0@@1 s1@@1) x@@22)  (or (|Seq#Contains_20794| s0@@1 x@@22) (|Seq#Contains_20794| s1@@1 x@@22)))
 :qid |DafnyPreludebpl.1037:18|
 :skolemid |239|
 :pattern ( (|Seq#Contains_20794| (|Seq#Append_12631| s0@@1 s1@@1) x@@22))
)))
(assert (forall ((s@@20 T@Seq_20794) (n@@9 Int) (x@@23 T@Box) ) (! (= (|Seq#Contains_20794| (|Seq#Take_13347| s@@20 n@@9) x@@23) (exists ((i@@9 Int) ) (!  (and (and (and (<= 0 i@@9) (< i@@9 n@@9)) (< i@@9 (|Seq#Length_12635| s@@20))) (= (|Seq#Index_12635| s@@20 i@@9) x@@23))
 :qid |DafnyPreludebpl.1049:13|
 :skolemid |241|
 :pattern ( (|Seq#Index_12635| s@@20 i@@9))
)))
 :qid |DafnyPreludebpl.1046:18|
 :skolemid |242|
 :pattern ( (|Seq#Contains_20794| (|Seq#Take_13347| s@@20 n@@9) x@@23))
)))
(assert (forall ((a@@22 (Array T@Box Bool)) (b@@15 (Array T@Box Bool)) ) (!  (=> (|Set#Disjoint_17766| a@@22 b@@15) (and (= (|Set#Difference_17766| (|Set#Union_17766| a@@22 b@@15) a@@22) b@@15) (= (|Set#Difference_17766| (|Set#Union_17766| a@@22 b@@15) b@@15) a@@22)))
 :qid |DafnyPreludebpl.694:18|
 :skolemid |138|
 :pattern ( (|Set#Union_17766| a@@22 b@@15))
)))
(assert (forall ((m@@9 T@Map_20925_20926) ) (! (= (= (|Map#Card_20925_20926| m@@9) 0) (= m@@9 |Map#Empty_20925_20926|))
 :qid |DafnyPreludebpl.1190:21|
 :skolemid |275|
 :pattern ( (|Map#Card_20925_20926| m@@9))
)))
(assert (forall ((s@@21 T@Seq_20794) (x@@24 T@Box) ) (! (= (|Seq#Contains_20794| s@@21 x@@24) (exists ((i@@10 Int) ) (!  (and (and (<= 0 i@@10) (< i@@10 (|Seq#Length_12635| s@@21))) (= (|Seq#Index_12635| s@@21 i@@10) x@@24))
 :qid |DafnyPreludebpl.1032:13|
 :skolemid |236|
 :pattern ( (|Seq#Index_12635| s@@21 i@@10))
)))
 :qid |DafnyPreludebpl.1030:18|
 :skolemid |237|
 :pattern ( (|Seq#Contains_20794| s@@21 x@@24))
)))
(assert (forall ((s@@22 T@Seq_20794) (i@@11 Int) (v@@39 T@Box) (n@@10 Int) ) (!  (=> (and (and (<= 0 i@@11) (< i@@11 n@@10)) (<= n@@10 (|Seq#Length_12635| s@@22))) (= (|Seq#Drop_20794| (|Seq#Update_13347| s@@22 i@@11 v@@39) n@@10) (|Seq#Drop_20794| s@@22 n@@10)))
 :qid |DafnyPreludebpl.1139:18|
 :skolemid |264|
 :pattern ( (|Seq#Drop_20794| (|Seq#Update_13347| s@@22 i@@11 v@@39) n@@10))
)))
(assert (forall ((a@@23 (Array T@Box Bool)) (b@@16 (Array T@Box Bool)) (o@@9 T@Box) ) (! (= (select (|Set#Intersection_17766| a@@23 b@@16) o@@9)  (and (select a@@23 o@@9) (select b@@16 o@@9)))
 :qid |DafnyPreludebpl.704:18|
 :skolemid |139|
 :pattern ( (select (|Set#Intersection_17766| a@@23 b@@16) o@@9))
)))
(assert (forall ((o@@10 T@Box) (p@@2 T@Box) ) (!  (or (or (|ORD#Less| o@@10 p@@2) (= o@@10 p@@2)) (|ORD#Less| p@@2 o@@10))
 :qid |DafnyPreludebpl.422:15|
 :skolemid |88|
 :pattern ( (|ORD#Less| o@@10 p@@2) (|ORD#Less| p@@2 o@@10))
)))
(assert (forall ((a@@24 (Array T@Box Bool)) (b@@17 (Array T@Box Bool)) (o@@11 T@Box) ) (! (= (select (|Set#Difference_17766| a@@24 b@@17) o@@11)  (and (select a@@24 o@@11) (not (select b@@17 o@@11))))
 :qid |DafnyPreludebpl.719:18|
 :skolemid |145|
 :pattern ( (select (|Set#Difference_17766| a@@24 b@@17) o@@11))
)))
(assert (forall ((v@@40 (Array T@Box Bool)) (t0@@3 T@Ty) (h@@28 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_12673 v@@40 (TSet t0@@3) h@@28) (forall ((bx@@6 T@Box) ) (!  (=> (select v@@40 bx@@6) ($IsAllocBox_13729 bx@@6 t0@@3 h@@28))
 :qid |DafnyPreludebpl.297:11|
 :skolemid |66|
 :pattern ( (select v@@40 bx@@6))
)))
 :qid |DafnyPreludebpl.295:15|
 :skolemid |67|
 :pattern ( ($IsAlloc_12673 v@@40 (TSet t0@@3) h@@28))
)))
(assert (forall ((v@@41 (Array T@Box Bool)) (t0@@4 T@Ty) (h@@29 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_12673 v@@41 (TISet t0@@4) h@@29) (forall ((bx@@7 T@Box) ) (!  (=> (select v@@41 bx@@7) ($IsAllocBox_13729 bx@@7 t0@@4 h@@29))
 :qid |DafnyPreludebpl.301:11|
 :skolemid |68|
 :pattern ( (select v@@41 bx@@7))
)))
 :qid |DafnyPreludebpl.299:15|
 :skolemid |69|
 :pattern ( ($IsAlloc_12673 v@@41 (TISet t0@@4) h@@29))
)))
(assert (forall ((o@@12 T@Box) ) (! (= (select |MultiSet#Empty_12631| o@@12) 0)
 :qid |DafnyPreludebpl.842:18|
 :skolemid |186|
 :pattern ( (select |MultiSet#Empty_12631| o@@12))
)))
(assert (forall ((m@@10 T@Map_20925_20926) (item T@Box) ) (! (= (select (|Map#Items_12644_12645| m@@10) item)  (and (select (|Map#Domain_12638_12639| m@@10) (_System.Tuple2._0 ($Unbox_13374 item))) (= (select (|Map#Elements_12638_12639| m@@10) (_System.Tuple2._0 ($Unbox_13374 item))) (_System.Tuple2._1 ($Unbox_13374 item)))))
 :qid |DafnyPreludebpl.1242:15|
 :skolemid |287|
 :pattern ( (select (|Map#Items_12644_12645| m@@10) item))
)))
(assert (forall ((m@@11 T@IMap_21069_21070) (item@@0 T@Box) ) (! (= (select (|IMap#Items_12655_12656| m@@11) item@@0)  (and (select (|IMap#Domain_12649_12650| m@@11) (_System.Tuple2._0 ($Unbox_13374 item@@0))) (= (select (|IMap#Elements_12649_12650| m@@11) (_System.Tuple2._0 ($Unbox_13374 item@@0))) (_System.Tuple2._1 ($Unbox_13374 item@@0)))))
 :qid |DafnyPreludebpl.1378:15|
 :skolemid |317|
 :pattern ( (select (|IMap#Items_12655_12656| m@@11) item@@0))
)))
(assert (forall ((m@@12 T@Map_20925_20926) (v@@42 T@Box) ) (! (= (select (|Map#Values_12644_12645| m@@12) v@@42) (exists ((u@@3 T@Box) ) (!  (and (select (|Map#Domain_12638_12639| m@@12) u@@3) (= v@@42 (select (|Map#Elements_12638_12639| m@@12) u@@3)))
 :qid |DafnyPreludebpl.1223:10|
 :skolemid |285|
 :pattern ( (select (|Map#Domain_12638_12639| m@@12) u@@3))
 :pattern ( (select (|Map#Elements_12638_12639| m@@12) u@@3))
)))
 :qid |DafnyPreludebpl.1221:20|
 :skolemid |286|
 :pattern ( (select (|Map#Values_12644_12645| m@@12) v@@42))
)))
(assert (forall ((m@@13 T@IMap_21069_21070) (v@@43 T@Box) ) (! (= (select (|IMap#Values_12655_12656| m@@13) v@@43) (exists ((u@@4 T@Box) ) (!  (and (select (|IMap#Domain_12649_12650| m@@13) u@@4) (= v@@43 (select (|IMap#Elements_12649_12650| m@@13) u@@4)))
 :qid |DafnyPreludebpl.1363:10|
 :skolemid |315|
 :pattern ( (select (|IMap#Domain_12649_12650| m@@13) u@@4))
 :pattern ( (select (|IMap#Elements_12649_12650| m@@13) u@@4))
)))
 :qid |DafnyPreludebpl.1361:20|
 :skolemid |316|
 :pattern ( (select (|IMap#Values_12655_12656| m@@13) v@@43))
)))
(assert (forall ((v@@44 T@Map_20925_20926) (t0@@5 T@Ty) (t1 T@Ty) (h@@30 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_23870 v@@44 (TMap t0@@5 t1) h@@30) (forall ((bx@@8 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| v@@44) bx@@8) (and ($IsAllocBox_13729 (select (|Map#Elements_12638_12639| v@@44) bx@@8) t1 h@@30) ($IsAllocBox_13729 bx@@8 t0@@5 h@@30)))
 :qid |DafnyPreludebpl.316:19|
 :skolemid |74|
 :pattern ( (select (|Map#Elements_12638_12639| v@@44) bx@@8))
 :pattern ( (select (|Map#Domain_12638_12639| v@@44) bx@@8))
)))
 :qid |DafnyPreludebpl.313:15|
 :skolemid |75|
 :pattern ( ($IsAlloc_23870 v@@44 (TMap t0@@5 t1) h@@30))
)))
(assert (forall ((v@@45 T@IMap_21069_21070) (t0@@6 T@Ty) (t1@@0 T@Ty) (h@@31 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_24132 v@@45 (TIMap t0@@6 t1@@0) h@@31) (forall ((bx@@9 T@Box) ) (!  (=> (select (|IMap#Domain_12649_12650| v@@45) bx@@9) (and ($IsAllocBox_13729 (select (|IMap#Elements_12649_12650| v@@45) bx@@9) t1@@0 h@@31) ($IsAllocBox_13729 bx@@9 t0@@6 h@@31)))
 :qid |DafnyPreludebpl.325:19|
 :skolemid |76|
 :pattern ( (select (|IMap#Elements_12649_12650| v@@45) bx@@9))
 :pattern ( (select (|IMap#Domain_12649_12650| v@@45) bx@@9))
)))
 :qid |DafnyPreludebpl.322:15|
 :skolemid |77|
 :pattern ( ($IsAlloc_24132 v@@45 (TIMap t0@@6 t1@@0) h@@31))
)))
(assert (forall ((o@@13 T@Box) (p@@3 T@Box) ) (!  (and (=> (= o@@13 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@13 p@@3) p@@3)) (=> (= p@@3 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@13 p@@3) o@@13)))
 :qid |DafnyPreludebpl.444:15|
 :skolemid |93|
 :pattern ( (|ORD#Plus| o@@13 p@@3))
)))
(assert (forall ((o@@14 T@Box) (p@@4 T@Box) ) (! (= (|ORD#LessThanLimit| o@@14 p@@4) (|ORD#Less| o@@14 p@@4))
 :qid |DafnyPreludebpl.432:15|
 :skolemid |90|
 :pattern ( (|ORD#LessThanLimit| o@@14 p@@4))
)))
(assert (forall ((a@@25 T@Seq_20794) (b@@18 T@Seq_20794) ) (!  (=> (|Seq#Equal_20794| a@@25 b@@18) (= a@@25 b@@18))
 :qid |DafnyPreludebpl.1063:18|
 :skolemid |247|
 :pattern ( (|Seq#Equal_20794| a@@25 b@@18))
)))
(assert (forall ((m@@14 T@Map_20925_20926) (|m'@@0| T@Map_20925_20926) ) (!  (=> (|Map#Equal_20925_20926| m@@14 |m'@@0|) (= m@@14 |m'@@0|))
 :qid |DafnyPreludebpl.1313:21|
 :skolemid |303|
 :pattern ( (|Map#Equal_20925_20926| m@@14 |m'@@0|))
)))
(assert (forall ((m@@15 T@IMap_21069_21070) (|m'@@1| T@IMap_21069_21070) ) (!  (=> (|IMap#Equal_21069_21070| m@@15 |m'@@1|) (= m@@15 |m'@@1|))
 :qid |DafnyPreludebpl.1423:21|
 :skolemid |327|
 :pattern ( (|IMap#Equal_21069_21070| m@@15 |m'@@1|))
)))
(assert (forall ((a@@26 (Array T@Box Bool)) (x@@25 T@Box) (y@@15 T@Box) ) (!  (=> (select a@@26 y@@15) (select (|Set#UnionOne_17766| a@@26 x@@25) y@@15))
 :qid |DafnyPreludebpl.680:18|
 :skolemid |132|
 :pattern ( (|Set#UnionOne_17766| a@@26 x@@25) (select a@@26 y@@15))
)))
(assert (forall ((a@@27 (Array T@Box Bool)) (b@@19 (Array T@Box Bool)) (y@@16 T@Box) ) (!  (=> (select a@@27 y@@16) (select (|Set#Union_17766| a@@27 b@@19) y@@16))
 :qid |DafnyPreludebpl.690:18|
 :skolemid |136|
 :pattern ( (|Set#Union_17766| a@@27 b@@19) (select a@@27 y@@16))
)))
(assert (forall ((a@@28 (Array T@Box Bool)) (b@@20 (Array T@Box Bool)) (y@@17 T@Box) ) (!  (=> (select b@@20 y@@17) (select (|Set#Union_17766| a@@28 b@@20) y@@17))
 :qid |DafnyPreludebpl.692:18|
 :skolemid |137|
 :pattern ( (|Set#Union_17766| a@@28 b@@20) (select b@@20 y@@17))
)))
(assert (forall ((a@@29 (Array T@Box Bool)) (x@@26 T@Box) (o@@15 T@Box) ) (! (= (select (|Set#UnionOne_17766| a@@29 x@@26) o@@15)  (or (= o@@15 x@@26) (select a@@29 o@@15)))
 :qid |DafnyPreludebpl.676:18|
 :skolemid |130|
 :pattern ( (select (|Set#UnionOne_17766| a@@29 x@@26) o@@15))
)))
(assert (forall ((s@@23 T@Seq_20794) (n@@11 Int) ) (!  (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length_12635| s@@23))) (= (|Seq#Length_12635| (|Seq#Take_13347| s@@23 n@@11)) n@@11))
 :qid |DafnyPreludebpl.1073:18|
 :skolemid |250|
 :pattern ( (|Seq#Length_12635| (|Seq#Take_13347| s@@23 n@@11)))
)))
(assert (forall ((a@@30 (Array T@ref T@PolymorphicMapType_21225)) (b@@21 (Array T@ref T@PolymorphicMapType_21225)) (c (Array T@ref T@PolymorphicMapType_21225)) ) (!  (=> (not (= a@@30 c)) (=> (and ($HeapSucc a@@30 b@@21) ($HeapSucc b@@21 c)) ($HeapSucc a@@30 c)))
 :qid |DafnyPreludebpl.604:15|
 :skolemid |116|
 :pattern ( ($HeapSucc a@@30 b@@21) ($HeapSucc b@@21 c))
)))
(assert (forall ((a@@31 (Array T@Box Bool)) (b@@22 (Array T@Box Bool)) (y@@18 T@Box) ) (!  (=> (select b@@22 y@@18) (not (select (|Set#Difference_17766| a@@31 b@@22) y@@18)))
 :qid |DafnyPreludebpl.721:18|
 :skolemid |146|
 :pattern ( (|Set#Difference_17766| a@@31 b@@22) (select b@@22 y@@18))
)))
(assert (forall ((m@@16 T@IMap_21069_21070) ) (! (= (= m@@16 |IMap#Empty_21069_21070|) (= (|IMap#Domain_12649_12650| m@@16) |ISet#Empty_18379|))
 :qid |DafnyPreludebpl.1344:21|
 :skolemid |312|
 :pattern ( (|IMap#Domain_12649_12650| m@@16))
)))
(assert (forall ((m@@17 T@IMap_21069_21070) ) (! (= (= m@@17 |IMap#Empty_21069_21070|) (= (|IMap#Values_12655_12656| m@@17) |ISet#Empty_18379|))
 :qid |DafnyPreludebpl.1347:21|
 :skolemid |313|
 :pattern ( (|IMap#Values_12655_12656| m@@17))
)))
(assert (forall ((m@@18 T@IMap_21069_21070) ) (! (= (= m@@18 |IMap#Empty_21069_21070|) (= (|IMap#Items_12655_12656| m@@18) |ISet#Empty_18379|))
 :qid |DafnyPreludebpl.1350:21|
 :skolemid |314|
 :pattern ( (|IMap#Items_12655_12656| m@@18))
)))
(assert (forall ((x@@27 Real) ) (! (= (q@Int x@@27) (to_int x@@27))
 :qid |DafnyPreludebpl.576:14|
 :skolemid |112|
 :pattern ( (q@Int x@@27))
)))
(assert (forall ((x@@28 Int) ) (! (= (LitInt x@@28) x@@28)
 :qid |DafnyPreludebpl.108:29|
 :skolemid |17|
 :pattern ( (LitInt x@@28))
)))
(assert (forall ((x@@29 Real) ) (! (= (LitReal x@@29) x@@29)
 :qid |DafnyPreludebpl.111:30|
 :skolemid |19|
 :pattern ( (LitReal x@@29))
)))
(assert (forall ((x@@30 T@Box) ) (! (= (Lit_13549 x@@30) x@@30)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_13549 x@@30))
)))
(assert (forall ((x@@31 Int) ) (! (= (Lit_552 x@@31) x@@31)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_552 x@@31))
)))
(assert (forall ((x@@32 Real) ) (! (= (Lit_594 x@@32) x@@32)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_594 x@@32))
)))
(assert (forall ((x@@33 Bool) ) (! (= (Lit_926 x@@33) x@@33)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_926 x@@33))
)))
(assert (forall ((x@@34 T@char) ) (! (= (Lit_12554 x@@34) x@@34)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_12554 x@@34))
)))
(assert (forall ((x@@35 (Array T@Box Bool)) ) (! (= (Lit_12565 x@@35) x@@35)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_12565 x@@35))
)))
(assert (forall ((x@@36 (Array T@Box Int)) ) (! (= (Lit_12581 x@@36) x@@36)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_12581 x@@36))
)))
(assert (forall ((x@@37 T@Seq_20794) ) (! (= (Lit_20812 x@@37) x@@37)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_20812 x@@37))
)))
(assert (forall ((x@@38 T@Map_20925_20926) ) (! (= (Lit_20946 x@@38) x@@38)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_20946 x@@38))
)))
(assert (forall ((x@@39 T@IMap_21069_21070) ) (! (= (Lit_21090 x@@39) x@@39)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_21090 x@@39))
)))
(assert (forall ((x@@40 T@DatatypeType) ) (! (= (Lit_12753 x@@40) x@@40)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_12753 x@@40))
)))
(assert (forall ((x@@41 T@ref) ) (! (= (Lit_12882 x@@41) x@@41)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit_12882 x@@41))
)))
(assert (forall ((m@@19 T@Map_20925_20926) ) (!  (or (= m@@19 |Map#Empty_20925_20926|) (exists ((k@@15 T@Box) (v@@46 T@Box) ) (! (select (|Map#Items_12644_12645| m@@19) ($Box_12753 (|#_System._tuple#2._#Make2| k@@15 v@@46)))
 :qid |DafnyPreludebpl.1202:31|
 :skolemid |280|
)))
 :qid |DafnyPreludebpl.1200:21|
 :skolemid |281|
 :pattern ( (|Map#Items_12644_12645| m@@19))
)))
(assert (forall ((m@@20 T@IMap_21069_21070) ) (!  (or (= m@@20 |IMap#Empty_21069_21070|) (exists ((k@@16 T@Box) (v@@47 T@Box) ) (! (select (|IMap#Items_12655_12656| m@@20) ($Box_12753 (|#_System._tuple#2._#Make2| k@@16 v@@47)))
 :qid |DafnyPreludebpl.1342:32|
 :skolemid |310|
)))
 :qid |DafnyPreludebpl.1340:21|
 :skolemid |311|
 :pattern ( (|IMap#Items_12655_12656| m@@20))
)))
(assert (forall ((a@@32 (Array T@Box Bool)) (b@@23 (Array T@Box Bool)) ) (!  (and (= (+ (+ (|Set#Card_17766| (|Set#Difference_17766| a@@32 b@@23)) (|Set#Card_17766| (|Set#Difference_17766| b@@23 a@@32))) (|Set#Card_17766| (|Set#Intersection_17766| a@@32 b@@23))) (|Set#Card_17766| (|Set#Union_17766| a@@32 b@@23))) (= (|Set#Card_17766| (|Set#Difference_17766| a@@32 b@@23)) (- (|Set#Card_17766| a@@32) (|Set#Card_17766| (|Set#Intersection_17766| a@@32 b@@23)))))
 :qid |DafnyPreludebpl.723:18|
 :skolemid |147|
 :pattern ( (|Set#Card_17766| (|Set#Difference_17766| a@@32 b@@23)))
)))
(assert (forall ((v@@48 T@Box) (t@@30 T@Ty) ) (! (= ($IsBox_12550 ($Box_12809 v@@48) t@@30) ($Is_12448 v@@48 t@@30))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12809 v@@48) t@@30))
)))
(assert (forall ((v@@49 T@ref) (t@@31 T@Ty) ) (! (= ($IsBox_12550 ($Box_12882 v@@49) t@@31) ($Is_12882 v@@49 t@@31))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12882 v@@49) t@@31))
)))
(assert (forall ((v@@50 T@DatatypeType) (t@@32 T@Ty) ) (! (= ($IsBox_12550 ($Box_12753 v@@50) t@@32) ($Is_12753 v@@50 t@@32))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12753 v@@50) t@@32))
)))
(assert (forall ((v@@51 T@IMap_21069_21070) (t@@33 T@Ty) ) (! (= ($IsBox_12550 ($Box_21090 v@@51) t@@33) ($Is_21138 v@@51 t@@33))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_21090 v@@51) t@@33))
)))
(assert (forall ((v@@52 T@Map_20925_20926) (t@@34 T@Ty) ) (! (= ($IsBox_12550 ($Box_20946 v@@52) t@@34) ($Is_20994 v@@52 t@@34))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_20946 v@@52) t@@34))
)))
(assert (forall ((v@@53 T@Seq_20794) (t@@35 T@Ty) ) (! (= ($IsBox_12550 ($Box_20812 v@@53) t@@35) ($Is_20853 v@@53 t@@35))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_20812 v@@53) t@@35))
)))
(assert (forall ((v@@54 (Array T@Box Int)) (t@@36 T@Ty) ) (! (= ($IsBox_12550 ($Box_12581 v@@54) t@@36) ($Is_12584 v@@54 t@@36))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12581 v@@54) t@@36))
)))
(assert (forall ((v@@55 (Array T@Box Bool)) (t@@37 T@Ty) ) (! (= ($IsBox_12550 ($Box_12565 v@@55) t@@37) ($Is_12560 v@@55 t@@37))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12565 v@@55) t@@37))
)))
(assert (forall ((v@@56 T@char) (t@@38 T@Ty) ) (! (= ($IsBox_12550 ($Box_12554 v@@56) t@@38) ($Is_12555 v@@56 t@@38))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_12554 v@@56) t@@38))
)))
(assert (forall ((v@@57 Bool) (t@@39 T@Ty) ) (! (= ($IsBox_12550 ($Box_926 v@@57) t@@39) ($Is_935 v@@57 t@@39))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_926 v@@57) t@@39))
)))
(assert (forall ((v@@58 Real) (t@@40 T@Ty) ) (! (= ($IsBox_12550 ($Box_594 v@@58) t@@40) ($Is_902 v@@58 t@@40))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_594 v@@58) t@@40))
)))
(assert (forall ((v@@59 Int) (t@@41 T@Ty) ) (! (= ($IsBox_12550 ($Box_552 v@@59) t@@41) ($Is_869 v@@59 t@@41))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox_12550 ($Box_552 v@@59) t@@41))
)))
(assert (forall ((s@@24 (Array T@Box Bool)) (a@@33 T@Box) ) (!  (and (= (= (select (|MultiSet#FromSet_12631| s@@24) a@@33) 0)  (not (select s@@24 a@@33))) (= (= (select (|MultiSet#FromSet_12631| s@@24) a@@33) 1) (select s@@24 a@@33)))
 :qid |DafnyPreludebpl.917:18|
 :skolemid |211|
 :pattern ( (select (|MultiSet#FromSet_12631| s@@24) a@@33))
)))
(assert (forall ((t@@42 T@Box) ) (! (= (|Seq#Index_12635| (|Seq#Singleton_12635| t@@42) 0) t@@42)
 :qid |DafnyPreludebpl.1016:18|
 :skolemid |232|
 :pattern ( (|Seq#Index_12635| (|Seq#Singleton_12635| t@@42) 0))
)))
(assert (forall ((s@@25 T@Seq_20794) (i@@12 Int) (v@@60 T@Box) (n@@12 Int) ) (!  (=> (and (<= n@@12 i@@12) (< i@@12 (|Seq#Length_12635| s@@25))) (= (|Seq#Take_13347| (|Seq#Update_13347| s@@25 i@@12 v@@60) n@@12) (|Seq#Take_13347| s@@25 n@@12)))
 :qid |DafnyPreludebpl.1133:18|
 :skolemid |262|
 :pattern ( (|Seq#Take_13347| (|Seq#Update_13347| s@@25 i@@12 v@@60) n@@12))
)))
(assert (forall ((r@@1 T@Box) (o@@16 T@Box) ) (!  (and (= (= (select (|MultiSet#Singleton_12631| r@@1) o@@16) 1) (= r@@1 o@@16)) (= (= (select (|MultiSet#Singleton_12631| r@@1) o@@16) 0) (not (= r@@1 o@@16))))
 :qid |DafnyPreludebpl.848:18|
 :skolemid |189|
 :pattern ( (select (|MultiSet#Singleton_12631| r@@1) o@@16))
)))
(assert (forall ((o@@17 T@Box) ) (! (<= 0 (|ORD#Offset| o@@17))
 :qid |DafnyPreludebpl.404:15|
 :skolemid |84|
 :pattern ( (|ORD#Offset| o@@17))
)))
(assert (forall ((o@@18 T@ref) ) (! (<= 0 (_System.array.Length o@@18))
 :qid |DafnyPreludebpl.569:15|
 :skolemid |111|
 :pattern ( (_System.array.Length o@@18))
)))
(assert (forall ((s@@26 (Array T@Box Bool)) ) (! (<= 0 (|Set#Card_17766| s@@26))
 :qid |DafnyPreludebpl.659:18|
 :skolemid |123|
 :pattern ( (|Set#Card_17766| s@@26))
)))
(assert (forall ((s@@27 (Array T@Box Int)) ) (! (<= 0 (|MultiSet#Card_12631| s@@27))
 :qid |DafnyPreludebpl.837:18|
 :skolemid |184|
 :pattern ( (|MultiSet#Card_12631| s@@27))
)))
(assert (forall ((s@@28 T@Seq_20794) ) (! (<= 0 (|Seq#Length_12635| s@@28))
 :qid |DafnyPreludebpl.962:18|
 :skolemid |221|
 :pattern ( (|Seq#Length_12635| s@@28))
)))
(assert (forall ((m@@21 T@Map_20925_20926) ) (! (<= 0 (|Map#Card_20925_20926| m@@21))
 :qid |DafnyPreludebpl.1188:20|
 :skolemid |274|
 :pattern ( (|Map#Card_20925_20926| m@@21))
)))
(assert (forall ((ty@@1 T@Ty) ) (!  (=> ($AlwaysAllocated ty@@1) (forall ((h@@32 (Array T@ref T@PolymorphicMapType_21225)) (v@@61 T@Box) ) (!  (=> ($IsBox_12550 v@@61 ty@@1) ($IsAllocBox_13729 v@@61 ty@@1 h@@32))
 :qid |DafnyPreludebpl.335:13|
 :skolemid |78|
 :pattern ( ($IsAllocBox_13729 v@@61 ty@@1 h@@32))
)))
 :qid |DafnyPreludebpl.333:17|
 :skolemid |79|
 :pattern ( ($AlwaysAllocated ty@@1))
)))
(assert (forall ((s@@29 T@Seq_20794) (i@@13 Int) (j@@2 Int) ) (!  (=> (and (and (<= 0 i@@13) (< i@@13 j@@2)) (<= j@@2 (|Seq#Length_12635| s@@29))) (< (|Seq#Rank_13371| (|Seq#Append_12631| (|Seq#Take_13347| s@@29 i@@13) (|Seq#Drop_20794| s@@29 j@@2))) (|Seq#Rank_13371| s@@29)))
 :qid |DafnyPreludebpl.1161:18|
 :skolemid |270|
 :pattern ( (|Seq#Rank_13371| (|Seq#Append_12631| (|Seq#Take_13347| s@@29 i@@13) (|Seq#Drop_20794| s@@29 j@@2))))
)))
(assert (forall ((a@@34 (Array T@Box Int)) (b@@24 (Array T@Box Int)) (o@@19 T@Box) ) (! (= (select (|MultiSet#Intersection_12631| a@@34 b@@24) o@@19) (|Math#min| (select a@@34 o@@19) (select b@@24 o@@19)))
 :qid |DafnyPreludebpl.877:18|
 :skolemid |198|
 :pattern ( (select (|MultiSet#Intersection_12631| a@@34 b@@24) o@@19))
)))
(assert (forall ((t@@43 T@Ty) (u@@5 T@Ty) ) (! (= (Inv0_TMap (TMap t@@43 u@@5)) t@@43)
 :qid |DafnyPreludebpl.57:15|
 :skolemid |9|
 :pattern ( (TMap t@@43 u@@5))
)))
(assert (forall ((t@@44 T@Ty) (u@@6 T@Ty) ) (! (= (Inv1_TMap (TMap t@@44 u@@6)) u@@6)
 :qid |DafnyPreludebpl.58:15|
 :skolemid |10|
 :pattern ( (TMap t@@44 u@@6))
)))
(assert (forall ((t@@45 T@Ty) (u@@7 T@Ty) ) (! (= (Tag (TMap t@@45 u@@7)) TagMap)
 :qid |DafnyPreludebpl.59:15|
 :skolemid |11|
 :pattern ( (TMap t@@45 u@@7))
)))
(assert (forall ((t@@46 T@Ty) (u@@8 T@Ty) ) (! (= (Inv0_TIMap (TIMap t@@46 u@@8)) t@@46)
 :qid |DafnyPreludebpl.62:15|
 :skolemid |12|
 :pattern ( (TIMap t@@46 u@@8))
)))
(assert (forall ((t@@47 T@Ty) (u@@9 T@Ty) ) (! (= (Inv1_TIMap (TIMap t@@47 u@@9)) u@@9)
 :qid |DafnyPreludebpl.63:15|
 :skolemid |13|
 :pattern ( (TIMap t@@47 u@@9))
)))
(assert (forall ((t@@48 T@Ty) (u@@10 T@Ty) ) (! (= (Tag (TIMap t@@48 u@@10)) TagIMap)
 :qid |DafnyPreludebpl.64:15|
 :skolemid |14|
 :pattern ( (TIMap t@@48 u@@10))
)))
(assert (forall ((v@@62 T@Seq_20794) (t0@@7 T@Ty) (h@@33 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_23682 v@@62 (TSeq t0@@7) h@@33) (forall ((i@@14 Int) ) (!  (=> (and (<= 0 i@@14) (< i@@14 (|Seq#Length_12635| v@@62))) ($IsAllocBox_13729 (|Seq#Index_12635| v@@62 i@@14) t0@@7 h@@33))
 :qid |DafnyPreludebpl.309:11|
 :skolemid |72|
 :pattern ( (|Seq#Index_12635| v@@62 i@@14))
)))
 :qid |DafnyPreludebpl.307:15|
 :skolemid |73|
 :pattern ( ($IsAlloc_23682 v@@62 (TSeq t0@@7) h@@33))
)))
(assert (forall ((a@@35 (Array T@Box Bool)) (x@@42 T@Box) ) (! (select (|Set#UnionOne_17766| a@@35 x@@42) x@@42)
 :qid |DafnyPreludebpl.678:18|
 :skolemid |131|
 :pattern ( (|Set#UnionOne_17766| a@@35 x@@42))
)))
(assert (forall ((a@@36 (Array T@Box Bool)) (x@@43 T@Box) ) (!  (=> (select a@@36 x@@43) (= (|Set#Card_17766| (|Set#UnionOne_17766| a@@36 x@@43)) (|Set#Card_17766| a@@36)))
 :qid |DafnyPreludebpl.682:18|
 :skolemid |133|
 :pattern ( (|Set#Card_17766| (|Set#UnionOne_17766| a@@36 x@@43)))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |DafnyPreludebpl.38:15|
 :skolemid |0|
 :pattern ( (TBitvector w))
)))
(assert (forall ((t@@49 T@Ty) ) (! (= (Inv0_TSet (TSet t@@49)) t@@49)
 :qid |DafnyPreludebpl.41:15|
 :skolemid |1|
 :pattern ( (TSet t@@49))
)))
(assert (forall ((t@@50 T@Ty) ) (! (= (Tag (TSet t@@50)) TagSet)
 :qid |DafnyPreludebpl.42:15|
 :skolemid |2|
 :pattern ( (TSet t@@50))
)))
(assert (forall ((t@@51 T@Ty) ) (! (= (Inv0_TISet (TISet t@@51)) t@@51)
 :qid |DafnyPreludebpl.45:15|
 :skolemid |3|
 :pattern ( (TISet t@@51))
)))
(assert (forall ((t@@52 T@Ty) ) (! (= (Tag (TISet t@@52)) TagISet)
 :qid |DafnyPreludebpl.46:15|
 :skolemid |4|
 :pattern ( (TISet t@@52))
)))
(assert (forall ((t@@53 T@Ty) ) (! (= (Inv0_TMultiSet (TMultiSet t@@53)) t@@53)
 :qid |DafnyPreludebpl.49:15|
 :skolemid |5|
 :pattern ( (TMultiSet t@@53))
)))
(assert (forall ((t@@54 T@Ty) ) (! (= (Tag (TMultiSet t@@54)) TagMultiSet)
 :qid |DafnyPreludebpl.50:15|
 :skolemid |6|
 :pattern ( (TMultiSet t@@54))
)))
(assert (forall ((t@@55 T@Ty) ) (! (= (Inv0_TSeq (TSeq t@@55)) t@@55)
 :qid |DafnyPreludebpl.53:15|
 :skolemid |7|
 :pattern ( (TSeq t@@55))
)))
(assert (forall ((t@@56 T@Ty) ) (! (= (Tag (TSeq t@@56)) TagSeq)
 :qid |DafnyPreludebpl.54:15|
 :skolemid |8|
 :pattern ( (TSeq t@@56))
)))
(assert (forall ((x@@44 T@DatatypeType) ) (! (= ($Unbox_13374 ($Box_12753 x@@44)) x@@44)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12753 x@@44))
)))
(assert (forall ((x@@45 T@Box) ) (! (= ($Unbox_12809 ($Box_12809 x@@45)) x@@45)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12809 x@@45))
)))
(assert (forall ((x@@46 T@ref) ) (! (= ($Unbox_12740 ($Box_12882 x@@46)) x@@46)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12882 x@@46))
)))
(assert (forall ((x@@47 T@IMap_21069_21070) ) (! (= ($Unbox_21073 ($Box_21090 x@@47)) x@@47)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_21090 x@@47))
)))
(assert (forall ((x@@48 T@Map_20925_20926) ) (! (= ($Unbox_20929 ($Box_20946 x@@48)) x@@48)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_20946 x@@48))
)))
(assert (forall ((x@@49 T@Seq_20794) ) (! (= ($Unbox_20797 ($Box_20812 x@@49)) x@@49)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_20812 x@@49))
)))
(assert (forall ((x@@50 (Array T@Box Int)) ) (! (= ($Unbox_12581 ($Box_12581 x@@50)) x@@50)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12581 x@@50))
)))
(assert (forall ((x@@51 (Array T@Box Bool)) ) (! (= ($Unbox_12560 ($Box_12565 x@@51)) x@@51)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12565 x@@51))
)))
(assert (forall ((x@@52 T@char) ) (! (= ($Unbox_12554 ($Box_12554 x@@52)) x@@52)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_12554 x@@52))
)))
(assert (forall ((x@@53 Bool) ) (! (= ($Unbox_926 ($Box_926 x@@53)) x@@53)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_926 x@@53))
)))
(assert (forall ((x@@54 Real) ) (! (= ($Unbox_893 ($Box_594 x@@54)) x@@54)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_594 x@@54))
)))
(assert (forall ((x@@55 Int) ) (! (= ($Unbox_860 ($Box_552 x@@55)) x@@55)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box_552 x@@55))
)))
(assert (forall ((i@@15 Int) ) (! (= (FDim_12809 (IndexField i@@15)) 1)
 :qid |DafnyPreludebpl.513:15|
 :skolemid |102|
 :pattern ( (IndexField i@@15))
)))
(assert (forall ((i@@16 Int) ) (! (= (IndexField_Inverse_12809 (IndexField i@@16)) i@@16)
 :qid |DafnyPreludebpl.515:15|
 :skolemid |103|
 :pattern ( (IndexField i@@16))
)))
(assert (forall ((i@@17 Int) ) (! (= (q@Int (q@Real i@@17)) i@@17)
 :qid |DafnyPreludebpl.578:15|
 :skolemid |114|
 :pattern ( (q@Int (q@Real i@@17)))
)))
(assert (forall ((r@@2 T@Box) ) (! (= (|Set#Card_17766| (|Set#Singleton_17766| r@@2)) 1)
 :qid |DafnyPreludebpl.673:18|
 :skolemid |129|
 :pattern ( (|Set#Card_17766| (|Set#Singleton_17766| r@@2)))
)))
(assert (forall ((t@@57 T@Box) ) (! (= (|Seq#Length_12635| (|Seq#Singleton_12635| t@@57)) 1)
 :qid |DafnyPreludebpl.980:18|
 :skolemid |224|
 :pattern ( (|Seq#Length_12635| (|Seq#Singleton_12635| t@@57)))
)))
(assert (forall ((v@@63 T@Map_20925_20926) (t0@@8 T@Ty) (t1@@1 T@Ty) ) (! (= ($Is_20994 v@@63 (TMap t0@@8 t1@@1)) (forall ((bx@@10 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| v@@63) bx@@10) (and ($IsBox_12550 (select (|Map#Elements_12638_12639| v@@63) bx@@10) t1@@1) ($IsBox_12550 bx@@10 t0@@8)))
 :qid |DafnyPreludebpl.259:19|
 :skolemid |54|
 :pattern ( (select (|Map#Elements_12638_12639| v@@63) bx@@10))
 :pattern ( (select (|Map#Domain_12638_12639| v@@63) bx@@10))
)))
 :qid |DafnyPreludebpl.256:15|
 :skolemid |55|
 :pattern ( ($Is_20994 v@@63 (TMap t0@@8 t1@@1)))
)))
(assert (forall ((v@@64 T@IMap_21069_21070) (t0@@9 T@Ty) (t1@@2 T@Ty) ) (! (= ($Is_21138 v@@64 (TIMap t0@@9 t1@@2)) (forall ((bx@@11 T@Box) ) (!  (=> (select (|IMap#Domain_12649_12650| v@@64) bx@@11) (and ($IsBox_12550 (select (|IMap#Elements_12649_12650| v@@64) bx@@11) t1@@2) ($IsBox_12550 bx@@11 t0@@9)))
 :qid |DafnyPreludebpl.274:19|
 :skolemid |57|
 :pattern ( (select (|IMap#Elements_12649_12650| v@@64) bx@@11))
 :pattern ( (select (|IMap#Domain_12649_12650| v@@64) bx@@11))
)))
 :qid |DafnyPreludebpl.271:15|
 :skolemid |58|
 :pattern ( ($Is_21138 v@@64 (TIMap t0@@9 t1@@2)))
)))
(assert (forall ((o@@20 T@Box) (p@@5 T@Box) ) (!  (and (and (and (=> (|ORD#Less| o@@20 p@@5) (not (= o@@20 p@@5))) (=> (and (|ORD#IsNat| o@@20) (not (|ORD#IsNat| p@@5))) (|ORD#Less| o@@20 p@@5))) (=> (and (|ORD#IsNat| o@@20) (|ORD#IsNat| p@@5)) (= (|ORD#Less| o@@20 p@@5) (< (|ORD#Offset| o@@20) (|ORD#Offset| p@@5))))) (=> (and (|ORD#Less| o@@20 p@@5) (|ORD#IsNat| p@@5)) (|ORD#IsNat| o@@20)))
 :qid |DafnyPreludebpl.416:15|
 :skolemid |87|
 :pattern ( (|ORD#Less| o@@20 p@@5))
)))
(assert (forall ((h@@34 (Array T@ref T@PolymorphicMapType_21225)) (i@@18 Int) (v@@65 T@Box) (a@@37 T@ref) ) (!  (=> (and (<= 0 i@@18) (< i@@18 (_System.array.Length a@@37))) (= (|Seq#FromArray| (store h@@34 a@@37 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@34 a@@37)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@34 a@@37)) (store (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@34 a@@37)) (IndexField i@@18) ($Box_12809 v@@65)))) a@@37) (|Seq#Update_13347| (|Seq#FromArray| h@@34 a@@37) i@@18 v@@65)))
 :qid |DafnyPreludebpl.1125:15|
 :skolemid |260|
 :pattern ( (|Seq#FromArray| (store h@@34 a@@37 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@34 a@@37)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@34 a@@37)) (store (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@34 a@@37)) (IndexField i@@18) ($Box_12809 v@@65)))) a@@37))
)))
(assert (forall ((r@@3 T@Box) ) (! (select (|Set#Singleton_17766| r@@3) r@@3)
 :qid |DafnyPreludebpl.671:18|
 :skolemid |127|
 :pattern ( (|Set#Singleton_17766| r@@3))
)))
(assert (forall ((m@@22 T@Map_20925_20926) (n@@13 T@Map_20925_20926) (u@@11 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| (|Map#Merge_12638_12639| m@@22 n@@13)) u@@11) (and (=> (not (select (|Map#Domain_12638_12639| n@@13) u@@11)) (= (select (|Map#Elements_12638_12639| (|Map#Merge_12638_12639| m@@22 n@@13)) u@@11) (select (|Map#Elements_12638_12639| m@@22) u@@11))) (=> (select (|Map#Domain_12638_12639| n@@13) u@@11) (= (select (|Map#Elements_12638_12639| (|Map#Merge_12638_12639| m@@22 n@@13)) u@@11) (select (|Map#Elements_12638_12639| n@@13) u@@11)))))
 :qid |DafnyPreludebpl.1291:21|
 :skolemid |297|
 :pattern ( (select (|Map#Elements_12638_12639| (|Map#Merge_12638_12639| m@@22 n@@13)) u@@11))
)))
(assert (forall ((m@@23 T@IMap_21069_21070) (n@@14 T@IMap_21069_21070) (u@@12 T@Box) ) (!  (=> (select (|IMap#Domain_12649_12650| (|IMap#Merge_12649_12650| m@@23 n@@14)) u@@12) (and (=> (not (select (|IMap#Domain_12649_12650| n@@14) u@@12)) (= (select (|IMap#Elements_12649_12650| (|IMap#Merge_12649_12650| m@@23 n@@14)) u@@12) (select (|IMap#Elements_12649_12650| m@@23) u@@12))) (=> (select (|IMap#Domain_12649_12650| n@@14) u@@12) (= (select (|IMap#Elements_12649_12650| (|IMap#Merge_12649_12650| m@@23 n@@14)) u@@12) (select (|IMap#Elements_12649_12650| n@@14) u@@12)))))
 :qid |DafnyPreludebpl.1432:21|
 :skolemid |329|
 :pattern ( (select (|IMap#Elements_12649_12650| (|IMap#Merge_12649_12650| m@@23 n@@14)) u@@12))
)))
(assert (forall ((s@@30 T@Seq_20794) (i@@19 Int) (v@@66 T@Box) (x@@56 T@Box) ) (!  (=> (and (<= 0 i@@19) (< i@@19 (|Seq#Length_12635| s@@30))) (= (select (|MultiSet#FromSeq_12631| (|Seq#Update_13347| s@@30 i@@19 v@@66)) x@@56) (select (|MultiSet#Union_12631| (|MultiSet#Difference_12631| (|MultiSet#FromSeq_12631| s@@30) (|MultiSet#Singleton_12631| (|Seq#Index_12635| s@@30 i@@19))) (|MultiSet#Singleton_12631| v@@66)) x@@56)))
 :qid |DafnyPreludebpl.946:18|
 :skolemid |218|
 :pattern ( (select (|MultiSet#FromSeq_12631| (|Seq#Update_13347| s@@30 i@@19 v@@66)) x@@56))
)))
(assert (forall ((a@@38 (Array T@Box Bool)) (b@@25 (Array T@Box Bool)) ) (! (= (|Set#Union_17766| a@@38 (|Set#Union_17766| a@@38 b@@25)) (|Set#Union_17766| a@@38 b@@25))
 :qid |DafnyPreludebpl.709:18|
 :skolemid |141|
 :pattern ( (|Set#Union_17766| a@@38 (|Set#Union_17766| a@@38 b@@25)))
)))
(assert (forall ((a@@39 (Array T@Box Bool)) (b@@26 (Array T@Box Bool)) ) (! (= (|Set#Intersection_17766| a@@39 (|Set#Intersection_17766| a@@39 b@@26)) (|Set#Intersection_17766| a@@39 b@@26))
 :qid |DafnyPreludebpl.713:18|
 :skolemid |143|
 :pattern ( (|Set#Intersection_17766| a@@39 (|Set#Intersection_17766| a@@39 b@@26)))
)))
(assert (forall ((a@@40 (Array T@Box Int)) (b@@27 (Array T@Box Int)) ) (! (= (|MultiSet#Intersection_12631| a@@40 (|MultiSet#Intersection_12631| a@@40 b@@27)) (|MultiSet#Intersection_12631| a@@40 b@@27))
 :qid |DafnyPreludebpl.883:18|
 :skolemid |200|
 :pattern ( (|MultiSet#Intersection_12631| a@@40 (|MultiSet#Intersection_12631| a@@40 b@@27)))
)))
(assert (forall ((m@@24 T@Map_20925_20926) (u@@13 T@Box) (|u'| T@Box) (v@@67 T@Box) ) (!  (and (=> (= |u'| u@@13) (and (select (|Map#Domain_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|) (= (select (|Map#Elements_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|) v@@67))) (=> (not (= |u'| u@@13)) (and (= (select (|Map#Domain_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|) (select (|Map#Domain_12638_12639| m@@24) |u'|)) (= (select (|Map#Elements_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|) (select (|Map#Elements_12638_12639| m@@24) |u'|)))))
 :qid |DafnyPreludebpl.1275:21|
 :skolemid |293|
 :pattern ( (select (|Map#Domain_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|))
 :pattern ( (select (|Map#Elements_12638_12639| (|Map#Build_12638_12639| m@@24 u@@13 v@@67)) |u'|))
)))
(assert (forall ((m@@25 T@IMap_21069_21070) (u@@14 T@Box) (|u'@@0| T@Box) (v@@68 T@Box) ) (!  (and (=> (= |u'@@0| u@@14) (and (select (|IMap#Domain_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|) (= (select (|IMap#Elements_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|) v@@68))) (=> (not (= |u'@@0| u@@14)) (and (= (select (|IMap#Domain_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|) (select (|IMap#Domain_12649_12650| m@@25) |u'@@0|)) (= (select (|IMap#Elements_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|) (select (|IMap#Elements_12649_12650| m@@25) |u'@@0|)))))
 :qid |DafnyPreludebpl.1409:21|
 :skolemid |323|
 :pattern ( (select (|IMap#Domain_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|))
 :pattern ( (select (|IMap#Elements_12649_12650| (|IMap#Build_12649_12650| m@@25 u@@14 v@@68)) |u'@@0|))
)))
(assert (forall ((n@@15 Int) ) (!  (=> (and (<= 0 n@@15) (< n@@15 65536)) (= (|char#ToInt| (|char#FromInt| n@@15)) n@@15))
 :qid |DafnyPreludebpl.131:15|
 :skolemid |21|
 :pattern ( (|char#FromInt| n@@15))
)))
(assert (forall ((o@@21 T@Box) ) (!  (not (select |Set#Empty_17766| o@@21))
 :qid |DafnyPreludebpl.662:18|
 :skolemid |124|
 :pattern ( (select |Set#Empty_17766| o@@21))
)))
(assert (forall ((o@@22 T@Box) ) (!  (not (select |ISet#Empty_18379| o@@22))
 :qid |DafnyPreludebpl.755:18|
 :skolemid |155|
 :pattern ( (select |ISet#Empty_18379| o@@22))
)))
(assert (forall ((h0 (Array T@ref T@PolymorphicMapType_21225)) (h1 (Array T@ref T@PolymorphicMapType_21225)) (a@@41 T@ref) ) (!  (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (= (select h0 a@@41) (select h1 a@@41))) (= (|Seq#FromArray| h0 a@@41) (|Seq#FromArray| h1 a@@41)))
 :qid |DafnyPreludebpl.1120:15|
 :skolemid |259|
 :pattern ( (|Seq#FromArray| h1 a@@41) ($HeapSucc h0 h1))
)))
(assert (forall ((s@@31 T@Seq_20794) (i@@20 Int) (v@@69 T@Box) ) (!  (=> (and (<= 0 i@@20) (< i@@20 (|Seq#Length_12635| s@@31))) (= (|Seq#Length_12635| (|Seq#Update_13347| s@@31 i@@20 v@@69)) (|Seq#Length_12635| s@@31)))
 :qid |DafnyPreludebpl.1022:18|
 :skolemid |234|
 :pattern ( (|Seq#Length_12635| (|Seq#Update_13347| s@@31 i@@20 v@@69)))
)))
(assert (forall ((a@@42 (Array T@Box Bool)) (b@@28 (Array T@Box T@Box)) (t0@@10 T@Ty) (t1@@3 T@Ty) ) (!  (=> (forall ((bx@@12 T@Box) ) (!  (=> (select a@@42 bx@@12) (and ($IsBox_12550 bx@@12 t0@@10) ($IsBox_12550 (select b@@28 bx@@12) t1@@3)))
 :qid |DafnyPreludebpl.1264:11|
 :skolemid |291|
)) ($Is_20994 (|Map#Glue_13429_13432| a@@42 b@@28 (TMap t0@@10 t1@@3)) (TMap t0@@10 t1@@3)))
 :qid |DafnyPreludebpl.1261:15|
 :skolemid |292|
 :pattern ( (|Map#Glue_13429_13432| a@@42 b@@28 (TMap t0@@10 t1@@3)))
)))
(assert (forall ((a@@43 (Array T@Box Bool)) (b@@29 (Array T@Box T@Box)) (t0@@11 T@Ty) (t1@@4 T@Ty) ) (!  (=> (forall ((bx@@13 T@Box) ) (!  (=> (select a@@43 bx@@13) (and ($IsBox_12550 bx@@13 t0@@11) ($IsBox_12550 (select b@@29 bx@@13) t1@@4)))
 :qid |DafnyPreludebpl.1399:11|
 :skolemid |321|
)) ($Is_20994 (|Map#Glue_13429_13432| a@@43 b@@29 (TIMap t0@@11 t1@@4)) (TIMap t0@@11 t1@@4)))
 :qid |DafnyPreludebpl.1396:15|
 :skolemid |322|
 :pattern ( (|IMap#Glue_13507_13510| a@@43 b@@29 (TIMap t0@@11 t1@@4)))
)))
(assert (forall ((h@@35 (Array T@ref T@PolymorphicMapType_21225)) (a@@44 T@ref) ) (! (= (|Seq#Length_12635| (|Seq#FromArray| h@@35 a@@44)) (_System.array.Length a@@44))
 :qid |DafnyPreludebpl.1105:15|
 :skolemid |256|
 :pattern ( (|Seq#Length_12635| (|Seq#FromArray| h@@35 a@@44)))
)))
(assert (forall ((a@@45 T@ClassName) (b@@30 T@ClassName) ) (!  (and (= (TypeTupleCar (TypeTuple a@@45 b@@30)) a@@45) (= (TypeTupleCdr (TypeTuple a@@45 b@@30)) b@@30))
 :qid |DafnyPreludebpl.359:15|
 :skolemid |80|
 :pattern ( (TypeTuple a@@45 b@@30))
)))
(assert (forall ((f@@0 T@Field_26410) (i@@21 Int) ) (!  (and (= (MultiIndexField_Inverse0_12814 (MultiIndexField f@@0 i@@21)) f@@0) (= (MultiIndexField_Inverse1_12814 (MultiIndexField f@@0 i@@21)) i@@21))
 :qid |DafnyPreludebpl.521:15|
 :skolemid |105|
 :pattern ( (MultiIndexField f@@0 i@@21))
)))
(assert (forall ((cl T@ClassName) (nm T@NameFamily) ) (!  (and (= (DeclType_3928 (FieldOfDecl_3928 cl nm)) cl) (= (DeclName_3928 (FieldOfDecl_3928 cl nm)) nm))
 :qid |DafnyPreludebpl.532:18|
 :skolemid |106|
 :pattern ( (FieldOfDecl_3928 cl nm))
)))
(assert (forall ((s@@32 T@Seq_20794) (val T@Box) ) (!  (and (= (|Seq#Build_inv0_13286| (|Seq#Build_13286| s@@32 val)) s@@32) (= (|Seq#Build_inv1_13286| (|Seq#Build_13286| s@@32 val)) val))
 :qid |DafnyPreludebpl.985:18|
 :skolemid |225|
 :pattern ( (|Seq#Build_13286| s@@32 val))
)))
(assert (forall ((m@@26 T@Map_20925_20926) (|m'@@2| T@Map_20925_20926) ) (! (= (|Map#Equal_20925_20926| m@@26 |m'@@2|)  (and (forall ((u@@15 T@Box) ) (! (= (select (|Map#Domain_12638_12639| m@@26) u@@15) (select (|Map#Domain_12638_12639| |m'@@2|) u@@15))
 :qid |DafnyPreludebpl.1310:35|
 :skolemid |300|
)) (forall ((u@@16 T@Box) ) (!  (=> (select (|Map#Domain_12638_12639| m@@26) u@@16) (= (select (|Map#Elements_12638_12639| m@@26) u@@16) (select (|Map#Elements_12638_12639| |m'@@2|) u@@16)))
 :qid |DafnyPreludebpl.1311:35|
 :skolemid |301|
))))
 :qid |DafnyPreludebpl.1308:21|
 :skolemid |302|
 :pattern ( (|Map#Equal_20925_20926| m@@26 |m'@@2|))
)))
(assert (forall ((m@@27 T@IMap_21069_21070) (|m'@@3| T@IMap_21069_21070) ) (! (= (|IMap#Equal_21069_21070| m@@27 |m'@@3|)  (and (forall ((u@@17 T@Box) ) (! (= (select (|IMap#Domain_12649_12650| m@@27) u@@17) (select (|IMap#Domain_12649_12650| |m'@@3|) u@@17))
 :qid |DafnyPreludebpl.1420:36|
 :skolemid |324|
)) (forall ((u@@18 T@Box) ) (!  (=> (select (|IMap#Domain_12649_12650| m@@27) u@@18) (= (select (|IMap#Elements_12649_12650| m@@27) u@@18) (select (|IMap#Elements_12649_12650| |m'@@3|) u@@18)))
 :qid |DafnyPreludebpl.1421:35|
 :skolemid |325|
))))
 :qid |DafnyPreludebpl.1418:21|
 :skolemid |326|
 :pattern ( (|IMap#Equal_21069_21070| m@@27 |m'@@3|))
)))
(assert (forall ((bx@@14 T@Box) ) (!  (=> ($IsBox_12550 bx@@14 TInt) (and (= ($Box_552 ($Unbox_860 bx@@14)) bx@@14) ($Is_869 ($Unbox_860 bx@@14) TInt)))
 :qid |DafnyPreludebpl.174:15|
 :skolemid |26|
 :pattern ( ($IsBox_12550 bx@@14 TInt))
)))
(assert (forall ((bx@@15 T@Box) ) (!  (=> ($IsBox_12550 bx@@15 TReal) (and (= ($Box_594 ($Unbox_893 bx@@15)) bx@@15) ($Is_902 ($Unbox_893 bx@@15) TReal)))
 :qid |DafnyPreludebpl.177:15|
 :skolemid |27|
 :pattern ( ($IsBox_12550 bx@@15 TReal))
)))
(assert (forall ((bx@@16 T@Box) ) (!  (=> ($IsBox_12550 bx@@16 TBool) (and (= ($Box_926 ($Unbox_926 bx@@16)) bx@@16) ($Is_935 ($Unbox_926 bx@@16) TBool)))
 :qid |DafnyPreludebpl.180:15|
 :skolemid |28|
 :pattern ( ($IsBox_12550 bx@@16 TBool))
)))
(assert (forall ((bx@@17 T@Box) ) (!  (=> ($IsBox_12550 bx@@17 TChar) (and (= ($Box_12554 ($Unbox_12554 bx@@17)) bx@@17) ($Is_12555 ($Unbox_12554 bx@@17) TChar)))
 :qid |DafnyPreludebpl.183:15|
 :skolemid |29|
 :pattern ( ($IsBox_12550 bx@@17 TChar))
)))
(assert (forall ((o@@23 T@Box) (m@@28 Int) (n@@16 Int) ) (!  (=> (and (<= 0 m@@28) (<= 0 n@@16)) (= (|ORD#Plus| (|ORD#Plus| o@@23 (|ORD#FromNat| m@@28)) (|ORD#FromNat| n@@16)) (|ORD#Plus| o@@23 (|ORD#FromNat| (+ m@@28 n@@16)))))
 :qid |DafnyPreludebpl.459:15|
 :skolemid |96|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@23 (|ORD#FromNat| m@@28)) (|ORD#FromNat| n@@16)))
)))
(assert (forall ((d T@DatatypeType) ) (! (= (BoxRank ($Box_12753 d)) (DtRank d))
 :qid |DafnyPreludebpl.389:15|
 :skolemid |83|
 :pattern ( (BoxRank ($Box_12753 d)))
)))
(assert (forall ((r@@4 T@Box) ) (! (= (|MultiSet#Singleton_12631| r@@4) (|MultiSet#UnionOne_12631| |MultiSet#Empty_12631| r@@4))
 :qid |DafnyPreludebpl.850:18|
 :skolemid |190|
 :pattern ( (|MultiSet#Singleton_12631| r@@4))
)))
(assert (forall ((s@@33 (Array T@Box Bool)) ) (! (= (|MultiSet#Card_12631| (|MultiSet#FromSet_12631| s@@33)) (|Set#Card_17766| s@@33))
 :qid |DafnyPreludebpl.920:18|
 :skolemid |212|
 :pattern ( (|MultiSet#Card_12631| (|MultiSet#FromSet_12631| s@@33)))
)))
(assert (forall ((s@@34 T@Seq_20794) ) (! (= (|MultiSet#Card_12631| (|MultiSet#FromSeq_12631| s@@34)) (|Seq#Length_12635| s@@34))
 :qid |DafnyPreludebpl.931:18|
 :skolemid |215|
 :pattern ( (|MultiSet#Card_12631| (|MultiSet#FromSeq_12631| s@@34)))
)))
(assert (forall ((m@@29 T@Map_20925_20926) ) (! (= (|Set#Card_17766| (|Map#Domain_12638_12639| m@@29)) (|Map#Card_20925_20926| m@@29))
 :qid |DafnyPreludebpl.1204:21|
 :skolemid |282|
 :pattern ( (|Set#Card_17766| (|Map#Domain_12638_12639| m@@29)))
 :pattern ( (|Map#Card_20925_20926| m@@29))
)))
(assert (forall ((m@@30 T@Map_20925_20926) ) (! (= (|Set#Card_17766| (|Map#Items_12644_12645| m@@30)) (|Map#Card_20925_20926| m@@30))
 :qid |DafnyPreludebpl.1210:21|
 :skolemid |284|
 :pattern ( (|Set#Card_17766| (|Map#Items_12644_12645| m@@30)))
 :pattern ( (|Map#Card_20925_20926| m@@30))
)))
(assert (forall ((m@@31 T@Map_20925_20926) ) (! (<= (|Set#Card_17766| (|Map#Values_12644_12645| m@@31)) (|Map#Card_20925_20926| m@@31))
 :qid |DafnyPreludebpl.1207:21|
 :skolemid |283|
 :pattern ( (|Set#Card_17766| (|Map#Values_12644_12645| m@@31)))
 :pattern ( (|Map#Card_20925_20926| m@@31))
)))
(assert (forall ((s@@35 T@Seq_20794) (n@@17 Int) (x@@57 T@Box) ) (! (= (|Seq#Contains_20794| (|Seq#Drop_20794| s@@35 n@@17) x@@57) (exists ((i@@22 Int) ) (!  (and (and (and (<= 0 n@@17) (<= n@@17 i@@22)) (< i@@22 (|Seq#Length_12635| s@@35))) (= (|Seq#Index_12635| s@@35 i@@22) x@@57))
 :qid |DafnyPreludebpl.1054:13|
 :skolemid |243|
 :pattern ( (|Seq#Index_12635| s@@35 i@@22))
)))
 :qid |DafnyPreludebpl.1051:18|
 :skolemid |244|
 :pattern ( (|Seq#Contains_20794| (|Seq#Drop_20794| s@@35 n@@17) x@@57))
)))
(assert (forall ((a@@46 Int) (b@@31 Int) ) (! (= (<= a@@46 b@@31) (= (|Math#min| a@@46 b@@31) a@@46))
 :qid |DafnyPreludebpl.820:15|
 :skolemid |177|
 :pattern ( (|Math#min| a@@46 b@@31))
)))
(assert (forall ((a@@47 Int) (b@@32 Int) ) (! (= (<= b@@32 a@@47) (= (|Math#min| a@@47 b@@32) b@@32))
 :qid |DafnyPreludebpl.821:15|
 :skolemid |178|
 :pattern ( (|Math#min| a@@47 b@@32))
)))
(assert (forall ((o@@24 T@Box) (m@@32 Int) (n@@18 Int) ) (!  (=> (and (and (<= 0 m@@32) (<= 0 n@@18)) (<= n@@18 (+ (|ORD#Offset| o@@24) m@@32))) (and (=> (<= 0 (- m@@32 n@@18)) (= (|ORD#Minus| (|ORD#Plus| o@@24 (|ORD#FromNat| m@@32)) (|ORD#FromNat| n@@18)) (|ORD#Plus| o@@24 (|ORD#FromNat| (- m@@32 n@@18))))) (=> (<= (- m@@32 n@@18) 0) (= (|ORD#Minus| (|ORD#Plus| o@@24 (|ORD#FromNat| m@@32)) (|ORD#FromNat| n@@18)) (|ORD#Minus| o@@24 (|ORD#FromNat| (- n@@18 m@@32)))))))
 :qid |DafnyPreludebpl.469:15|
 :skolemid |98|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@24 (|ORD#FromNat| m@@32)) (|ORD#FromNat| n@@18)))
)))
(assert (forall ((o@@25 T@Box) (m@@33 Int) (n@@19 Int) ) (!  (=> (and (and (<= 0 m@@33) (<= 0 n@@19)) (<= n@@19 (+ (|ORD#Offset| o@@25) m@@33))) (and (=> (<= 0 (- m@@33 n@@19)) (= (|ORD#Plus| (|ORD#Minus| o@@25 (|ORD#FromNat| m@@33)) (|ORD#FromNat| n@@19)) (|ORD#Minus| o@@25 (|ORD#FromNat| (- m@@33 n@@19))))) (=> (<= (- m@@33 n@@19) 0) (= (|ORD#Plus| (|ORD#Minus| o@@25 (|ORD#FromNat| m@@33)) (|ORD#FromNat| n@@19)) (|ORD#Plus| o@@25 (|ORD#FromNat| (- n@@19 m@@33)))))))
 :qid |DafnyPreludebpl.475:15|
 :skolemid |99|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@25 (|ORD#FromNat| m@@33)) (|ORD#FromNat| n@@19)))
)))
(assert (= (|MultiSet#FromSeq_12631| |Seq#Empty_12631|) |MultiSet#Empty_12631|))
(assert (forall ((s@@36 T@Seq_20794) (v@@70 T@Box) ) (! (= (|MultiSet#FromSeq_12631| (|Seq#Build_13286| s@@36 v@@70)) (|MultiSet#UnionOne_12631| (|MultiSet#FromSeq_12631| s@@36) v@@70))
 :qid |DafnyPreludebpl.935:18|
 :skolemid |216|
 :pattern ( (|MultiSet#FromSeq_12631| (|Seq#Build_13286| s@@36 v@@70)))
)))
(assert (forall ((m@@34 T@Map_20925_20926) (s@@37 (Array T@Box Bool)) ) (! (= (|Map#Domain_12638_12639| (|Map#Subtract_12638_12639| m@@34 s@@37)) (|Set#Difference_17766| (|Map#Domain_12638_12639| m@@34) s@@37))
 :qid |DafnyPreludebpl.1298:21|
 :skolemid |298|
 :pattern ( (|Map#Domain_12638_12639| (|Map#Subtract_12638_12639| m@@34 s@@37)))
)))
(assert (forall ((m@@35 T@IMap_21069_21070) (s@@38 (Array T@Box Bool)) ) (! (= (|IMap#Domain_12649_12650| (|IMap#Subtract_12649_12650| m@@35 s@@38)) (|Set#Difference_17766| (|IMap#Domain_12649_12650| m@@35) s@@38))
 :qid |DafnyPreludebpl.1439:21|
 :skolemid |330|
 :pattern ( (|IMap#Domain_12649_12650| (|IMap#Subtract_12649_12650| m@@35 s@@38)))
)))
(assert (forall ((ch T@char) ) (!  (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (and (<= 0 (|char#ToInt| ch)) (< (|char#ToInt| ch) 65536)))
 :qid |DafnyPreludebpl.136:15|
 :skolemid |22|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((o@@26 T@Box) ) (!  (=> (|ORD#IsNat| o@@26) (= o@@26 (|ORD#FromNat| (|ORD#Offset| o@@26))))
 :qid |DafnyPreludebpl.412:15|
 :skolemid |86|
 :pattern ( (|ORD#Offset| o@@26))
 :pattern ( (|ORD#IsNat| o@@26))
)))
(assert (forall ((s@@39 (Array T@Box Bool)) ) (!  (and (= (= (|Set#Card_17766| s@@39) 0) (= s@@39 |Set#Empty_17766|)) (=> (not (= (|Set#Card_17766| s@@39) 0)) (exists ((x@@58 T@Box) ) (! (select s@@39 x@@58)
 :qid |DafnyPreludebpl.665:33|
 :skolemid |125|
))))
 :qid |DafnyPreludebpl.663:18|
 :skolemid |126|
 :pattern ( (|Set#Card_17766| s@@39))
)))
(assert (forall ((h@@36 (Array T@ref T@PolymorphicMapType_21225)) (r@@5 T@ref) (f@@1 T@Field_29474) (x@@59 (Array T@Box Bool)) ) (!  (=> ($IsGoodHeap (store h@@36 r@@5 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@36 r@@5)) (store (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@36 r@@5)) f@@1 ($Box_12565 x@@59)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@36 r@@5))))) ($HeapSucc h@@36 (store h@@36 r@@5 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@36 r@@5)) (store (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@36 r@@5)) f@@1 ($Box_12565 x@@59)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@36 r@@5))))))
 :qid |DafnyPreludebpl.601:22|
 :skolemid |115|
 :pattern ( (store h@@36 r@@5 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@36 r@@5)) (store (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@36 r@@5)) f@@1 ($Box_12565 x@@59)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@36 r@@5)))))
)))
(assert (forall ((h@@37 (Array T@ref T@PolymorphicMapType_21225)) (r@@6 T@ref) (f@@2 T@Field_3928) (x@@60 Bool) ) (!  (=> ($IsGoodHeap (store h@@37 r@@6 (PolymorphicMapType_21225 (store (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@37 r@@6)) f@@2 ($Box_926 x@@60)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@37 r@@6)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@37 r@@6))))) ($HeapSucc h@@37 (store h@@37 r@@6 (PolymorphicMapType_21225 (store (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@37 r@@6)) f@@2 ($Box_926 x@@60)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@37 r@@6)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@37 r@@6))))))
 :qid |DafnyPreludebpl.601:22|
 :skolemid |115|
 :pattern ( (store h@@37 r@@6 (PolymorphicMapType_21225 (store (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@37 r@@6)) f@@2 ($Box_926 x@@60)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@37 r@@6)) (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@37 r@@6)))))
)))
(assert (forall ((h@@38 (Array T@ref T@PolymorphicMapType_21225)) (r@@7 T@ref) (f@@3 T@Field_26410) (x@@61 T@Box) ) (!  (=> ($IsGoodHeap (store h@@38 r@@7 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@38 r@@7)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@38 r@@7)) (store (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@38 r@@7)) f@@3 ($Box_12809 x@@61))))) ($HeapSucc h@@38 (store h@@38 r@@7 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@38 r@@7)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@38 r@@7)) (store (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@38 r@@7)) f@@3 ($Box_12809 x@@61))))))
 :qid |DafnyPreludebpl.601:22|
 :skolemid |115|
 :pattern ( (store h@@38 r@@7 (PolymorphicMapType_21225 (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@38 r@@7)) (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@38 r@@7)) (store (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@38 r@@7)) f@@3 ($Box_12809 x@@61)))))
)))
(assert (forall ((u@@19 T@Box) ) (!  (not (select (|Map#Domain_12638_12639| |Map#Empty_20925_20926|) u@@19))
 :qid |DafnyPreludebpl.1250:21|
 :skolemid |288|
 :pattern ( (select (|Map#Domain_12638_12639| |Map#Empty_20925_20926|) u@@19))
)))
(assert (forall ((u@@20 T@Box) ) (!  (not (select (|IMap#Domain_12649_12650| |IMap#Empty_21069_21070|) u@@20))
 :qid |DafnyPreludebpl.1385:21|
 :skolemid |318|
 :pattern ( (select (|IMap#Domain_12649_12650| |IMap#Empty_21069_21070|) u@@20))
)))
(assert (forall ((s@@40 T@Seq_20794) (n@@20 Int) (k@@17 Int) ) (!  (=> (and (and (<= 0 n@@20) (<= n@@20 k@@17)) (< k@@17 (|Seq#Length_12635| s@@40))) (= (|Seq#Index_12635| (|Seq#Drop_20794| s@@40 n@@20) (- k@@17 n@@20)) (|Seq#Index_12635| s@@40 k@@17)))
 :qid |DafnyPreludebpl.1090:18|
 :weight 25
 :skolemid |254|
 :pattern ( (|Seq#Index_12635| s@@40 k@@17) (|Seq#Drop_20794| s@@40 n@@20))
)))
(assert (forall ((v@@71 (Array T@Box Int)) (t0@@12 T@Ty) (h@@39 (Array T@ref T@PolymorphicMapType_21225)) ) (! (= ($IsAlloc_12685 v@@71 (TMultiSet t0@@12) h@@39) (forall ((bx@@18 T@Box) ) (!  (=> (< 0 (select v@@71 bx@@18)) ($IsAllocBox_13729 bx@@18 t0@@12 h@@39))
 :qid |DafnyPreludebpl.305:11|
 :skolemid |70|
 :pattern ( (select v@@71 bx@@18))
)))
 :qid |DafnyPreludebpl.303:15|
 :skolemid |71|
 :pattern ( ($IsAlloc_12685 v@@71 (TMultiSet t0@@12) h@@39))
)))
(assert (forall ((o@@27 T@Box) (p@@6 T@Box) ) (!  (=> (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@27))) (or (and (= p@@6 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@27 p@@6) o@@27)) (and (not (= p@@6 (|ORD#FromNat| 0))) (|ORD#Less| (|ORD#Minus| o@@27 p@@6) o@@27))))
 :qid |DafnyPreludebpl.453:15|
 :skolemid |95|
 :pattern ( (|ORD#Minus| o@@27 p@@6))
)))
(assert (forall ((a@@48 (Array T@Box Bool)) (x@@62 T@Box) ) (!  (=> (not (select a@@48 x@@62)) (= (|Set#Card_17766| (|Set#UnionOne_17766| a@@48 x@@62)) (+ (|Set#Card_17766| a@@48) 1)))
 :qid |DafnyPreludebpl.684:18|
 :skolemid |134|
 :pattern ( (|Set#Card_17766| (|Set#UnionOne_17766| a@@48 x@@62)))
)))
(assert (forall ((s@@41 (Array T@ref Bool)) ) (! ($Is_12560 (SetRef_to_SetBox s@@41) (TSet Tclass._System.object?))
 :qid |DafnyPreludebpl.370:15|
 :skolemid |82|
 :pattern ( (SetRef_to_SetBox s@@41))
)))
(assert (forall ((s@@42 T@Seq_20794) (m@@36 Int) (n@@21 Int) ) (!  (=> (and (and (<= 0 m@@36) (<= 0 n@@21)) (<= (+ m@@36 n@@21) (|Seq#Length_12635| s@@42))) (= (|Seq#Drop_20794| (|Seq#Drop_20794| s@@42 m@@36) n@@21) (|Seq#Drop_20794| s@@42 (+ m@@36 n@@21))))
 :qid |DafnyPreludebpl.1170:18|
 :skolemid |273|
 :pattern ( (|Seq#Drop_20794| (|Seq#Drop_20794| s@@42 m@@36) n@@21))
)))
(assert (forall ((s0@@2 T@Seq_20794) (s1@@2 T@Seq_20794) (n@@22 Int) ) (! (= (|Seq#SameUntil_20794| s0@@2 s1@@2 n@@22) (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 n@@22)) (= (|Seq#Index_12635| s0@@2 j@@3) (|Seq#Index_12635| s1@@2 j@@3)))
 :qid |DafnyPreludebpl.1069:13|
 :skolemid |248|
 :pattern ( (|Seq#Index_12635| s0@@2 j@@3))
 :pattern ( (|Seq#Index_12635| s1@@2 j@@3))
)))
 :qid |DafnyPreludebpl.1067:18|
 :skolemid |249|
 :pattern ( (|Seq#SameUntil_20794| s0@@2 s1@@2 n@@22))
)))
(assert (forall ((a@@49 (Array T@Box Bool)) (b@@33 (Array T@Box Bool)) ) (! (= (|Set#Disjoint_17766| a@@49 b@@33) (forall ((o@@28 T@Box) ) (!  (or (not (select a@@49 o@@28)) (not (select b@@33 o@@28)))
 :qid |DafnyPreludebpl.746:34|
 :skolemid |153|
 :pattern ( (select a@@49 o@@28))
 :pattern ( (select b@@33 o@@28))
)))
 :qid |DafnyPreludebpl.745:18|
 :skolemid |154|
 :pattern ( (|Set#Disjoint_17766| a@@49 b@@33))
)))
(assert (forall ((a@@50 (Array T@Box Int)) (x@@63 T@Box) (y@@19 T@Box) ) (!  (=> (not (= x@@63 y@@19)) (= (select a@@50 y@@19) (select (|MultiSet#UnionOne_12631| a@@50 x@@63) y@@19)))
 :qid |DafnyPreludebpl.863:18|
 :skolemid |194|
 :pattern ( (|MultiSet#UnionOne_12631| a@@50 x@@63) (select a@@50 y@@19))
)))
(assert (forall ((s0@@3 T@Seq_20794) (s1@@3 T@Seq_20794) (n@@23 Int) ) (!  (and (=> (< n@@23 (|Seq#Length_12635| s0@@3)) (= (|Seq#Index_12635| (|Seq#Append_12631| s0@@3 s1@@3) n@@23) (|Seq#Index_12635| s0@@3 n@@23))) (=> (<= (|Seq#Length_12635| s0@@3) n@@23) (= (|Seq#Index_12635| (|Seq#Append_12631| s0@@3 s1@@3) n@@23) (|Seq#Index_12635| s1@@3 (- n@@23 (|Seq#Length_12635| s0@@3))))))
 :qid |DafnyPreludebpl.1017:18|
 :skolemid |233|
 :pattern ( (|Seq#Index_12635| (|Seq#Append_12631| s0@@3 s1@@3) n@@23))
)))
(assert (forall ((o@@29 T@Box) (p@@7 T@Box) ) (!  (and (=> (|ORD#IsNat| (|ORD#Plus| o@@29 p@@7)) (and (|ORD#IsNat| o@@29) (|ORD#IsNat| p@@7))) (=> (|ORD#IsNat| p@@7) (and (= (|ORD#IsNat| (|ORD#Plus| o@@29 p@@7)) (|ORD#IsNat| o@@29)) (= (|ORD#Offset| (|ORD#Plus| o@@29 p@@7)) (+ (|ORD#Offset| o@@29) (|ORD#Offset| p@@7))))))
 :qid |DafnyPreludebpl.436:15|
 :skolemid |91|
 :pattern ( (|ORD#Plus| o@@29 p@@7))
)))
(assert (forall ((a@@51 Int) ) (!  (=> (< a@@51 0) (= (|Math#clip| a@@51) 0))
 :qid |DafnyPreludebpl.826:15|
 :skolemid |181|
 :pattern ( (|Math#clip| a@@51))
)))
(assert (forall ((bx@@19 T@Box) (s@@43 T@Ty) (t@@58 T@Ty) ) (!  (=> ($IsBox_12550 bx@@19 (TMap s@@43 t@@58)) (and (= ($Box_20946 ($Unbox_20929 bx@@19)) bx@@19) ($Is_20994 ($Unbox_20929 bx@@19) (TMap s@@43 t@@58))))
 :qid |DafnyPreludebpl.205:15|
 :skolemid |35|
 :pattern ( ($IsBox_12550 bx@@19 (TMap s@@43 t@@58)))
)))
(assert (forall ((bx@@20 T@Box) (s@@44 T@Ty) (t@@59 T@Ty) ) (!  (=> ($IsBox_12550 bx@@20 (TIMap s@@44 t@@59)) (and (= ($Box_21090 ($Unbox_21073 bx@@20)) bx@@20) ($Is_21138 ($Unbox_21073 bx@@20) (TIMap s@@44 t@@59))))
 :qid |DafnyPreludebpl.208:15|
 :skolemid |36|
 :pattern ( ($IsBox_12550 bx@@20 (TIMap s@@44 t@@59)))
)))
(assert (forall ((x@@64 T@Box) ) (! (= ($Box_12809 (Lit_13549 x@@64)) (Lit_13549 ($Box_12809 x@@64)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12809 (Lit_13549 x@@64)))
)))
(assert (forall ((x@@65 T@ref) ) (! (= ($Box_12882 (Lit_12882 x@@65)) (Lit_13549 ($Box_12882 x@@65)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12882 (Lit_12882 x@@65)))
)))
(assert (forall ((x@@66 T@DatatypeType) ) (! (= ($Box_12753 (Lit_12753 x@@66)) (Lit_13549 ($Box_12753 x@@66)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12753 (Lit_12753 x@@66)))
)))
(assert (forall ((x@@67 T@IMap_21069_21070) ) (! (= ($Box_21090 (Lit_21090 x@@67)) (Lit_13549 ($Box_21090 x@@67)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_21090 (Lit_21090 x@@67)))
)))
(assert (forall ((x@@68 T@Map_20925_20926) ) (! (= ($Box_20946 (Lit_20946 x@@68)) (Lit_13549 ($Box_20946 x@@68)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_20946 (Lit_20946 x@@68)))
)))
(assert (forall ((x@@69 T@Seq_20794) ) (! (= ($Box_20812 (Lit_20812 x@@69)) (Lit_13549 ($Box_20812 x@@69)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_20812 (Lit_20812 x@@69)))
)))
(assert (forall ((x@@70 (Array T@Box Int)) ) (! (= ($Box_12581 (Lit_12581 x@@70)) (Lit_13549 ($Box_12581 x@@70)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12581 (Lit_12581 x@@70)))
)))
(assert (forall ((x@@71 (Array T@Box Bool)) ) (! (= ($Box_12565 (Lit_12565 x@@71)) (Lit_13549 ($Box_12565 x@@71)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12565 (Lit_12565 x@@71)))
)))
(assert (forall ((x@@72 T@char) ) (! (= ($Box_12554 (Lit_12554 x@@72)) (Lit_13549 ($Box_12554 x@@72)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_12554 (Lit_12554 x@@72)))
)))
(assert (forall ((x@@73 Bool) ) (! (= ($Box_926 (Lit_926 x@@73)) (Lit_13549 ($Box_926 x@@73)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_926 (Lit_926 x@@73)))
)))
(assert (forall ((x@@74 Real) ) (! (= ($Box_594 (Lit_594 x@@74)) (Lit_13549 ($Box_594 x@@74)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_594 (Lit_594 x@@74)))
)))
(assert (forall ((x@@75 Int) ) (! (= ($Box_552 (Lit_552 x@@75)) (Lit_13549 ($Box_552 x@@75)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box_552 (Lit_552 x@@75)))
)))
(assert (forall ((x@@76 Int) ) (! (= ($Box_552 (LitInt x@@76)) (Lit_13549 ($Box_552 x@@76)))
 :qid |DafnyPreludebpl.109:15|
 :skolemid |18|
 :pattern ( ($Box_552 (LitInt x@@76)))
)))
(assert (forall ((x@@77 Real) ) (! (= ($Box_594 (LitReal x@@77)) (Lit_13549 ($Box_594 x@@77)))
 :qid |DafnyPreludebpl.112:15|
 :skolemid |20|
 :pattern ( ($Box_594 (LitReal x@@77)))
)))
(assert (forall ((a@@52 T@Seq_20794) (b@@34 T@Seq_20794) ) (! (= (|MultiSet#FromSeq_12631| (|Seq#Append_12631| a@@52 b@@34)) (|MultiSet#Union_12631| (|MultiSet#FromSeq_12631| a@@52) (|MultiSet#FromSeq_12631| b@@34)))
 :qid |DafnyPreludebpl.941:18|
 :skolemid |217|
 :pattern ( (|MultiSet#FromSeq_12631| (|Seq#Append_12631| a@@52 b@@34)))
)))
(assert (forall ((m@@37 T@Map_20925_20926) (n@@24 T@Map_20925_20926) ) (! (= (|Map#Domain_12638_12639| (|Map#Merge_12638_12639| m@@37 n@@24)) (|Set#Union_17766| (|Map#Domain_12638_12639| m@@37) (|Map#Domain_12638_12639| n@@24)))
 :qid |DafnyPreludebpl.1288:21|
 :skolemid |296|
 :pattern ( (|Map#Domain_12638_12639| (|Map#Merge_12638_12639| m@@37 n@@24)))
)))
(assert (forall ((m@@38 T@IMap_21069_21070) (n@@25 T@IMap_21069_21070) ) (! (= (|IMap#Domain_12649_12650| (|IMap#Merge_12649_12650| m@@38 n@@25)) (|Set#Union_17766| (|IMap#Domain_12649_12650| m@@38) (|IMap#Domain_12649_12650| n@@25)))
 :qid |DafnyPreludebpl.1429:21|
 :skolemid |328|
 :pattern ( (|IMap#Domain_12649_12650| (|IMap#Merge_12649_12650| m@@38 n@@25)))
)))
(assert (forall ((s@@45 T@Seq_20794) ) (!  (=> (= (|Seq#Length_12635| s@@45) 0) (= s@@45 |Seq#Empty_12631|))
 :qid |DafnyPreludebpl.967:18|
 :skolemid |223|
 :pattern ( (|Seq#Length_12635| s@@45))
)))
(assert (forall ((s@@46 T@Seq_20794) (n@@26 Int) ) (!  (=> (= n@@26 0) (= (|Seq#Take_13347| s@@46 n@@26) |Seq#Empty_12631|))
 :qid |DafnyPreludebpl.1168:18|
 :skolemid |272|
 :pattern ( (|Seq#Take_13347| s@@46 n@@26))
)))
(assert (forall ((s@@47 (Array T@Box Int)) (x@@78 T@Box) (n@@27 Int) ) (!  (=> (<= 0 n@@27) (= (|MultiSet#Card_12631| (store s@@47 x@@78 n@@27)) (+ (- (|MultiSet#Card_12631| s@@47) (select s@@47 x@@78)) n@@27)))
 :qid |DafnyPreludebpl.838:18|
 :skolemid |185|
 :pattern ( (|MultiSet#Card_12631| (store s@@47 x@@78 n@@27)))
)))
(assert (forall ((h@@40 (Array T@ref T@PolymorphicMapType_21225)) (k@@18 (Array T@ref T@PolymorphicMapType_21225)) ) (!  (=> ($HeapSuccGhost h@@40 k@@18) (and ($HeapSucc h@@40 k@@18) (and (and (forall ((o@@30 T@ref) (f@@4 T@Field_3928) ) (!  (=> (not ($IsGhostField_3928 f@@4)) (= ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select h@@40 o@@30)) f@@4)) ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select k@@18 o@@30)) f@@4))))
 :qid |DafnyPreludebpl.542:20|
 :skolemid |107|
 :pattern ( ($Unbox_926 (select (|PolymorphicMapType_21225_3928#PolymorphicMapType_21225| (select k@@18 o@@30)) f@@4)))
)) (forall ((o@@31 T@ref) (f@@5 T@Field_26410) ) (!  (=> (not ($IsGhostField_26410 f@@5)) (= ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select h@@40 o@@31)) f@@5)) ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select k@@18 o@@31)) f@@5))))
 :qid |DafnyPreludebpl.542:20|
 :skolemid |107|
 :pattern ( ($Unbox_12809 (select (|PolymorphicMapType_21225_12809#PolymorphicMapType_21225| (select k@@18 o@@31)) f@@5)))
))) (forall ((o@@32 T@ref) (f@@6 T@Field_29474) ) (!  (=> (not ($IsGhostField_29474 f@@6)) (= ($Unbox_12560 (select (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select h@@40 o@@32)) f@@6)) ($Unbox_12560 (select (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select k@@18 o@@32)) f@@6))))
 :qid |DafnyPreludebpl.542:20|
 :skolemid |107|
 :pattern ( ($Unbox_12560 (select (|PolymorphicMapType_21225_12907#PolymorphicMapType_21225| (select k@@18 o@@32)) f@@6)))
)))))
 :qid |DafnyPreludebpl.539:15|
 :skolemid |108|
 :pattern ( ($HeapSuccGhost h@@40 k@@18))
)))
(assert (forall ((bx@@21 T@Box) ) (!  (=> ($IsBox_12550 bx@@21 (TBitvector 0)) (and (= ($Box_552 ($Unbox_860 bx@@21)) bx@@21) ($Is_12560 ($Unbox_12560 bx@@21) (TBitvector 0))))
 :qid |DafnyPreludebpl.189:15|
 :skolemid |30|
 :pattern ( ($IsBox_12550 bx@@21 (TBitvector 0)))
)))
(assert (forall ((bx@@22 T@Box) (t@@60 T@Ty) ) (!  (=> ($IsBox_12550 bx@@22 (TSet t@@60)) (and (= ($Box_12565 ($Unbox_12560 bx@@22)) bx@@22) ($Is_12560 ($Unbox_12560 bx@@22) (TSet t@@60))))
 :qid |DafnyPreludebpl.193:15|
 :skolemid |31|
 :pattern ( ($IsBox_12550 bx@@22 (TSet t@@60)))
)))
(assert (forall ((bx@@23 T@Box) (t@@61 T@Ty) ) (!  (=> ($IsBox_12550 bx@@23 (TISet t@@61)) (and (= ($Box_12565 ($Unbox_12560 bx@@23)) bx@@23) ($Is_12560 ($Unbox_12560 bx@@23) (TISet t@@61))))
 :qid |DafnyPreludebpl.196:15|
 :skolemid |32|
 :pattern ( ($IsBox_12550 bx@@23 (TISet t@@61)))
)))
(assert (forall ((bx@@24 T@Box) (t@@62 T@Ty) ) (!  (=> ($IsBox_12550 bx@@24 (TMultiSet t@@62)) (and (= ($Box_12581 ($Unbox_12581 bx@@24)) bx@@24) ($Is_12584 ($Unbox_12581 bx@@24) (TMultiSet t@@62))))
 :qid |DafnyPreludebpl.199:15|
 :skolemid |33|
 :pattern ( ($IsBox_12550 bx@@24 (TMultiSet t@@62)))
)))
(assert (forall ((bx@@25 T@Box) (t@@63 T@Ty) ) (!  (=> ($IsBox_12550 bx@@25 (TSeq t@@63)) (and (= ($Box_20812 ($Unbox_20797 bx@@25)) bx@@25) ($Is_20853 ($Unbox_20797 bx@@25) (TSeq t@@63))))
 :qid |DafnyPreludebpl.202:15|
 :skolemid |34|
 :pattern ( ($IsBox_12550 bx@@25 (TSeq t@@63)))
)))
(assert (forall ((a@@53 (Array T@Box Bool)) (b@@35 (Array T@Box Bool)) (o@@33 T@Box) ) (! (= (select (|Set#Union_17766| a@@53 b@@35) o@@33)  (or (select a@@53 o@@33) (select b@@35 o@@33)))
 :qid |DafnyPreludebpl.688:18|
 :skolemid |135|
 :pattern ( (select (|Set#Union_17766| a@@53 b@@35) o@@33))
)))
(assert (forall ((h@@41 (Array T@ref T@PolymorphicMapType_21225)) (v@@72 Int) ) (! ($IsAlloc_1910 v@@72 TInt h@@41)
 :qid |DafnyPreludebpl.287:14|
 :skolemid |60|
 :pattern ( ($IsAlloc_1910 v@@72 TInt h@@41))
)))
(assert (forall ((h@@42 (Array T@ref T@PolymorphicMapType_21225)) (v@@73 Real) ) (! ($IsAlloc_1929 v@@73 TReal h@@42)
 :qid |DafnyPreludebpl.288:14|
 :skolemid |61|
 :pattern ( ($IsAlloc_1929 v@@73 TReal h@@42))
)))
(assert (forall ((h@@43 (Array T@ref T@PolymorphicMapType_21225)) (v@@74 Bool) ) (! ($IsAlloc_1948 v@@74 TBool h@@43)
 :qid |DafnyPreludebpl.289:14|
 :skolemid |62|
 :pattern ( ($IsAlloc_1948 v@@74 TBool h@@43))
)))
(assert (forall ((h@@44 (Array T@ref T@PolymorphicMapType_21225)) (v@@75 T@char) ) (! ($IsAlloc_12666 v@@75 TChar h@@44)
 :qid |DafnyPreludebpl.290:14|
 :skolemid |63|
 :pattern ( ($IsAlloc_12666 v@@75 TChar h@@44))
)))
(assert (forall ((h@@45 (Array T@ref T@PolymorphicMapType_21225)) (v@@76 T@Box) ) (! ($IsAlloc_12448 v@@76 TORDINAL h@@45)
 :qid |DafnyPreludebpl.291:14|
 :skolemid |64|
 :pattern ( ($IsAlloc_12448 v@@76 TORDINAL h@@45))
)))
(assert (forall ((s@@48 T@Seq_20794) (i@@23 Int) (v@@77 T@Box) (n@@28 Int) ) (!  (=> (and (and (<= 0 i@@23) (< i@@23 n@@28)) (<= n@@28 (|Seq#Length_12635| s@@48))) (= (|Seq#Take_13347| (|Seq#Update_13347| s@@48 i@@23 v@@77) n@@28) (|Seq#Update_13347| (|Seq#Take_13347| s@@48 n@@28) i@@23 v@@77)))
 :qid |DafnyPreludebpl.1130:18|
 :skolemid |261|
 :pattern ( (|Seq#Take_13347| (|Seq#Update_13347| s@@48 i@@23 v@@77) n@@28))
)))
(assert (forall ((v@@78 T@Seq_20794) (t0@@13 T@Ty) ) (! (= ($Is_20853 v@@78 (TSeq t0@@13)) (forall ((i@@24 Int) ) (!  (=> (and (<= 0 i@@24) (< i@@24 (|Seq#Length_12635| v@@78))) ($IsBox_12550 (|Seq#Index_12635| v@@78 i@@24) t0@@13))
 :qid |DafnyPreludebpl.252:11|
 :skolemid |52|
 :pattern ( (|Seq#Index_12635| v@@78 i@@24))
)))
 :qid |DafnyPreludebpl.250:15|
 :skolemid |53|
 :pattern ( ($Is_20853 v@@78 (TSeq t0@@13)))
)))
(assert (forall ((v@@79 T@Map_20925_20926) (t0@@14 T@Ty) (t1@@5 T@Ty) ) (!  (=> ($Is_20994 v@@79 (TMap t0@@14 t1@@5)) (and (and ($Is_12560 (|Map#Domain_12638_12639| v@@79) (TSet t0@@14)) ($Is_12560 (|Map#Values_12644_12645| v@@79) (TSet t1@@5))) ($Is_12560 (|Map#Items_12644_12645| v@@79) (TSet (Tclass._System.Tuple2 t0@@14 t1@@5)))))
 :qid |DafnyPreludebpl.265:15|
 :skolemid |56|
 :pattern ( ($Is_20994 v@@79 (TMap t0@@14 t1@@5)))
)))
(assert (forall ((v@@80 T@IMap_21069_21070) (t0@@15 T@Ty) (t1@@6 T@Ty) ) (!  (=> ($Is_21138 v@@80 (TIMap t0@@15 t1@@6)) (and (and ($Is_12560 (|IMap#Domain_12649_12650| v@@80) (TISet t0@@15)) ($Is_12560 (|IMap#Values_12655_12656| v@@80) (TISet t1@@6))) ($Is_12560 (|IMap#Items_12655_12656| v@@80) (TISet (Tclass._System.Tuple2 t0@@15 t1@@6)))))
 :qid |DafnyPreludebpl.279:15|
 :skolemid |59|
 :pattern ( ($Is_21138 v@@80 (TIMap t0@@15 t1@@6)))
)))
(assert (forall ((v@@81 Int) ) (! ($Is_869 v@@81 TInt)
 :qid |DafnyPreludebpl.226:14|
 :skolemid |39|
 :pattern ( ($Is_869 v@@81 TInt))
)))
(assert (forall ((v@@82 Real) ) (! ($Is_902 v@@82 TReal)
 :qid |DafnyPreludebpl.227:14|
 :skolemid |40|
 :pattern ( ($Is_902 v@@82 TReal))
)))
(assert (forall ((v@@83 Bool) ) (! ($Is_935 v@@83 TBool)
 :qid |DafnyPreludebpl.228:14|
 :skolemid |41|
 :pattern ( ($Is_935 v@@83 TBool))
)))
(assert (forall ((v@@84 T@char) ) (! ($Is_12555 v@@84 TChar)
 :qid |DafnyPreludebpl.229:14|
 :skolemid |42|
 :pattern ( ($Is_12555 v@@84 TChar))
)))
(assert (forall ((v@@85 T@Box) ) (! ($Is_12448 v@@85 TORDINAL)
 :qid |DafnyPreludebpl.230:14|
 :skolemid |43|
 :pattern ( ($Is_12448 v@@85 TORDINAL))
)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $Heap () (Array T@ref T@PolymorphicMapType_21225))
(declare-fun $IsHeapAnchor ((Array T@ref T@PolymorphicMapType_21225)) Bool)
(set-info :boogie-vc-id should_not_prove)
(set-option :timeout 1000)
(set-option :rlimit 0)
(assert (not
 (=> (= (ControlFlow 0 0) 3) (let ((anon0_correct  (=> (= (ControlFlow 0 2) (- 0 1)) false)))
(let ((PreconditionGeneratedEntry_correct  (=> (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (= (ControlFlow 0 3) 2)) anon0_correct)))
PreconditionGeneratedEntry_correct)))
))
(check-sat)
(get-info :reason-unknown)
(assert (not (= (ControlFlow 0 2) (- 1))))
(check-sat)
(pop 1)
; Invalid
(get-info :rlimit)
