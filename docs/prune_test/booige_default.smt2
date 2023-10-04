(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun TBool () T@U)
(declare-fun TChar () T@U)
(declare-fun TInt () T@U)
(declare-fun TReal () T@U)
(declare-fun TORDINAL () T@U)
(declare-fun TagBool () T@U)
(declare-fun TagChar () T@U)
(declare-fun TagInt () T@U)
(declare-fun TagReal () T@U)
(declare-fun TagORDINAL () T@U)
(declare-fun TagSet () T@U)
(declare-fun TagISet () T@U)
(declare-fun TagMultiSet () T@U)
(declare-fun TagSeq () T@U)
(declare-fun TagMap () T@U)
(declare-fun TagIMap () T@U)
(declare-fun TagClass () T@U)
(declare-fun class._System.int () T@U)
(declare-fun class._System.bool () T@U)
(declare-fun class._System.set () T@U)
(declare-fun class._System.seq () T@U)
(declare-fun class._System.multiset () T@U)
(declare-fun alloc () T@U)
(declare-fun allocName () T@U)
(declare-fun Tagclass._System.nat () T@U)
(declare-fun class._System.object? () T@U)
(declare-fun Tagclass._System.object? () T@U)
(declare-fun Tagclass._System.object () T@U)
(declare-fun class._System.array? () T@U)
(declare-fun Tagclass._System.array? () T@U)
(declare-fun Tagclass._System.array () T@U)
(declare-fun Tagclass._System.___hFunc1 () T@U)
(declare-fun Tagclass._System.___hPartialFunc1 () T@U)
(declare-fun Tagclass._System.___hTotalFunc1 () T@U)
(declare-fun Tagclass._System.___hFunc0 () T@U)
(declare-fun Tagclass._System.___hPartialFunc0 () T@U)
(declare-fun Tagclass._System.___hTotalFunc0 () T@U)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun class._module.__default () T@U)
(declare-fun tytagFamily$nat () T@U)
(declare-fun tytagFamily$object () T@U)
(declare-fun tytagFamily$array () T@U)
(declare-fun |tytagFamily$_#Func1| () T@U)
(declare-fun |tytagFamily$_#PartialFunc1| () T@U)
(declare-fun |tytagFamily$_#TotalFunc1| () T@U)
(declare-fun |tytagFamily$_#Func0| () T@U)
(declare-fun |tytagFamily$_#PartialFunc0| () T@U)
(declare-fun |tytagFamily$_#TotalFunc0| () T@U)
(declare-fun |tytagFamily$_tuple#2| () T@U)
(declare-fun |tytagFamily$_tuple#0| () T@U)
(declare-fun Ctor (T@T) Int)
(declare-fun boolType () T@T)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun |Map#Disjoint| (T@T T@T T@U T@U) Bool)
(declare-fun MapType0Select (T@T T@T T@U T@U) T@U)
(declare-fun |Map#Domain| (T@T T@T T@U) T@U)
(declare-fun MapType0Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun FDim (T@T T@U) Int)
(declare-fun Tag (T@U) T@U)
(declare-fun DeclName (T@T T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun Reads0 (T@U T@U T@U) T@U)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $Is (T@T T@U T@U) Bool)
(declare-fun HandleTypeType () T@T)
(declare-fun Tclass._System.___hFunc0 (T@U) T@U)
(declare-fun null () T@U)
(declare-fun BoxType () T@T)
(declare-fun $Box (T@T T@U) T@U)
(declare-fun refType () T@T)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType1Select (T@T T@T T@U T@U) T@U)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType1Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun Apply0 (T@U T@U T@U) T@U)
(declare-fun Requires1 (T@U T@U T@U T@U T@U) Bool)
(declare-fun $OneHeap () T@U)
(declare-fun $IsBox (T@T T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc1 (T@U T@U) T@U)
(declare-fun |Set#Equal| (T@T T@U T@U) Bool)
(declare-fun Reads1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun |Set#Empty| (T@T) T@U)
(declare-fun $IsAlloc (T@T T@U T@U T@U) Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun Tclass._System.array? (T@U) T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun |MultiSet#Card| (T@T T@U) Int)
(declare-fun |MultiSet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@T T@U T@U) T@U)
(declare-fun |ORD#Less| (T@U T@U) Bool)
(declare-fun Tclass._System.nat () T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun |MultiSet#FromSeq| (T@T T@U) T@U)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |MultiSet#Empty| (T@T) T@U)
(declare-fun |Seq#Contains| (T@T T@U T@U) Bool)
(declare-fun |Seq#Build| (T@T T@U T@U) T@U)
(declare-fun |Map#Glue| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |Map#Elements| (T@T T@T T@U) T@U)
(declare-fun |IMap#Domain| (T@T T@T T@U) T@U)
(declare-fun |IMap#Glue| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |IMap#Elements| (T@T T@T T@U) T@U)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun Tclass._System.object? () T@U)
(declare-fun Tclass._System.array (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0 (T@U) T@U)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#Offset| (T@U) Int)
(declare-fun DatatypeTypeType () T@T)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun _System.Tuple2._1 (T@U) T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun |Seq#Drop| (T@T T@U Int) T@U)
(declare-fun |Seq#Length| (T@T T@U) Int)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun TMultiSet (T@U) T@U)
(declare-fun $IsGoodMultiSet (T@T T@U) Bool)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun |Seq#Index| (T@T T@U Int) T@U)
(declare-fun |Seq#Update| (T@T T@U Int T@U) T@U)
(declare-fun |Set#Union| (T@T T@U T@U) T@U)
(declare-fun |Set#Intersection| (T@T T@U T@U) T@U)
(declare-fun |ISet#Union| (T@T T@U T@U) T@U)
(declare-fun |ISet#Intersection| (T@T T@U T@U) T@U)
(declare-fun |Seq#Take| (T@T T@U Int) T@U)
(declare-fun |Seq#Append| (T@T T@U T@U) T@U)
(declare-fun Tclass._System.object () T@U)
(declare-fun |Map#Card| (T@T T@T T@U) Int)
(declare-fun |Map#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |Set#Singleton| (T@T T@U) T@U)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun Handle0 (T@U T@U T@U) T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun _module.__default.secretPredicate (T@U Int) Bool)
(declare-fun $LS (T@U) T@U)
(declare-fun |_module.__default.secretPredicate#canCall| (Int) Bool)
(declare-fun |Set#Card| (T@T T@U) Int)
(declare-fun |Map#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun IndexField (Int) T@U)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun TSet (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun |Math#clip| (Int) Int)
(declare-fun q@Int (Real) Int)
(declare-fun LitInt (Int) Int)
(declare-fun LitReal (Real) Real)
(declare-fun Lit (T@T T@U) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun TSeq (T@U) T@U)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun $$Language$Dafny () Bool)
(declare-fun $IsAllocBox (T@T T@U T@U T@U) Bool)
(declare-fun |Seq#Equal| (T@T T@U T@U) Bool)
(declare-fun |_module.__default.magicNum#canCall| () Bool)
(declare-fun |Seq#Rank| (T@T T@U) Int)
(declare-fun Requires0 (T@U T@U T@U) Bool)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun |MultiSet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun AtLayer (T@T T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun $IsGhostField (T@T T@U) Bool)
(declare-fun |Seq#Create| (T@U T@U Int T@U) T@U)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun TagFamily (T@U) T@U)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |ISet#Equal| (T@T T@U T@U) Bool)
(declare-fun Tclass._System.___hPartialFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1 (T@U T@U) T@U)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun Handle1 (T@U T@U T@U) T@U)
(declare-fun MapType2Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |Map#Values| (T@T T@T T@U) T@U)
(declare-fun |IMap#Values| (T@T T@T T@U) T@U)
(declare-fun StartFuel__module._default.secretPredicate () T@U)
(declare-fun MoreFuel__module._default.secretPredicate0 () T@U)
(declare-fun StartFuelAssert__module._default.secretPredicate () T@U)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun _module.__default.magicNum () Int)
(declare-fun MoreFuel__module._default.secretPredicate1 () T@U)
(declare-fun |Set#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |Set#Difference| (T@T T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |ISet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Equal| (T@T T@U T@U) Bool)
(declare-fun |MultiSet#Subset| (T@T T@U T@U) Bool)
(declare-fun |_module.__default.secretPredicate#requires| (T@U Int) Bool)
(declare-fun |Map#Items| (T@T T@T T@U) T@U)
(declare-fun |IMap#Items| (T@T T@T T@U) T@U)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun TMap (T@U T@U) T@U)
(declare-fun MapTypeInv0 (T@T) T@T)
(declare-fun MapTypeInv1 (T@T) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun TIMap (T@U T@U) T@U)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-fun |ORD#LessThanLimit| (T@U T@U) Bool)
(declare-fun $LZ () T@U)
(declare-fun |Map#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |IMap#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |Set#UnionOne| (T@T T@U T@U) T@U)
(declare-fun |ISet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun q@Real (Int) Real)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun FieldOfDecl (T@T T@U T@U) T@U)
(declare-fun DeclType (T@T T@U) T@U)
(declare-fun charType () T@T)
(declare-fun |MultiSet#FromSet| (T@T T@U) T@U)
(declare-fun |Seq#Singleton| (T@T T@U) T@U)
(declare-fun |MultiSet#Singleton| (T@T T@U) T@U)
(declare-fun $AlwaysAllocated (T@U) Bool)
(declare-fun Inv0_TMap (T@U) T@U)
(declare-fun Inv1_TMap (T@U) T@U)
(declare-fun Inv0_TIMap (T@U) T@U)
(declare-fun Inv1_TIMap (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun MapType3Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun MapType3Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun IndexField_Inverse (T@T T@U) Int)
(declare-fun Tclass._System.array?_0 (T@U) T@U)
(declare-fun Tclass._System.array_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0_0 (T@U) T@U)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun |Map#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun BoxRank (T@U) Int)
(declare-fun DtRank (T@U) Int)
(declare-fun |IMap#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |MultiSet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun TypeTuple (T@U T@U) T@U)
(declare-fun TypeTupleCar (T@U) T@U)
(declare-fun TypeTupleCdr (T@U) T@U)
(declare-fun MultiIndexField_Inverse0 (T@T T@U) T@U)
(declare-fun MultiIndexField_Inverse1 (T@T T@U) Int)
(declare-fun |Seq#Build_inv0| (T@T T@U) T@U)
(declare-fun |Seq#Build_inv1| (T@T T@U) T@U)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun |Set#Subset| (T@T T@U T@U) Bool)
(declare-fun |ISet#Subset| (T@T T@U T@U) Bool)
(declare-fun |Seq#SameUntil| (T@T T@U T@U Int) Bool)
(declare-fun |_module.__default.magicNum#requires| () Bool)
(assert  (and (and (and (and (and (and (and (and (= (Ctor boolType) 0) (= (Ctor intType) 1)) (= (Ctor realType) 2)) (forall ((arg0 Bool) ) (! (= (U_2_bool (bool_2_U arg0)) arg0)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0))
))) (forall ((x T@U) ) (! (= (bool_2_U (U_2_bool x)) x)
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x))
))) (forall ((arg0@@0 Int) ) (! (= (U_2_int (int_2_U arg0@@0)) arg0@@0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((x@@0 T@U) ) (! (= (int_2_U (U_2_int x@@0)) x@@0)
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@1 T@U) ) (! (= (real_2_U (U_2_real x@@1)) x@@1)
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@1))
))))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 class._System.Tuple2 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._System.Tuple0 class._module.__default tytagFamily$nat tytagFamily$object tytagFamily$array |tytagFamily$_#Func1| |tytagFamily$_#PartialFunc1| |tytagFamily$_#TotalFunc1| |tytagFamily$_#Func0| |tytagFamily$_#PartialFunc0| |tytagFamily$_#TotalFunc0| |tytagFamily$_tuple#2| |tytagFamily$_tuple#0|)
)
(assert  (and (forall ((t0 T@T) (t1 T@T) (val T@U) (m T@U) (x0 T@U) ) (! (= (MapType0Select t0 t1 (MapType0Store t0 t1 m x0 val) x0) val)
 :qid |mapAx0:MapType0Select|
 :weight 0
)) (forall ((u0 T@T) (u1 T@T) (val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select u0 u1 (MapType0Store u0 u1 m@@0 x0@@0 val@@0) y0) (MapType0Select u0 u1 m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
))))
(assert (forall ((m@@1 T@U) (|m'| T@U) (U T@T) (V T@T) ) (! (= (|Map#Disjoint| U V m@@1 |m'|) (forall ((o T@U) ) (!  (or (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V m@@1) o))) (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V |m'|) o))))
 :qid |testbpl.1601:19|
 :skolemid |304|
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V m@@1) o))
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V |m'|) o))
)))
 :qid |testbpl.1598:20|
 :skolemid |305|
 :pattern ( (|Map#Disjoint| U V m@@1 |m'|))
)))
(assert (= (FDim boolType alloc) 0))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (= (DeclName boolType alloc) allocName))
(assert  (and (and (and (and (and (and (= (Ctor HandleTypeType) 3) (= (Ctor BoxType) 4)) (= (Ctor refType) 5)) (forall ((t0@@0 T@T) (t1@@0 T@T) (val@@1 T@U) (m@@2 T@U) (x0@@1 T@U) ) (! (= (MapType1Select t0@@0 t1@@0 (MapType1Store t0@@0 t1@@0 m@@2 x0@@1 val@@1) x0@@1) val@@1)
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((u0@@0 T@T) (s0 T@T) (t0@@1 T@T) (val@@2 T@U) (m@@3 T@U) (x0@@2 T@U) (y0@@0 T@U) ) (!  (or (= s0 t0@@1) (= (MapType1Select t0@@1 u0@@0 (MapType1Store s0 u0@@0 m@@3 x0@@2 val@@2) y0@@0) (MapType1Select t0@@1 u0@@0 m@@3 y0@@0)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((u0@@1 T@T) (s0@@0 T@T) (t0@@2 T@T) (val@@3 T@U) (m@@4 T@U) (x0@@3 T@U) (y0@@1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select t0@@2 u0@@1 (MapType1Store s0@@0 u0@@1 m@@4 x0@@3 val@@3) y0@@1) (MapType1Select t0@@2 u0@@1 m@@4 y0@@1)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
)))) (forall ((arg0@@2 T@T) ) (! (= (Ctor (MapType1Type arg0@@2)) 6)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@3 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@3)) arg0@@3)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@3))
))))
(assert (forall ((t0@@3 T@U) (h0 T@U) (h1 T@U) (f T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0 h1) ($IsGoodHeap h0)) ($IsGoodHeap h1)) ($Is HandleTypeType f (Tclass._System.___hFunc0 t0@@3))) (forall ((o@@0 T@U) (fld T@U) (a T@T) ) (!  (=> (and (or (not (= o@@0 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@3 h0 f) ($Box refType o@@0)))) (= ($Unbox a (MapType1Select a BoxType (MapType0Select refType (MapType1Type BoxType) h0 o@@0) fld)) ($Unbox a (MapType1Select a BoxType (MapType0Select refType (MapType1Type BoxType) h1 o@@0) fld))))
 :qid |testbpl.2388:22|
 :skolemid |420|
))) (= (Reads0 t0@@3 h0 f) (Reads0 t0@@3 h1 f)))
 :qid |testbpl.2381:15|
 :skolemid |421|
 :pattern ( ($HeapSucc h0 h1) (Reads0 t0@@3 h1 f))
)))
(assert (forall ((t0@@4 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@0 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@0 h1@@0) ($IsGoodHeap h0@@0)) ($IsGoodHeap h1@@0)) ($Is HandleTypeType f@@0 (Tclass._System.___hFunc0 t0@@4))) (forall ((o@@1 T@U) (fld@@0 T@U) (a@@0 T@T) ) (!  (=> (and (or (not (= o@@1 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@4 h1@@0 f@@0) ($Box refType o@@1)))) (= ($Unbox a@@0 (MapType1Select a@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@0 o@@1) fld@@0)) ($Unbox a@@0 (MapType1Select a@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@0 o@@1) fld@@0))))
 :qid |testbpl.2401:22|
 :skolemid |422|
))) (= (Reads0 t0@@4 h0@@0 f@@0) (Reads0 t0@@4 h1@@0 f@@0)))
 :qid |testbpl.2394:15|
 :skolemid |423|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads0 t0@@4 h1@@0 f@@0))
)))
(assert (forall ((t0@@5 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@1 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@1 h1@@1) ($IsGoodHeap h0@@1)) ($IsGoodHeap h1@@1)) ($Is HandleTypeType f@@1 (Tclass._System.___hFunc0 t0@@5))) (forall ((o@@2 T@U) (fld@@1 T@U) (a@@1 T@T) ) (!  (=> (and (or (not (= o@@2 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@5 h0@@1 f@@1) ($Box refType o@@2)))) (= ($Unbox a@@1 (MapType1Select a@@1 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@1 o@@2) fld@@1)) ($Unbox a@@1 (MapType1Select a@@1 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@1 o@@2) fld@@1))))
 :qid |testbpl.2440:22|
 :skolemid |428|
))) (= (Apply0 t0@@5 h0@@1 f@@1) (Apply0 t0@@5 h1@@1 f@@1)))
 :qid |testbpl.2433:15|
 :skolemid |429|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Apply0 t0@@5 h1@@1 f@@1))
)))
(assert (forall ((t0@@6 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@2 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@2 h1@@2) ($IsGoodHeap h0@@2)) ($IsGoodHeap h1@@2)) ($Is HandleTypeType f@@2 (Tclass._System.___hFunc0 t0@@6))) (forall ((o@@3 T@U) (fld@@2 T@U) (a@@2 T@T) ) (!  (=> (and (or (not (= o@@3 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@6 h1@@2 f@@2) ($Box refType o@@3)))) (= ($Unbox a@@2 (MapType1Select a@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@2 o@@3) fld@@2)) ($Unbox a@@2 (MapType1Select a@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@2 o@@3) fld@@2))))
 :qid |testbpl.2453:22|
 :skolemid |430|
))) (= (Apply0 t0@@6 h0@@2 f@@2) (Apply0 t0@@6 h1@@2 f@@2)))
 :qid |testbpl.2446:15|
 :skolemid |431|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Apply0 t0@@6 h1@@2 f@@2))
)))
(assert (forall ((t0@@7 T@U) (t1@@1 T@U) (heap T@U) (f@@3 T@U) (bx0 T@U) ) (!  (=> (and (and (and ($IsGoodHeap heap) ($IsBox BoxType bx0 t0@@7)) ($Is HandleTypeType f@@3 (Tclass._System.___hFunc1 t0@@7 t1@@1))) (|Set#Equal| BoxType (Reads1 t0@@7 t1@@1 $OneHeap f@@3 bx0) (|Set#Empty| BoxType))) (= (Requires1 t0@@7 t1@@1 $OneHeap f@@3 bx0) (Requires1 t0@@7 t1@@1 heap f@@3 bx0)))
 :qid |testbpl.2182:15|
 :skolemid |389|
 :pattern ( (Requires1 t0@@7 t1@@1 $OneHeap f@@3 bx0) ($IsGoodHeap heap))
 :pattern ( (Requires1 t0@@7 t1@@1 heap f@@3 bx0))
)))
(assert (forall ((v T@U) (h T@U) ) (! ($IsAlloc intType v (TBitvector 0) h)
 :qid |testbpl.346:15|
 :skolemid |65|
 :pattern ( ($IsAlloc intType v (TBitvector 0) h))
)))
(assert (forall ((_System.array$arg T@U) ($o T@U) ) (!  (=> (and (or (not (= $o null)) (not true)) (= (dtype $o) (Tclass._System.array? _System.array$arg))) ($Is intType (int_2_U (_System.array.Length $o)) TInt))
 :qid |testbpl.1953:15|
 :skolemid |362|
 :pattern ( (_System.array.Length $o) (Tclass._System.array? _System.array$arg))
)))
(assert (forall ((a@@3 T@U) (b T@U) (T T@T) ) (!  (and (= (+ (+ (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)) (|MultiSet#Card| T (|MultiSet#Difference| T b a@@3))) (* 2 (|MultiSet#Card| T (|MultiSet#Intersection| T a@@3 b)))) (|MultiSet#Card| T (|MultiSet#Union| T a@@3 b))) (= (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)) (- (|MultiSet#Card| T a@@3) (|MultiSet#Card| T (|MultiSet#Intersection| T a@@3 b)))))
 :qid |testbpl.1114:18|
 :skolemid |203|
 :pattern ( (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)))
)))
(assert (forall ((h@@0 T@U) (k T@U) ) (!  (=> ($HeapSucc h@@0 k) (forall ((o@@4 T@U) ) (!  (=> (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@0 o@@4) alloc))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@4) alloc))))
 :qid |testbpl.725:18|
 :skolemid |117|
 :pattern ( ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@4) alloc)))
)))
 :qid |testbpl.722:15|
 :skolemid |118|
 :pattern ( ($HeapSucc h@@0 k))
)))
(assert (forall ((o@@5 T@U) (p T@U) (r T@U) ) (!  (=> (and (|ORD#Less| o@@5 p) (|ORD#Less| p r)) (|ORD#Less| o@@5 r))
 :qid |testbpl.500:15|
 :skolemid |89|
 :pattern ( (|ORD#Less| o@@5 p) (|ORD#Less| p r))
 :pattern ( (|ORD#Less| o@@5 p) (|ORD#Less| o@@5 r))
)))
(assert (forall ((|x#0| T@U) ($h T@U) ) (! ($IsAlloc intType |x#0| Tclass._System.nat $h)
 :qid |testbpl.1834:15|
 :skolemid |348|
 :pattern ( ($IsAlloc intType |x#0| Tclass._System.nat $h))
)))
(assert (forall ((d T@U) ) (!  (=> (|$IsA#_System.Tuple2| d) (_System.Tuple2.___hMake2_q d))
 :qid |testbpl.2711:15|
 :skolemid |470|
 :pattern ( (|$IsA#_System.Tuple2| d))
)))
(assert (forall ((d@@0 T@U) ) (!  (=> (|$IsA#_System.Tuple0| d@@0) (_System.Tuple0.___hMake0_q d@@0))
 :qid |testbpl.2795:15|
 :skolemid |478|
 :pattern ( (|$IsA#_System.Tuple0| d@@0))
)))
(assert (forall ((T@@0 T@T) ) (! (= (|MultiSet#FromSeq| T@@0 (|Seq#Empty| T@@0)) (|MultiSet#Empty| T@@0))
 :skolemid |213|
)))
(assert (forall ((_System.array$arg@@0 T@U) ($o@@0 T@U) ($h@@0 T@U) ) (! (= ($IsAlloc refType $o@@0 (Tclass._System.array? _System.array$arg@@0) $h@@0)  (or (= $o@@0 null) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@0 $o@@0) alloc)))))
 :qid |testbpl.1947:15|
 :skolemid |361|
 :pattern ( ($IsAlloc refType $o@@0 (Tclass._System.array? _System.array$arg@@0) $h@@0))
)))
(assert (forall ((s T@U) (v@@0 T@U) (x@@2 T@U) (T@@1 T@T) ) (! (= (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2)  (or (= v@@0 x@@2) (|Seq#Contains| T@@1 s x@@2)))
 :qid |testbpl.1300:18|
 :skolemid |240|
 :pattern ( (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2))
)))
(assert (forall ((a@@4 T@U) (b@@0 T@U) (t T@U) (U@@0 T@T) (V@@0 T@T) ) (! (= (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@4 b@@0 t)) a@@4)
 :qid |testbpl.1530:20|
 :skolemid |289|
 :pattern ( (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@4 b@@0 t)))
)))
(assert (forall ((a@@5 T@U) (b@@1 T@U) (t@@0 T@U) (U@@1 T@T) (V@@1 T@T) ) (! (= (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@5 b@@1 t@@0)) b@@1)
 :qid |testbpl.1534:20|
 :skolemid |290|
 :pattern ( (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@5 b@@1 t@@0)))
)))
(assert (forall ((a@@6 T@U) (b@@2 T@U) (t@@1 T@U) (U@@2 T@T) (V@@2 T@T) ) (! (= (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@6 b@@2 t@@1)) a@@6)
 :qid |testbpl.1662:20|
 :skolemid |319|
 :pattern ( (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@6 b@@2 t@@1)))
)))
(assert (forall ((a@@7 T@U) (b@@3 T@U) (t@@2 T@U) (U@@3 T@T) (V@@3 T@T) ) (! (= (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@7 b@@3 t@@2)) b@@3)
 :qid |testbpl.1666:20|
 :skolemid |320|
 :pattern ( (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@7 b@@3 t@@2)))
)))
(assert (forall ((v@@1 T@U) ) (! ($Is intType v@@1 (TBitvector 0))
 :qid |testbpl.278:15|
 :skolemid |44|
 :pattern ( ($Is intType v@@1 (TBitvector 0)))
)))
(assert (forall ((a@@8 Int) (b@@4 Int) ) (!  (or (= (|Math#min| a@@8 b@@4) a@@8) (= (|Math#min| a@@8 b@@4) b@@4))
 :qid |testbpl.1009:15|
 :skolemid |179|
 :pattern ( (|Math#min| a@@8 b@@4))
)))
(assert (forall (($o@@1 T@U) ($h@@1 T@U) ) (! (= ($IsAlloc refType $o@@1 Tclass._System.object? $h@@1)  (or (= $o@@1 null) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@1 $o@@1) alloc)))))
 :qid |testbpl.1854:15|
 :skolemid |351|
 :pattern ( ($IsAlloc refType $o@@1 Tclass._System.object? $h@@1))
)))
(assert (forall ((_System.array$arg@@1 T@U) (|c#0| T@U) ($h@@2 T@U) ) (! (= ($IsAlloc refType |c#0| (Tclass._System.array _System.array$arg@@1) $h@@2) ($IsAlloc refType |c#0| (Tclass._System.array? _System.array$arg@@1) $h@@2))
 :qid |testbpl.2000:15|
 :skolemid |368|
 :pattern ( ($IsAlloc refType |c#0| (Tclass._System.array _System.array$arg@@1) $h@@2))
)))
(assert (forall ((|#$R| T@U) (|f#0| T@U) ($h@@3 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hPartialFunc0 |#$R|) $h@@3) ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hFunc0 |#$R|) $h@@3))
 :qid |testbpl.2536:15|
 :skolemid |445|
 :pattern ( ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hPartialFunc0 |#$R|) $h@@3))
)))
(assert (forall ((|#$R@@0| T@U) (|f#0@@0| T@U) ($h@@4 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hTotalFunc0 |#$R@@0|) $h@@4) ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hPartialFunc0 |#$R@@0|) $h@@4))
 :qid |testbpl.2572:15|
 :skolemid |450|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hTotalFunc0 |#$R@@0|) $h@@4))
)))
(assert (forall ((o@@6 T@U) (m@@5 Int) (n Int) ) (!  (=> (and (and (<= 0 m@@5) (<= 0 n)) (<= (+ m@@5 n) (|ORD#Offset| o@@6))) (= (|ORD#Minus| (|ORD#Minus| o@@6 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)) (|ORD#Minus| o@@6 (|ORD#FromNat| (+ m@@5 n)))))
 :qid |testbpl.549:15|
 :skolemid |97|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@6 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)))
)))
(assert (= (Ctor DatatypeTypeType) 7))
(assert (forall ((|_System._tuple#2$T0| T@U) (|_System._tuple#2$T1| T@U) (d@@1 T@U) ) (!  (=> ($Is DatatypeTypeType d@@1 (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)) (_System.Tuple2.___hMake2_q d@@1))
 :qid |testbpl.2716:15|
 :skolemid |471|
 :pattern ( (_System.Tuple2.___hMake2_q d@@1) ($Is DatatypeTypeType d@@1 (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)))
)))
(assert (forall ((a@@9 T@U) (b@@5 T@U) ) (!  (=> true (= (|_System.Tuple2#Equal| a@@9 b@@5)  (and (= (_System.Tuple2._0 a@@9) (_System.Tuple2._0 b@@5)) (= (_System.Tuple2._1 a@@9) (_System.Tuple2._1 b@@5)))))
 :qid |testbpl.2725:15|
 :skolemid |472|
 :pattern ( (|_System.Tuple2#Equal| a@@9 b@@5))
)))
(assert (forall ((x@@3 T@U) (T@@2 T@T) ) (!  (not (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
 :qid |testbpl.1291:18|
 :skolemid |238|
 :pattern ( (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
)))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((s@@0 T@U) (v@@2 T@U) (n@@0 Int) (T@@3 T@T) ) (!  (=> (and (<= 0 n@@0) (<= n@@0 (|Seq#Length| T@@3 s@@0))) (= (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0) (|Seq#Build| T@@3 (|Seq#Drop| T@@3 s@@0 n@@0) v@@2)))
 :qid |testbpl.1421:18|
 :skolemid |266|
 :pattern ( (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0))
)))
(assert  (and (and (forall ((arg0@@4 T@T) (arg1 T@T) ) (! (= (Ctor (MapType0Type arg0@@4 arg1)) 8)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@5 T@T) (arg1@@0 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@5 arg1@@0)) arg0@@5)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@5 arg1@@0))
))) (forall ((arg0@@6 T@T) (arg1@@1 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@6 arg1@@1)) arg1@@1)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@6 arg1@@1))
))))
(assert (forall ((v@@3 T@U) (t0@@8 T@U) ) (!  (=> ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@8)) ($IsGoodMultiSet BoxType v@@3))
 :qid |testbpl.293:15|
 :skolemid |51|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@8)))
)))
(assert (forall ((s@@1 T@U) (T@@4 T@T) ) (! ($IsGoodMultiSet T@@4 (|MultiSet#FromSeq| T@@4 s@@1))
 :qid |testbpl.1163:18|
 :skolemid |214|
 :pattern ( (|MultiSet#FromSeq| T@@4 s@@1))
)))
(assert (forall ((s@@2 T@U) (i Int) (v@@4 T@U) (n@@1 Int) (T@@5 T@T) ) (!  (=> (and (<= 0 n@@1) (< n@@1 (|Seq#Length| T@@5 s@@2))) (and (=> (= i n@@1) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) v@@4)) (=> (or (not (= i n@@1)) (not true)) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) (|Seq#Index| T@@5 s@@2 n@@1)))))
 :qid |testbpl.1276:18|
 :skolemid |235|
 :pattern ( (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1))
)))
(assert (forall ((a@@10 T@U) (b@@6 T@U) (T@@6 T@T) ) (! (= (|Set#Union| T@@6 (|Set#Union| T@@6 a@@10 b@@6) b@@6) (|Set#Union| T@@6 a@@10 b@@6))
 :qid |testbpl.852:18|
 :skolemid |140|
 :pattern ( (|Set#Union| T@@6 (|Set#Union| T@@6 a@@10 b@@6) b@@6))
)))
(assert (forall ((a@@11 T@U) (b@@7 T@U) (T@@7 T@T) ) (! (= (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@11 b@@7) b@@7) (|Set#Intersection| T@@7 a@@11 b@@7))
 :qid |testbpl.860:18|
 :skolemid |142|
 :pattern ( (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@11 b@@7) b@@7))
)))
(assert (forall ((a@@12 T@U) (b@@8 T@U) (T@@8 T@T) ) (! (= (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@12 b@@8) b@@8) (|ISet#Union| T@@8 a@@12 b@@8))
 :qid |testbpl.955:18|
 :skolemid |164|
 :pattern ( (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@12 b@@8) b@@8))
)))
(assert (forall ((a@@13 T@U) (b@@9 T@U) (T@@9 T@T) ) (! (= (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@13 b@@9) b@@9) (|ISet#Intersection| T@@9 a@@13 b@@9))
 :qid |testbpl.963:18|
 :skolemid |166|
 :pattern ( (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@13 b@@9) b@@9))
)))
(assert (forall ((a@@14 T@U) (b@@10 T@U) (T@@10 T@T) ) (! (= (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@14 b@@10) b@@10) (|MultiSet#Intersection| T@@10 a@@14 b@@10))
 :qid |testbpl.1094:18|
 :skolemid |199|
 :pattern ( (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@14 b@@10) b@@10))
)))
(assert (forall ((f@@4 T@U) (t0@@9 T@U) (t1@@2 T@U) (u0@@2 T@U) (u1@@0 T@U) ) (!  (=> (and (and ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 t0@@9 t1@@2)) (forall ((bx T@U) ) (!  (=> ($IsBox BoxType bx u0@@2) ($IsBox BoxType bx t0@@9))
 :qid |testbpl.2203:19|
 :skolemid |392|
 :pattern ( ($IsBox BoxType bx u0@@2))
 :pattern ( ($IsBox BoxType bx t0@@9))
))) (forall ((bx@@0 T@U) ) (!  (=> ($IsBox BoxType bx@@0 t1@@2) ($IsBox BoxType bx@@0 u1@@0))
 :qid |testbpl.2206:19|
 :skolemid |393|
 :pattern ( ($IsBox BoxType bx@@0 t1@@2))
 :pattern ( ($IsBox BoxType bx@@0 u1@@0))
))) ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 u0@@2 u1@@0)))
 :qid |testbpl.2200:15|
 :skolemid |394|
 :pattern ( ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 t0@@9 t1@@2)) ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 u0@@2 u1@@0)))
)))
(assert (forall ((s@@3 T@U) (t@@3 T@U) (n@@2 Int) (T@@11 T@T) ) (!  (=> (= n@@2 (|Seq#Length| T@@11 s@@3)) (and (= (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) s@@3) (= (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) t@@3)))
 :qid |testbpl.1366:18|
 :skolemid |255|
 :pattern ( (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
 :pattern ( (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@5 T@U) ) (! (= ($IsAlloc refType |c#0@@0| Tclass._System.object $h@@5) ($IsAlloc refType |c#0@@0| Tclass._System.object? $h@@5))
 :qid |testbpl.1883:15|
 :skolemid |354|
 :pattern ( ($IsAlloc refType |c#0@@0| Tclass._System.object $h@@5))
)))
(assert (forall ((m@@6 T@U) (u T@U) (v@@5 T@U) (U@@4 T@T) (V@@4 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@4 boolType (|Map#Domain| U@@4 V@@4 m@@6) u)) (= (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)) (|Map#Card| U@@4 V@@4 m@@6)))
 :qid |testbpl.1553:20|
 :skolemid |294|
 :pattern ( (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)))
)))
(assert (forall ((r@@0 T@U) (o@@7 T@U) (T@@12 T@T) ) (! (= (U_2_bool (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@7)) (= r@@0 o@@7))
 :qid |testbpl.798:18|
 :skolemid |128|
 :pattern ( (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@7))
)))
(assert (forall ((d@@2 T@U) ) (!  (=> ($Is DatatypeTypeType d@@2 Tclass._System.Tuple0) (_System.Tuple0.___hMake0_q d@@2))
 :qid |testbpl.2800:15|
 :skolemid |479|
 :pattern ( (_System.Tuple0.___hMake0_q d@@2) ($Is DatatypeTypeType d@@2 Tclass._System.Tuple0))
)))
(assert (forall ((s@@4 T@U) (x@@4 T@U) (T@@13 T@T) ) (! (= (exists ((i@@0 Int) ) (!  (and (and (<= 0 i@@0) (< i@@0 (|Seq#Length| T@@13 s@@4))) (= x@@4 (|Seq#Index| T@@13 s@@4 i@@0)))
 :qid |testbpl.1189:11|
 :skolemid |219|
 :pattern ( (|Seq#Index| T@@13 s@@4 i@@0))
)) (< 0 (U_2_int (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))))
 :qid |testbpl.1187:18|
 :skolemid |220|
 :pattern ( (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))
)))
(assert (forall ((|_System._tuple#2$T0@@0| T@U) (|_System._tuple#2$T1@@0| T@U) (|a#2#0#0| T@U) (|a#2#1#0| T@U) ) (! (= ($Is DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|))  (and ($IsBox BoxType |a#2#0#0| |_System._tuple#2$T0@@0|) ($IsBox BoxType |a#2#1#0| |_System._tuple#2$T1@@0|)))
 :qid |testbpl.2636:15|
 :skolemid |459|
 :pattern ( ($Is DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|)))
)))
(assert ($Is DatatypeTypeType |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall ((t0@@10 T@U) (heap@@0 T@U) (h@@1 T@U) (r@@1 T@U) (rd T@U) ) (! (= (Apply0 t0@@10 heap@@0 (Handle0 h@@1 r@@1 rd)) (MapType0Select (MapType0Type refType (MapType1Type BoxType)) BoxType h@@1 heap@@0))
 :qid |testbpl.2358:15|
 :skolemid |417|
 :pattern ( (Apply0 t0@@10 heap@@0 (Handle0 h@@1 r@@1 rd)))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly T@U) (|q#0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0|) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly) |q#0|) (> |q#0| 1234)))
 :qid |testbpl.2838:16|
 :skolemid |483|
 :pattern ( (_module.__default.secretPredicate ($LS $ly) |q#0|))
))))
(assert (forall ((a@@15 T@U) (b@@11 T@U) (T@@14 T@T) ) (! (= (+ (|Set#Card| T@@14 (|Set#Union| T@@14 a@@15 b@@11)) (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@15 b@@11))) (+ (|Set#Card| T@@14 a@@15) (|Set#Card| T@@14 b@@11)))
 :qid |testbpl.868:18|
 :skolemid |144|
 :pattern ( (|Set#Card| T@@14 (|Set#Union| T@@14 a@@15 b@@11)))
 :pattern ( (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@15 b@@11)))
)))
(assert (forall ((m@@7 T@U) (s@@5 T@U) (u@@0 T@U) (U@@5 T@T) (V@@5 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@5 boolType (|Map#Domain| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0)) (= (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0) (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 m@@7) u@@0)))
 :qid |testbpl.1579:20|
 :skolemid |299|
 :pattern ( (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0))
)))
(assert (forall ((m@@8 T@U) (s@@6 T@U) (u@@1 T@U) (U@@6 T@T) (V@@6 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@6 boolType (|IMap#Domain| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1)) (= (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1) (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 m@@8) u@@1)))
 :qid |testbpl.1720:20|
 :skolemid |331|
 :pattern ( (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1))
)))
(assert (forall ((h@@2 T@U) (a@@16 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@16))) (= (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n1) (|Seq#Build| BoxType (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n0) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@2 a@@16) (IndexField n0))))))
 :qid |testbpl.1415:15|
 :skolemid |265|
 :pattern ( (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n0) (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n1))
)))
(assert (forall ((s@@7 T@U) (i@@1 Int) (v@@6 T@U) (n@@3 Int) (T@@15 T@T) ) (!  (=> (and (and (<= 0 n@@3) (<= n@@3 i@@1)) (< i@@1 (|Seq#Length| T@@15 s@@7))) (= (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3) (|Seq#Update| T@@15 (|Seq#Drop| T@@15 s@@7 n@@3) (- i@@1 n@@3) v@@6)))
 :qid |testbpl.1405:18|
 :skolemid |263|
 :pattern ( (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) (o@@8 T@U) (T@@16 T@T) ) (! (= (U_2_int (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@17 b@@12) o@@8)) (+ (U_2_int (MapType0Select T@@16 intType a@@17 o@@8)) (U_2_int (MapType0Select T@@16 intType b@@12 o@@8))))
 :qid |testbpl.1080:18|
 :skolemid |196|
 :pattern ( (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@17 b@@12) o@@8))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) ) (! (= (|_System.Tuple2#Equal| a@@18 b@@13) (= a@@18 b@@13))
 :qid |testbpl.2733:15|
 :skolemid |473|
 :pattern ( (|_System.Tuple2#Equal| a@@18 b@@13))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) ) (! (= (|_System.Tuple0#Equal| a@@19 b@@14) (= a@@19 b@@14))
 :qid |testbpl.2813:15|
 :skolemid |481|
 :pattern ( (|_System.Tuple0#Equal| a@@19 b@@14))
)))
(assert (forall ((s@@8 T@U) (n@@4 Int) (T@@17 T@T) ) (!  (=> (= n@@4 0) (= (|Seq#Drop| T@@17 s@@8 n@@4) s@@8))
 :qid |testbpl.1446:18|
 :skolemid |271|
 :pattern ( (|Seq#Drop| T@@17 s@@8 n@@4))
)))
(assert (forall ((v@@7 T@U) (t0@@11 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@11)) (forall ((bx@@1 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@7 bx@@1)) ($IsBox BoxType bx@@1 t0@@11))
 :qid |testbpl.282:33|
 :skolemid |45|
 :pattern ( (MapType0Select BoxType boolType v@@7 bx@@1))
)))
 :qid |testbpl.280:15|
 :skolemid |46|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@11)))
)))
(assert (forall ((v@@8 T@U) (t0@@12 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@12)) (forall ((bx@@2 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@8 bx@@2)) ($IsBox BoxType bx@@2 t0@@12))
 :qid |testbpl.286:34|
 :skolemid |47|
 :pattern ( (MapType0Select BoxType boolType v@@8 bx@@2))
)))
 :qid |testbpl.284:15|
 :skolemid |48|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@12)))
)))
(assert (forall ((a@@20 Int) ) (!  (=> (<= 0 a@@20) (= (|Math#clip| a@@20) a@@20))
 :qid |testbpl.1015:15|
 :skolemid |180|
 :pattern ( (|Math#clip| a@@20))
)))
(assert (forall ((x@@5 Real) ) (! (= (q@Int x@@5) (to_int x@@5))
 :qid |testbpl.674:15|
 :skolemid |112|
 :pattern ( (q@Int x@@5))
)))
(assert (forall ((x@@6 Int) ) (! (= (LitInt x@@6) x@@6)
 :qid |testbpl.141:15|
 :skolemid |17|
 :pattern ( (LitInt x@@6))
)))
(assert (forall ((x@@7 Real) ) (! (= (LitReal x@@7) x@@7)
 :qid |testbpl.148:15|
 :skolemid |19|
 :pattern ( (LitReal x@@7))
)))
(assert (forall ((x@@8 T@U) (T@@18 T@T) ) (! (= (Lit T@@18 x@@8) x@@8)
 :qid |testbpl.134:18|
 :skolemid |15|
 :pattern ( (Lit T@@18 x@@8))
)))
(assert  (and (forall ((arg0@@7 T@T) ) (! (= (Ctor (SeqType arg0@@7)) 9)
 :qid |ctor:SeqType|
)) (forall ((arg0@@8 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@8)) arg0@@8)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@8))
))))
(assert (forall ((s@@9 T@U) (bx@@3 T@U) (t@@4 T@U) ) (!  (=> (and ($Is (SeqType BoxType) s@@9 (TSeq t@@4)) ($IsBox BoxType bx@@3 t@@4)) ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@3) (TSeq t@@4)))
 :qid |testbpl.1235:15|
 :skolemid |228|
 :pattern ( ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@3) (TSeq t@@4)))
)))
(assert $$Language$Dafny)
(assert (forall ((s@@10 T@U) (n@@5 Int) (j Int) (T@@19 T@T) ) (!  (=> (and (and (<= 0 j) (< j n@@5)) (< j (|Seq#Length| T@@19 s@@10))) (= (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j) (|Seq#Index| T@@19 s@@10 j)))
 :qid |testbpl.1345:18|
 :weight 25
 :skolemid |251|
 :pattern ( (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j))
 :pattern ( (|Seq#Index| T@@19 s@@10 j) (|Seq#Take| T@@19 s@@10 n@@5))
)))
(assert (forall ((|_System._tuple#2$T0@@1| T@U) (|_System._tuple#2$T1@@1| T@U) (|a#2#0#0@@0| T@U) (|a#2#1#0@@0| T@U) ($h@@6 T@U) ) (!  (=> ($IsGoodHeap $h@@6) (= ($IsAlloc DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0@@0| |a#2#1#0@@0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|) $h@@6)  (and ($IsAllocBox BoxType |a#2#0#0@@0| |_System._tuple#2$T0@@1| $h@@6) ($IsAllocBox BoxType |a#2#1#0@@0| |_System._tuple#2$T1@@1| $h@@6))))
 :qid |testbpl.2644:15|
 :skolemid |460|
 :pattern ( ($IsAlloc DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0@@0| |a#2#1#0@@0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|) $h@@6))
)))
(assert (forall ((s@@11 T@U) (n@@6 Int) (T@@20 T@T) ) (!  (=> (and (<= 0 n@@6) (<= n@@6 (|Seq#Length| T@@20 s@@11))) (= (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)) (- (|Seq#Length| T@@20 s@@11) n@@6)))
 :qid |testbpl.1352:18|
 :skolemid |252|
 :pattern ( (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)))
)))
(assert (forall ((m@@9 T@U) (u@@2 T@U) (v@@9 T@U) (U@@7 T@T) (V@@7 T@T) ) (!  (=> (not (U_2_bool (MapType0Select U@@7 boolType (|Map#Domain| U@@7 V@@7 m@@9) u@@2))) (= (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)) (+ (|Map#Card| U@@7 V@@7 m@@9) 1)))
 :qid |testbpl.1557:20|
 :skolemid |295|
 :pattern ( (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)))
)))
(assert (forall ((d@@3 T@U) ) (! (= (_System.Tuple2.___hMake2_q d@@3) (= (DatatypeCtorId d@@3) |##_System._tuple#2._#Make2|))
 :qid |testbpl.2589:15|
 :skolemid |452|
 :pattern ( (_System.Tuple2.___hMake2_q d@@3))
)))
(assert (forall ((d@@4 T@U) ) (! (= (_System.Tuple0.___hMake0_q d@@4) (= (DatatypeCtorId d@@4) |##_System._tuple#0._#Make0|))
 :qid |testbpl.2759:15|
 :skolemid |474|
 :pattern ( (_System.Tuple0.___hMake0_q d@@4))
)))
(assert (forall ((s0@@1 T@U) (s1 T@U) (T@@21 T@T) ) (! (= (|Seq#Equal| T@@21 s0@@1 s1)  (and (= (|Seq#Length| T@@21 s0@@1) (|Seq#Length| T@@21 s1)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| T@@21 s0@@1))) (= (|Seq#Index| T@@21 s0@@1 j@@0) (|Seq#Index| T@@21 s1 j@@0)))
 :qid |testbpl.1324:19|
 :skolemid |245|
 :pattern ( (|Seq#Index| T@@21 s0@@1 j@@0))
 :pattern ( (|Seq#Index| T@@21 s1 j@@0))
))))
 :qid |testbpl.1320:18|
 :skolemid |246|
 :pattern ( (|Seq#Equal| T@@21 s0@@1 s1))
)))
(assert (forall ((a@@21 T@U) (b@@15 T@U) (o@@9 T@U) (T@@22 T@T) ) (! (= (U_2_int (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@21 b@@15) o@@9)) (|Math#clip| (- (U_2_int (MapType0Select T@@22 intType a@@21 o@@9)) (U_2_int (MapType0Select T@@22 intType b@@15 o@@9)))))
 :qid |testbpl.1106:18|
 :skolemid |201|
 :pattern ( (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@21 b@@15) o@@9))
)))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) true)))
(assert (forall ((s@@12 T@U) (i@@2 Int) (T@@23 T@T) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| T@@23 s@@12))) (< (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)) (|Seq#Rank| T@@23 s@@12)))
 :qid |testbpl.1437:18|
 :skolemid |269|
 :pattern ( (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)))
)))
(assert (forall ((t0@@13 T@U) (heap@@1 T@U) (f@@5 T@U) ) (!  (=> (and (and ($IsGoodHeap heap@@1) ($Is HandleTypeType f@@5 (Tclass._System.___hFunc0 t0@@13))) (|Set#Equal| BoxType (Reads0 t0@@13 $OneHeap f@@5) (|Set#Empty| BoxType))) (= (Requires0 t0@@13 $OneHeap f@@5) (Requires0 t0@@13 heap@@1 f@@5)))
 :qid |testbpl.2466:15|
 :skolemid |433|
 :pattern ( (Requires0 t0@@13 $OneHeap f@@5) ($IsGoodHeap heap@@1))
 :pattern ( (Requires0 t0@@13 heap@@1 f@@5))
)))
(assert (forall ((d@@5 T@U) ) (!  (=> (_System.Tuple2.___hMake2_q d@@5) (exists ((|a#1#0#0| T@U) (|a#1#1#0| T@U) ) (! (= d@@5 (|#_System._tuple#2._#Make2| |a#1#0#0| |a#1#1#0|))
 :qid |testbpl.2598:18|
 :skolemid |453|
)))
 :qid |testbpl.2595:15|
 :skolemid |454|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5))
)))
(assert (forall ((T@@24 T@T) ) (! (= (|Seq#Length| T@@24 (|Seq#Empty| T@@24)) 0)
 :skolemid |222|
 :pattern ( (|Seq#Empty| T@@24))
)))
(assert (forall ((s@@13 T@U) (bx@@4 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@4)) (U_2_bool (MapType0Select refType boolType s@@13 ($Unbox refType bx@@4))))
 :qid |testbpl.436:15|
 :skolemid |81|
 :pattern ( (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@4))
)))
(assert (forall ((d@@6 T@U) ) (!  (=> (_System.Tuple0.___hMake0_q d@@6) (= d@@6 |#_System._tuple#0._#Make0|))
 :qid |testbpl.2765:15|
 :skolemid |475|
 :pattern ( (_System.Tuple0.___hMake0_q d@@6))
)))
(assert (forall ((f@@6 T@U) (i@@3 Int) ) (! (= (FDim BoxType (MultiIndexField f@@6 i@@3)) (+ (FDim BoxType f@@6) 1))
 :qid |testbpl.614:15|
 :skolemid |104|
 :pattern ( (MultiIndexField f@@6 i@@3))
)))
(assert (forall ((a@@22 T@U) (x@@9 T@U) (T@@25 T@T) ) (! (= (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@22 x@@9)) (+ (|MultiSet#Card| T@@25 a@@22) 1))
 :qid |testbpl.1074:18|
 :skolemid |195|
 :pattern ( (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@22 x@@9)))
)))
(assert (forall ((s@@14 T@U) (i@@4 Int) (T@@26 T@T) ) (!  (=> (and (< 0 i@@4) (<= i@@4 (|Seq#Length| T@@26 s@@14))) (< (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)) (|Seq#Rank| T@@26 s@@14)))
 :qid |testbpl.1433:18|
 :skolemid |268|
 :pattern ( (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)))
)))
(assert (= (Ctor LayerTypeType) 10))
(assert (forall ((f@@7 T@U) (ly T@U) (A T@T) ) (! (= (AtLayer A f@@7 ly) (MapType0Select LayerTypeType A f@@7 ly))
 :qid |testbpl.589:18|
 :skolemid |100|
 :pattern ( (AtLayer A f@@7 ly))
)))
(assert (forall ((|x#0@@0| T@U) ) (! (= ($Is intType |x#0@@0| Tclass._System.nat) (<= (LitInt 0) (U_2_int |x#0@@0|)))
 :qid |testbpl.1829:15|
 :skolemid |347|
 :pattern ( ($Is intType |x#0@@0| Tclass._System.nat))
)))
(assert ($IsGhostField boolType alloc))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((s@@15 T@U) (v@@10 T@U) (T@@27 T@T) ) (! (= (|Seq#Length| T@@27 (|Seq#Build| T@@27 s@@15 v@@10)) (+ 1 (|Seq#Length| T@@27 s@@15)))
 :qid |testbpl.1226:18|
 :skolemid |226|
 :pattern ( (|Seq#Build| T@@27 s@@15 v@@10))
)))
(assert (forall ((ty T@U) (heap@@2 T@U) (len Int) (init T@U) (i@@5 Int) ) (!  (=> (and (and ($IsGoodHeap heap@@2) (<= 0 i@@5)) (< i@@5 len)) (= (|Seq#Index| BoxType (|Seq#Create| ty heap@@2 len init) i@@5) (Apply1 TInt ty heap@@2 init ($Box intType (int_2_U i@@5)))))
 :qid |testbpl.1246:15|
 :skolemid |230|
 :pattern ( (|Seq#Index| BoxType (|Seq#Create| ty heap@@2 len init) i@@5))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@0 T@U) (|q#0@@0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| (LitInt |q#0@@0|)) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)) (U_2_bool (Lit boolType (bool_2_U (> |q#0@@0| 1234))))))
 :qid |testbpl.2844:16|
 :weight 3
 :skolemid |484|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)))
))))
(assert (forall ((_System.array$arg@@2 T@U) (|c#0@@1| T@U) ) (! (= ($Is refType |c#0@@1| (Tclass._System.array _System.array$arg@@2))  (and ($Is refType |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (or (not (= |c#0@@1| null)) (not true))))
 :qid |testbpl.1994:15|
 :skolemid |367|
 :pattern ( ($Is refType |c#0@@1| (Tclass._System.array _System.array$arg@@2)))
)))
(assert (forall ((v@@11 T@U) (t@@5 T@U) (h@@3 T@U) (T@@28 T@T) ) (! (= ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@3) ($IsAlloc T@@28 v@@11 t@@5 h@@3))
 :qid |testbpl.262:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@3))
)))
(assert (forall ((h@@4 T@U) (k@@0 T@U) (bx@@5 T@U) (t@@6 T@U) ) (!  (=> ($HeapSucc h@@4 k@@0) (=> ($IsAllocBox BoxType bx@@5 t@@6 h@@4) ($IsAllocBox BoxType bx@@5 t@@6 k@@0)))
 :qid |testbpl.660:15|
 :skolemid |110|
 :pattern ( ($HeapSucc h@@4 k@@0) ($IsAllocBox BoxType bx@@5 t@@6 h@@4))
)))
(assert (forall ((h@@5 T@U) (k@@1 T@U) (v@@12 T@U) (t@@7 T@U) (T@@29 T@T) ) (!  (=> ($HeapSucc h@@5 k@@1) (=> ($IsAlloc T@@29 v@@12 t@@7 h@@5) ($IsAlloc T@@29 v@@12 t@@7 k@@1)))
 :qid |testbpl.656:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@5 k@@1) ($IsAlloc T@@29 v@@12 t@@7 h@@5))
)))
(assert (forall ((d@@7 T@U) (|_System._tuple#2$T0@@2| T@U) ($h@@7 T@U) ) (!  (=> (and (and ($IsGoodHeap $h@@7) (_System.Tuple2.___hMake2_q d@@7)) (exists ((|_System._tuple#2$T1@@2| T@U) ) (! ($IsAlloc DatatypeTypeType d@@7 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|) $h@@7)
 :qid |testbpl.2665:19|
 :skolemid |461|
 :pattern ( ($IsAlloc DatatypeTypeType d@@7 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|) $h@@7))
))) ($IsAllocBox BoxType (_System.Tuple2._0 d@@7) |_System._tuple#2$T0@@2| $h@@7))
 :qid |testbpl.2660:15|
 :skolemid |462|
 :pattern ( ($IsAllocBox BoxType (_System.Tuple2._0 d@@7) |_System._tuple#2$T0@@2| $h@@7))
)))
(assert (forall ((d@@8 T@U) (|_System._tuple#2$T1@@3| T@U) ($h@@8 T@U) ) (!  (=> (and (and ($IsGoodHeap $h@@8) (_System.Tuple2.___hMake2_q d@@8)) (exists ((|_System._tuple#2$T0@@3| T@U) ) (! ($IsAlloc DatatypeTypeType d@@8 (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|) $h@@8)
 :qid |testbpl.2676:19|
 :skolemid |463|
 :pattern ( ($IsAlloc DatatypeTypeType d@@8 (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|) $h@@8))
))) ($IsAllocBox BoxType (_System.Tuple2._1 d@@8) |_System._tuple#2$T1@@3| $h@@8))
 :qid |testbpl.2671:15|
 :skolemid |464|
 :pattern ( ($IsAllocBox BoxType (_System.Tuple2._1 d@@8) |_System._tuple#2$T1@@3| $h@@8))
)))
(assert (forall ((s@@16 T@U) (n@@7 Int) (j@@1 Int) (T@@30 T@T) ) (!  (=> (and (and (<= 0 n@@7) (<= 0 j@@1)) (< j@@1 (- (|Seq#Length| T@@30 s@@16) n@@7))) (= (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1) (|Seq#Index| T@@30 s@@16 (+ j@@1 n@@7))))
 :qid |testbpl.1356:18|
 :weight 25
 :skolemid |253|
 :pattern ( (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1))
)))
(assert (forall ((s@@17 T@U) (T@@31 T@T) ) (!  (and (= (= (|MultiSet#Card| T@@31 s@@17) 0) (= s@@17 (|MultiSet#Empty| T@@31))) (=> (or (not (= (|MultiSet#Card| T@@31 s@@17) 0)) (not true)) (exists ((x@@10 T@U) ) (! (< 0 (U_2_int (MapType0Select T@@31 intType s@@17 x@@10)))
 :qid |testbpl.1043:44|
 :skolemid |187|
))))
 :qid |testbpl.1040:18|
 :skolemid |188|
 :pattern ( (|MultiSet#Card| T@@31 s@@17))
)))
(assert (forall ((_System.array$arg@@3 T@U) ) (!  (and (= (Tag (Tclass._System.array? _System.array$arg@@3)) Tagclass._System.array?) (= (TagFamily (Tclass._System.array? _System.array$arg@@3)) tytagFamily$array))
 :qid |testbpl.1895:15|
 :skolemid |355|
 :pattern ( (Tclass._System.array? _System.array$arg@@3))
)))
(assert (forall ((_System.array$arg@@4 T@U) ) (!  (and (= (Tag (Tclass._System.array _System.array$arg@@4)) Tagclass._System.array) (= (TagFamily (Tclass._System.array _System.array$arg@@4)) tytagFamily$array))
 :qid |testbpl.1973:15|
 :skolemid |364|
 :pattern ( (Tclass._System.array _System.array$arg@@4))
)))
(assert (forall ((|#$R@@1| T@U) ) (!  (and (= (Tag (Tclass._System.___hFunc0 |#$R@@1|)) Tagclass._System.___hFunc0) (= (TagFamily (Tclass._System.___hFunc0 |#$R@@1|)) |tytagFamily$_#Func0|))
 :qid |testbpl.2331:15|
 :skolemid |414|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@1|))
)))
(assert (forall ((|#$R@@2| T@U) ) (!  (and (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@2|)) Tagclass._System.___hPartialFunc0) (= (TagFamily (Tclass._System.___hPartialFunc0 |#$R@@2|)) |tytagFamily$_#PartialFunc0|))
 :qid |testbpl.2509:15|
 :skolemid |441|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@2|))
)))
(assert (forall ((|#$R@@3| T@U) ) (!  (and (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@3|)) Tagclass._System.___hTotalFunc0) (= (TagFamily (Tclass._System.___hTotalFunc0 |#$R@@3|)) |tytagFamily$_#TotalFunc0|))
 :qid |testbpl.2546:15|
 :skolemid |446|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@3|))
)))
(assert (forall ((a@@23 T@U) (b@@16 T@U) (y T@U) (T@@32 T@T) ) (!  (=> (<= (U_2_int (MapType0Select T@@32 intType a@@23 y)) (U_2_int (MapType0Select T@@32 intType b@@16 y))) (= (U_2_int (MapType0Select T@@32 intType (|MultiSet#Difference| T@@32 a@@23 b@@16) y)) 0))
 :qid |testbpl.1110:18|
 :skolemid |202|
 :pattern ( (|MultiSet#Difference| T@@32 a@@23 b@@16) (MapType0Select T@@32 intType b@@16 y) (MapType0Select T@@32 intType a@@23 y))
)))
(assert (forall ((u@@3 T@U) (U@@8 T@T) (V@@8 T@T) ) (!  (not (U_2_bool (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3)))
 :qid |testbpl.1524:20|
 :skolemid |288|
 :pattern ( (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3))
)))
(assert (forall ((u@@4 T@U) (U@@9 T@T) (V@@9 T@T) ) (!  (not (U_2_bool (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4)))
 :qid |testbpl.1656:20|
 :skolemid |318|
 :pattern ( (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4))
)))
(assert (forall ((h@@6 T@U) (k@@2 T@U) ) (!  (=> ($HeapSuccGhost h@@6 k@@2) (and ($HeapSucc h@@6 k@@2) (forall ((o@@10 T@U) (f@@8 T@U) (alpha T@T) ) (!  (=> (not ($IsGhostField alpha f@@8)) (= ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) h@@6 o@@10) f@@8)) ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@10) f@@8))))
 :qid |testbpl.652:26|
 :skolemid |107|
 :pattern ( ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@10) f@@8)))
))))
 :qid |testbpl.648:15|
 :skolemid |108|
 :pattern ( ($HeapSuccGhost h@@6 k@@2))
)))
(assert (forall ((o@@11 T@U) (p@@0 T@U) ) (!  (=> (and (|ORD#IsNat| p@@0) (<= (|ORD#Offset| p@@0) (|ORD#Offset| o@@11))) (and (= (|ORD#IsNat| (|ORD#Minus| o@@11 p@@0)) (|ORD#IsNat| o@@11)) (= (|ORD#Offset| (|ORD#Minus| o@@11 p@@0)) (- (|ORD#Offset| o@@11) (|ORD#Offset| p@@0)))))
 :qid |testbpl.531:15|
 :skolemid |94|
 :pattern ( (|ORD#Minus| o@@11 p@@0))
)))
(assert (forall ((a@@24 T@U) (b@@17 T@U) (T@@33 T@T) ) (! (= (|Set#Equal| T@@33 a@@24 b@@17) (forall ((o@@12 T@U) ) (! (= (U_2_bool (MapType0Select T@@33 boolType a@@24 o@@12)) (U_2_bool (MapType0Select T@@33 boolType b@@17 o@@12)))
 :qid |testbpl.901:32|
 :skolemid |150|
 :pattern ( (MapType0Select T@@33 boolType a@@24 o@@12))
 :pattern ( (MapType0Select T@@33 boolType b@@17 o@@12))
)))
 :qid |testbpl.899:18|
 :skolemid |151|
 :pattern ( (|Set#Equal| T@@33 a@@24 b@@17))
)))
(assert (forall ((a@@25 T@U) (b@@18 T@U) (T@@34 T@T) ) (! (= (|ISet#Equal| T@@34 a@@25 b@@18) (forall ((o@@13 T@U) ) (! (= (U_2_bool (MapType0Select T@@34 boolType a@@25 o@@13)) (U_2_bool (MapType0Select T@@34 boolType b@@18 o@@13)))
 :qid |testbpl.991:33|
 :skolemid |172|
 :pattern ( (MapType0Select T@@34 boolType a@@25 o@@13))
 :pattern ( (MapType0Select T@@34 boolType b@@18 o@@13))
)))
 :qid |testbpl.989:18|
 :skolemid |173|
 :pattern ( (|ISet#Equal| T@@34 a@@25 b@@18))
)))
(assert (forall ((t0@@14 T@U) (t1@@3 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@9 T@U) (bx0@@0 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@3 h1@@3) ($IsGoodHeap h0@@3)) ($IsGoodHeap h1@@3)) ($IsBox BoxType bx0@@0 t0@@14)) ($Is HandleTypeType f@@9 (Tclass._System.___hFunc1 t0@@14 t1@@3))) (forall ((o@@14 T@U) (fld@@3 T@U) (a@@26 T@T) ) (!  (=> (and (or (not (= o@@14 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@14 t1@@3 h0@@3 f@@9 bx0@@0) ($Box refType o@@14)))) (= ($Unbox a@@26 (MapType1Select a@@26 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@3 o@@14) fld@@3)) ($Unbox a@@26 (MapType1Select a@@26 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@3 o@@14) fld@@3))))
 :qid |testbpl.2123:22|
 :skolemid |380|
))) (= (Requires1 t0@@14 t1@@3 h0@@3 f@@9 bx0@@0) (Requires1 t0@@14 t1@@3 h1@@3 f@@9 bx0@@0)))
 :qid |testbpl.2114:15|
 :skolemid |381|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires1 t0@@14 t1@@3 h1@@3 f@@9 bx0@@0))
)))
(assert (forall ((t0@@15 T@U) (t1@@4 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@10 T@U) (bx0@@1 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@4 h1@@4) ($IsGoodHeap h0@@4)) ($IsGoodHeap h1@@4)) ($IsBox BoxType bx0@@1 t0@@15)) ($Is HandleTypeType f@@10 (Tclass._System.___hFunc1 t0@@15 t1@@4))) (forall ((o@@15 T@U) (fld@@4 T@U) (a@@27 T@T) ) (!  (=> (and (or (not (= o@@15 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1) ($Box refType o@@15)))) (= ($Unbox a@@27 (MapType1Select a@@27 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@4 o@@15) fld@@4)) ($Unbox a@@27 (MapType1Select a@@27 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@4 o@@15) fld@@4))))
 :qid |testbpl.2138:22|
 :skolemid |382|
))) (= (Requires1 t0@@15 t1@@4 h0@@4 f@@10 bx0@@1) (Requires1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1)))
 :qid |testbpl.2129:15|
 :skolemid |383|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Requires1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1))
)))
(assert (forall ((a@@28 T@U) (b@@19 T@U) (T@@35 T@T) ) (! (= (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@28 b@@19)) (+ (|MultiSet#Card| T@@35 a@@28) (|MultiSet#Card| T@@35 b@@19)))
 :qid |testbpl.1084:18|
 :skolemid |197|
 :pattern ( (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@28 b@@19)))
)))
(assert (forall ((s0@@2 T@U) (s1@@0 T@U) (T@@36 T@T) ) (! (= (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)) (+ (|Seq#Length| T@@36 s0@@2) (|Seq#Length| T@@36 s1@@0)))
 :qid |testbpl.1254:18|
 :skolemid |231|
 :pattern ( (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)))
)))
(assert (forall ((n@@8 Int) ) (!  (=> (<= 0 n@@8) (and (|ORD#IsNat| (|ORD#FromNat| n@@8)) (= (|ORD#Offset| (|ORD#FromNat| n@@8)) n@@8)))
 :qid |testbpl.478:15|
 :skolemid |85|
 :pattern ( (|ORD#FromNat| n@@8))
)))
(assert (forall ((|#$T0| T@U) (|#$R@@4| T@U) (|f#0@@1| T@U) ($h@@9 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0| |#$R@@4|) $h@@9) ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hFunc1 |#$T0| |#$R@@4|) $h@@9))
 :qid |testbpl.2275:15|
 :skolemid |406|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0| |#$R@@4|) $h@@9))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$R@@5| T@U) (|f#0@@2| T@U) ($h@@10 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@0| |#$R@@5|) $h@@10) ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@0| |#$R@@5|) $h@@10))
 :qid |testbpl.2321:15|
 :skolemid |413|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@0| |#$R@@5|) $h@@10))
)))
(assert (forall ((ms T@U) (T@@37 T@T) ) (! (= ($IsGoodMultiSet T@@37 ms) (forall ((bx@@6 T@U) ) (!  (and (<= 0 (U_2_int (MapType0Select T@@37 intType ms bx@@6))) (<= (U_2_int (MapType0Select T@@37 intType ms bx@@6)) (|MultiSet#Card| T@@37 ms)))
 :qid |testbpl.1026:19|
 :skolemid |182|
 :pattern ( (MapType0Select T@@37 intType ms bx@@6))
)))
 :qid |testbpl.1023:18|
 :skolemid |183|
 :pattern ( ($IsGoodMultiSet T@@37 ms))
)))
(assert (forall ((o@@16 T@U) (p@@1 T@U) ) (!  (and (or (= o@@16 (|ORD#Plus| o@@16 p@@1)) (|ORD#Less| o@@16 (|ORD#Plus| o@@16 p@@1))) (or (= p@@1 (|ORD#Plus| o@@16 p@@1)) (|ORD#Less| p@@1 (|ORD#Plus| o@@16 p@@1))))
 :qid |testbpl.519:15|
 :skolemid |92|
 :pattern ( (|ORD#Plus| o@@16 p@@1))
)))
(assert  (and (forall ((t0@@16 T@T) (t1@@5 T@T) (t2 T@T) (val@@4 T@U) (m@@10 T@U) (x0@@4 T@U) (x1 T@U) ) (! (= (MapType2Select t0@@16 t1@@5 t2 (MapType2Store t0@@16 t1@@5 t2 m@@10 x0@@4 x1 val@@4) x0@@4 x1) val@@4)
 :qid |mapAx0:MapType2Select|
 :weight 0
)) (and (forall ((u0@@3 T@T) (u1@@1 T@T) (u2 T@T) (val@@5 T@U) (m@@11 T@U) (x0@@5 T@U) (x1@@0 T@U) (y0@@2 T@U) (y1 T@U) ) (!  (or (= x0@@5 y0@@2) (= (MapType2Select u0@@3 u1@@1 u2 (MapType2Store u0@@3 u1@@1 u2 m@@11 x0@@5 x1@@0 val@@5) y0@@2 y1) (MapType2Select u0@@3 u1@@1 u2 m@@11 y0@@2 y1)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
)) (forall ((u0@@4 T@T) (u1@@2 T@T) (u2@@0 T@T) (val@@6 T@U) (m@@12 T@U) (x0@@6 T@U) (x1@@1 T@U) (y0@@3 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType2Select u0@@4 u1@@2 u2@@0 (MapType2Store u0@@4 u1@@2 u2@@0 m@@12 x0@@6 x1@@1 val@@6) y0@@3 y1@@0) (MapType2Select u0@@4 u1@@2 u2@@0 m@@12 y0@@3 y1@@0)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
)))))
(assert (forall ((t0@@17 T@U) (t1@@6 T@U) (heap@@3 T@U) (h@@7 T@U) (r@@2 T@U) (rd@@0 T@U) (bx0@@2 T@U) ) (! (= (Apply1 t0@@17 t1@@6 heap@@3 (Handle1 h@@7 r@@2 rd@@0) bx0@@2) (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType BoxType h@@7 heap@@3 bx0@@2))
 :qid |testbpl.2042:15|
 :skolemid |373|
 :pattern ( (Apply1 t0@@17 t1@@6 heap@@3 (Handle1 h@@7 r@@2 rd@@0) bx0@@2))
)))
(assert (forall ((bx@@7 T@U) ) (!  (=> ($IsBox BoxType bx@@7 Tclass._System.nat) (and (= ($Box intType ($Unbox intType bx@@7)) bx@@7) ($Is intType ($Unbox intType bx@@7) Tclass._System.nat)))
 :qid |testbpl.1823:15|
 :skolemid |346|
 :pattern ( ($IsBox BoxType bx@@7 Tclass._System.nat))
)))
(assert (forall ((bx@@8 T@U) ) (!  (=> ($IsBox BoxType bx@@8 Tclass._System.object?) (and (= ($Box refType ($Unbox refType bx@@8)) bx@@8) ($Is refType ($Unbox refType bx@@8) Tclass._System.object?)))
 :qid |testbpl.1843:15|
 :skolemid |349|
 :pattern ( ($IsBox BoxType bx@@8 Tclass._System.object?))
)))
(assert (forall ((bx@@9 T@U) ) (!  (=> ($IsBox BoxType bx@@9 Tclass._System.object) (and (= ($Box refType ($Unbox refType bx@@9)) bx@@9) ($Is refType ($Unbox refType bx@@9) Tclass._System.object)))
 :qid |testbpl.1871:15|
 :skolemid |352|
 :pattern ( ($IsBox BoxType bx@@9 Tclass._System.object))
)))
(assert (forall ((bx@@10 T@U) ) (!  (=> ($IsBox BoxType bx@@10 Tclass._System.Tuple0) (and (= ($Box DatatypeTypeType ($Unbox DatatypeTypeType bx@@10)) bx@@10) ($Is DatatypeTypeType ($Unbox DatatypeTypeType bx@@10) Tclass._System.Tuple0)))
 :qid |testbpl.2779:15|
 :skolemid |476|
 :pattern ( ($IsBox BoxType bx@@10 Tclass._System.Tuple0))
)))
(assert (forall ((_System.array$arg@@5 T@U) ($o@@2 T@U) ) (! (= ($Is refType $o@@2 (Tclass._System.array? _System.array$arg@@5))  (or (= $o@@2 null) (= (dtype $o@@2) (Tclass._System.array? _System.array$arg@@5))))
 :qid |testbpl.1941:15|
 :skolemid |360|
 :pattern ( ($Is refType $o@@2 (Tclass._System.array? _System.array$arg@@5)))
)))
(assert (forall ((a@@29 T@U) (x@@11 T@U) (T@@38 T@T) ) (! (= (U_2_int (MapType0Select T@@38 intType (|MultiSet#UnionOne| T@@38 a@@29 x@@11) x@@11)) (+ (U_2_int (MapType0Select T@@38 intType a@@29 x@@11)) 1))
 :qid |testbpl.1062:18|
 :skolemid |192|
 :pattern ( (|MultiSet#UnionOne| T@@38 a@@29 x@@11))
)))
(assert (forall ((|c#0@@2| T@U) ) (! (= ($Is refType |c#0@@2| Tclass._System.object)  (and ($Is refType |c#0@@2| Tclass._System.object?) (or (not (= |c#0@@2| null)) (not true))))
 :qid |testbpl.1877:15|
 :skolemid |353|
 :pattern ( ($Is refType |c#0@@2| Tclass._System.object))
)))
(assert (forall ((s@@18 T@U) (i@@6 Int) (v@@13 T@U) (T@@39 T@T) ) (!  (and (=> (= i@@6 (|Seq#Length| T@@39 s@@18)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) v@@13)) (=> (or (not (= i@@6 (|Seq#Length| T@@39 s@@18))) (not true)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) (|Seq#Index| T@@39 s@@18 i@@6))))
 :qid |testbpl.1230:18|
 :skolemid |227|
 :pattern ( (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6))
)))
(assert (forall ((a@@30 T@U) (b@@20 T@U) ) (! (= (|char#Minus| a@@30 b@@20) (|char#FromInt| (- (|char#ToInt| a@@30) (|char#ToInt| b@@20))))
 :qid |testbpl.180:15|
 :skolemid |24|
 :pattern ( (|char#Minus| a@@30 b@@20))
)))
(assert (forall ((a@@31 T@U) (b@@21 T@U) ) (! (= (|char#Plus| a@@31 b@@21) (|char#FromInt| (+ (|char#ToInt| a@@31) (|char#ToInt| b@@21))))
 :qid |testbpl.174:15|
 :skolemid |23|
 :pattern ( (|char#Plus| a@@31 b@@21))
)))
(assert (forall ((a@@32 T@U) (x@@12 T@U) (y@@0 T@U) (T@@40 T@T) ) (!  (=> (< 0 (U_2_int (MapType0Select T@@40 intType a@@32 y@@0))) (< 0 (U_2_int (MapType0Select T@@40 intType (|MultiSet#UnionOne| T@@40 a@@32 x@@12) y@@0))))
 :qid |testbpl.1066:18|
 :skolemid |193|
 :pattern ( (|MultiSet#UnionOne| T@@40 a@@32 x@@12) (MapType0Select T@@40 intType a@@32 y@@0))
)))
(assert (forall ((m@@13 T@U) (U@@10 T@T) (V@@10 T@T) ) (!  (or (= m@@13 (|Map#Empty| U@@10 V@@10)) (exists ((k@@3 T@U) ) (! (U_2_bool (MapType0Select U@@10 boolType (|Map#Domain| U@@10 V@@10 m@@13) k@@3))
 :qid |testbpl.1475:31|
 :skolemid |276|
)))
 :qid |testbpl.1473:20|
 :skolemid |277|
 :pattern ( (|Map#Domain| U@@10 V@@10 m@@13))
)))
(assert (forall ((m@@14 T@U) (U@@11 T@T) (V@@11 T@T) ) (!  (or (= m@@14 (|Map#Empty| U@@11 V@@11)) (exists ((v@@14 T@U) ) (! (U_2_bool (MapType0Select V@@11 boolType (|Map#Values| U@@11 V@@11 m@@14) v@@14))
 :qid |testbpl.1479:31|
 :skolemid |278|
)))
 :qid |testbpl.1477:20|
 :skolemid |279|
 :pattern ( (|Map#Values| U@@11 V@@11 m@@14))
)))
(assert (forall ((m@@15 T@U) (U@@12 T@T) (V@@12 T@T) ) (!  (or (= m@@15 (|IMap#Empty| U@@12 V@@12)) (exists ((k@@4 T@U) ) (! (U_2_bool (MapType0Select U@@12 boolType (|IMap#Domain| U@@12 V@@12 m@@15) k@@4))
 :qid |testbpl.1613:32|
 :skolemid |306|
)))
 :qid |testbpl.1611:20|
 :skolemid |307|
 :pattern ( (|IMap#Domain| U@@12 V@@12 m@@15))
)))
(assert (forall ((m@@16 T@U) (U@@13 T@T) (V@@13 T@T) ) (!  (or (= m@@16 (|IMap#Empty| U@@13 V@@13)) (exists ((v@@15 T@U) ) (! (U_2_bool (MapType0Select V@@13 boolType (|IMap#Values| U@@13 V@@13 m@@16) v@@15))
 :qid |testbpl.1617:32|
 :skolemid |308|
)))
 :qid |testbpl.1615:20|
 :skolemid |309|
 :pattern ( (|IMap#Values| U@@13 V@@13 m@@16))
)))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate0)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate0)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate0) MoreFuel__module._default.secretPredicate0)) (= _module.__default.magicNum (LitInt 15213))))))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate1)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate1)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate1) MoreFuel__module._default.secretPredicate1)) (= _module.__default.magicNum (LitInt 15213))))))
(assert (forall ((a@@33 T@U) (x@@13 T@U) (o@@17 T@U) (T@@41 T@T) ) (! (= (< 0 (U_2_int (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@33 x@@13) o@@17)))  (or (= o@@17 x@@13) (< 0 (U_2_int (MapType0Select T@@41 intType a@@33 o@@17)))))
 :qid |testbpl.1058:18|
 :skolemid |191|
 :pattern ( (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@33 x@@13) o@@17))
)))
(assert (forall ((h@@8 T@U) (a@@34 T@U) ) (! (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (|Seq#Length| BoxType (|Seq#FromArray| h@@8 a@@34)))) (= (|Seq#Index| BoxType (|Seq#FromArray| h@@8 a@@34) i@@7) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@8 a@@34) (IndexField i@@7)))))
 :qid |testbpl.1379:11|
 :skolemid |257|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@8 a@@34) (IndexField i@@7))))
 :pattern ( (|Seq#Index| BoxType (|Seq#FromArray| h@@8 a@@34) i@@7))
))
 :qid |testbpl.1377:15|
 :skolemid |258|
 :pattern ( (|Seq#FromArray| h@@8 a@@34))
)))
(assert (forall ((v@@16 T@U) (t0@@18 T@U) ) (! (= ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@18)) (forall ((bx@@11 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@16 bx@@11))) ($IsBox BoxType bx@@11 t0@@18))
 :qid |testbpl.291:19|
 :skolemid |49|
 :pattern ( (MapType0Select BoxType intType v@@16 bx@@11))
)))
 :qid |testbpl.288:15|
 :skolemid |50|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@18)))
)))
(assert (forall ((s0@@3 T@U) (s1@@1 T@U) (x@@14 T@U) (T@@42 T@T) ) (! (= (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14)  (or (|Seq#Contains| T@@42 s0@@3 x@@14) (|Seq#Contains| T@@42 s1@@1 x@@14)))
 :qid |testbpl.1295:18|
 :skolemid |239|
 :pattern ( (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14))
)))
(assert (forall ((s@@19 T@U) (n@@9 Int) (x@@15 T@U) (T@@43 T@T) ) (! (= (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15) (exists ((i@@8 Int) ) (!  (and (and (and (<= 0 i@@8) (< i@@8 n@@9)) (< i@@8 (|Seq#Length| T@@43 s@@19))) (= (|Seq#Index| T@@43 s@@19 i@@8) x@@15))
 :qid |testbpl.1307:19|
 :skolemid |241|
 :pattern ( (|Seq#Index| T@@43 s@@19 i@@8))
)))
 :qid |testbpl.1304:18|
 :skolemid |242|
 :pattern ( (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15))
)))
(assert (forall ((a@@35 T@U) (b@@22 T@U) (T@@44 T@T) ) (!  (=> (|Set#Disjoint| T@@44 a@@35 b@@22) (and (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@35 b@@22) a@@35) b@@22) (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@35 b@@22) b@@22) a@@35)))
 :qid |testbpl.840:18|
 :skolemid |138|
 :pattern ( (|Set#Union| T@@44 a@@35 b@@22))
)))
(assert (forall ((a@@36 T@U) (b@@23 T@U) (T@@45 T@T) ) (!  (=> (|ISet#Disjoint| T@@45 a@@36 b@@23) (and (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@36 b@@23) a@@36) b@@23) (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@36 b@@23) b@@23) a@@36)))
 :qid |testbpl.943:18|
 :skolemid |162|
 :pattern ( (|ISet#Union| T@@45 a@@36 b@@23))
)))
(assert (forall ((f@@11 T@U) (t0@@19 T@U) (t1@@7 T@U) (h@@9 T@U) ) (!  (=> (and ($IsGoodHeap h@@9) ($IsAlloc HandleTypeType f@@11 (Tclass._System.___hFunc1 t0@@19 t1@@7) h@@9)) (forall ((bx0@@3 T@U) ) (!  (=> (and ($IsAllocBox BoxType bx0@@3 t0@@19 h@@9) (Requires1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3)) ($IsAllocBox BoxType (Apply1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3) t1@@7 h@@9))
 :qid |testbpl.2225:18|
 :skolemid |398|
 :pattern ( (Apply1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3))
)))
 :qid |testbpl.2222:15|
 :skolemid |399|
 :pattern ( ($IsAlloc HandleTypeType f@@11 (Tclass._System.___hFunc1 t0@@19 t1@@7) h@@9))
)))
(assert (forall ((a@@37 T@U) (b@@24 T@U) (T@@46 T@T) ) (! (= (|MultiSet#Equal| T@@46 a@@37 b@@24) (forall ((o@@18 T@U) ) (! (= (U_2_int (MapType0Select T@@46 intType a@@37 o@@18)) (U_2_int (MapType0Select T@@46 intType b@@24 o@@18)))
 :qid |testbpl.1133:37|
 :skolemid |206|
 :pattern ( (MapType0Select T@@46 intType a@@37 o@@18))
 :pattern ( (MapType0Select T@@46 intType b@@24 o@@18))
)))
 :qid |testbpl.1131:18|
 :skolemid |207|
 :pattern ( (|MultiSet#Equal| T@@46 a@@37 b@@24))
)))
(assert (forall ((a@@38 T@U) (b@@25 T@U) (T@@47 T@T) ) (! (= (|MultiSet#Subset| T@@47 a@@38 b@@25) (forall ((o@@19 T@U) ) (! (<= (U_2_int (MapType0Select T@@47 intType a@@38 o@@19)) (U_2_int (MapType0Select T@@47 intType b@@25 o@@19)))
 :qid |testbpl.1127:38|
 :skolemid |204|
 :pattern ( (MapType0Select T@@47 intType a@@38 o@@19))
 :pattern ( (MapType0Select T@@47 intType b@@25 o@@19))
)))
 :qid |testbpl.1125:18|
 :skolemid |205|
 :pattern ( (|MultiSet#Subset| T@@47 a@@38 b@@25))
)))
(assert (forall ((t0@@20 T@U) (t1@@8 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@12 T@U) (bx0@@4 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@5 h1@@5) ($IsGoodHeap h0@@5)) ($IsGoodHeap h1@@5)) ($IsBox BoxType bx0@@4 t0@@20)) ($Is HandleTypeType f@@12 (Tclass._System.___hFunc1 t0@@20 t1@@8))) (forall ((o@@20 T@U) (fld@@5 T@U) (a@@39 T@T) ) (!  (=> (and (or (not (= o@@20 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@20 t1@@8 h0@@5 f@@12 bx0@@4) ($Box refType o@@20)))) (= ($Unbox a@@39 (MapType1Select a@@39 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@5 o@@20) fld@@5)) ($Unbox a@@39 (MapType1Select a@@39 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@5 o@@20) fld@@5))))
 :qid |testbpl.2093:22|
 :skolemid |376|
))) (= (Reads1 t0@@20 t1@@8 h0@@5 f@@12 bx0@@4) (Reads1 t0@@20 t1@@8 h1@@5 f@@12 bx0@@4)))
 :qid |testbpl.2084:15|
 :skolemid |377|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Reads1 t0@@20 t1@@8 h1@@5 f@@12 bx0@@4))
)))
(assert (forall ((t0@@21 T@U) (t1@@9 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@13 T@U) (bx0@@5 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@6 h1@@6) ($IsGoodHeap h0@@6)) ($IsGoodHeap h1@@6)) ($IsBox BoxType bx0@@5 t0@@21)) ($Is HandleTypeType f@@13 (Tclass._System.___hFunc1 t0@@21 t1@@9))) (forall ((o@@21 T@U) (fld@@6 T@U) (a@@40 T@T) ) (!  (=> (and (or (not (= o@@21 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5) ($Box refType o@@21)))) (= ($Unbox a@@40 (MapType1Select a@@40 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@6 o@@21) fld@@6)) ($Unbox a@@40 (MapType1Select a@@40 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@6 o@@21) fld@@6))))
 :qid |testbpl.2108:22|
 :skolemid |378|
))) (= (Reads1 t0@@21 t1@@9 h0@@6 f@@13 bx0@@5) (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5)))
 :qid |testbpl.2099:15|
 :skolemid |379|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5))
)))
(assert (forall ((t0@@22 T@U) (t1@@10 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@14 T@U) (bx0@@6 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@7 h1@@7) ($IsGoodHeap h0@@7)) ($IsGoodHeap h1@@7)) ($IsBox BoxType bx0@@6 t0@@22)) ($Is HandleTypeType f@@14 (Tclass._System.___hFunc1 t0@@22 t1@@10))) (forall ((o@@22 T@U) (fld@@7 T@U) (a@@41 T@T) ) (!  (=> (and (or (not (= o@@22 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@22 t1@@10 h0@@7 f@@14 bx0@@6) ($Box refType o@@22)))) (= ($Unbox a@@41 (MapType1Select a@@41 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@7 o@@22) fld@@7)) ($Unbox a@@41 (MapType1Select a@@41 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@7 o@@22) fld@@7))))
 :qid |testbpl.2153:22|
 :skolemid |384|
))) (= (Apply1 t0@@22 t1@@10 h0@@7 f@@14 bx0@@6) (Apply1 t0@@22 t1@@10 h1@@7 f@@14 bx0@@6)))
 :qid |testbpl.2144:15|
 :skolemid |385|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Apply1 t0@@22 t1@@10 h1@@7 f@@14 bx0@@6))
)))
(assert (forall ((t0@@23 T@U) (t1@@11 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@15 T@U) (bx0@@7 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@8 h1@@8) ($IsGoodHeap h0@@8)) ($IsGoodHeap h1@@8)) ($IsBox BoxType bx0@@7 t0@@23)) ($Is HandleTypeType f@@15 (Tclass._System.___hFunc1 t0@@23 t1@@11))) (forall ((o@@23 T@U) (fld@@8 T@U) (a@@42 T@T) ) (!  (=> (and (or (not (= o@@23 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7) ($Box refType o@@23)))) (= ($Unbox a@@42 (MapType1Select a@@42 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@8 o@@23) fld@@8)) ($Unbox a@@42 (MapType1Select a@@42 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@8 o@@23) fld@@8))))
 :qid |testbpl.2168:22|
 :skolemid |386|
))) (= (Apply1 t0@@23 t1@@11 h0@@8 f@@15 bx0@@7) (Apply1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7)))
 :qid |testbpl.2159:15|
 :skolemid |387|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Apply1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7))
)))
(assert (forall ((m@@17 T@U) (U@@14 T@T) (V@@14 T@T) ) (! (= (= (|Map#Card| U@@14 V@@14 m@@17) 0) (= m@@17 (|Map#Empty| U@@14 V@@14)))
 :qid |testbpl.1469:20|
 :skolemid |275|
 :pattern ( (|Map#Card| U@@14 V@@14 m@@17))
)))
(assert (forall ((a@@43 T@U) (b@@26 T@U) ) (!  (=> true (= (|_System.Tuple0#Equal| a@@43 b@@26) true))
 :qid |testbpl.2808:15|
 :skolemid |480|
 :pattern ( (|_System.Tuple0#Equal| a@@43 b@@26))
)))
(assert (forall ((s@@20 T@U) (x@@16 T@U) (T@@48 T@T) ) (! (= (|Seq#Contains| T@@48 s@@20 x@@16) (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| T@@48 s@@20))) (= (|Seq#Index| T@@48 s@@20 i@@9) x@@16))
 :qid |testbpl.1287:19|
 :skolemid |236|
 :pattern ( (|Seq#Index| T@@48 s@@20 i@@9))
)))
 :qid |testbpl.1284:18|
 :skolemid |237|
 :pattern ( (|Seq#Contains| T@@48 s@@20 x@@16))
)))
(assert (forall (($ly@@1 T@U) (|q#0@@1| Int) ) (! (= (|_module.__default.secretPredicate#requires| $ly@@1 |q#0@@1|) true)
 :qid |testbpl.2868:15|
 :skolemid |487|
 :pattern ( (|_module.__default.secretPredicate#requires| $ly@@1 |q#0@@1|))
)))
(assert (forall ((f@@16 T@U) (t0@@24 T@U) (t1@@12 T@U) (h@@10 T@U) ) (!  (=> ($IsGoodHeap h@@10) (= ($IsAlloc HandleTypeType f@@16 (Tclass._System.___hFunc1 t0@@24 t1@@12) h@@10) (forall ((bx0@@8 T@U) ) (!  (=> (and (and ($IsBox BoxType bx0@@8 t0@@24) ($IsAllocBox BoxType bx0@@8 t0@@24 h@@10)) (Requires1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8)) (forall ((r@@3 T@U) ) (!  (=> (and (or (not (= r@@3 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8) ($Box refType r@@3)))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@10 r@@3) alloc))))
 :qid |testbpl.2218:24|
 :skolemid |395|
 :pattern ( (MapType0Select BoxType boolType (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8) ($Box refType r@@3)))
)))
 :qid |testbpl.2215:21|
 :skolemid |396|
 :pattern ( (Apply1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8))
 :pattern ( (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8))
))))
 :qid |testbpl.2211:15|
 :skolemid |397|
 :pattern ( ($IsAlloc HandleTypeType f@@16 (Tclass._System.___hFunc1 t0@@24 t1@@12) h@@10))
)))
(assert (forall ((s@@21 T@U) (i@@10 Int) (v@@17 T@U) (n@@10 Int) (T@@49 T@T) ) (!  (=> (and (and (<= 0 i@@10) (< i@@10 n@@10)) (<= n@@10 (|Seq#Length| T@@49 s@@21))) (= (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10) (|Seq#Drop| T@@49 s@@21 n@@10)))
 :qid |testbpl.1410:18|
 :skolemid |264|
 :pattern ( (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10))
)))
(assert (forall ((a@@44 T@U) (b@@27 T@U) (o@@24 T@U) (T@@50 T@T) ) (! (= (U_2_bool (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@44 b@@27) o@@24))  (and (U_2_bool (MapType0Select T@@50 boolType a@@44 o@@24)) (U_2_bool (MapType0Select T@@50 boolType b@@27 o@@24))))
 :qid |testbpl.848:18|
 :skolemid |139|
 :pattern ( (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@44 b@@27) o@@24))
)))
(assert (forall ((a@@45 T@U) (b@@28 T@U) (o@@25 T@U) (T@@51 T@T) ) (! (= (U_2_bool (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@45 b@@28) o@@25))  (and (U_2_bool (MapType0Select T@@51 boolType a@@45 o@@25)) (U_2_bool (MapType0Select T@@51 boolType b@@28 o@@25))))
 :qid |testbpl.951:18|
 :skolemid |163|
 :pattern ( (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@45 b@@28) o@@25))
)))
(assert (forall ((o@@26 T@U) (p@@2 T@U) ) (!  (or (or (|ORD#Less| o@@26 p@@2) (= o@@26 p@@2)) (|ORD#Less| p@@2 o@@26))
 :qid |testbpl.496:15|
 :skolemid |88|
 :pattern ( (|ORD#Less| o@@26 p@@2) (|ORD#Less| p@@2 o@@26))
)))
(assert (forall ((a@@46 T@U) (b@@29 T@U) (o@@27 T@U) (T@@52 T@T) ) (! (= (U_2_bool (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@46 b@@29) o@@27))  (and (U_2_bool (MapType0Select T@@52 boolType a@@46 o@@27)) (not (U_2_bool (MapType0Select T@@52 boolType b@@29 o@@27)))))
 :qid |testbpl.875:18|
 :skolemid |145|
 :pattern ( (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@46 b@@29) o@@27))
)))
(assert (forall ((a@@47 T@U) (b@@30 T@U) (o@@28 T@U) (T@@53 T@T) ) (! (= (U_2_bool (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@47 b@@30) o@@28))  (and (U_2_bool (MapType0Select T@@53 boolType a@@47 o@@28)) (not (U_2_bool (MapType0Select T@@53 boolType b@@30 o@@28)))))
 :qid |testbpl.973:18|
 :skolemid |168|
 :pattern ( (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@47 b@@30) o@@28))
)))
(assert (forall ((v@@18 T@U) (t0@@25 T@U) (h@@11 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@25) h@@11) (forall ((bx@@12 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@18 bx@@12)) ($IsAllocBox BoxType bx@@12 t0@@25 h@@11))
 :qid |testbpl.353:19|
 :skolemid |66|
 :pattern ( (MapType0Select BoxType boolType v@@18 bx@@12))
)))
 :qid |testbpl.350:15|
 :skolemid |67|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@25) h@@11))
)))
(assert (forall ((v@@19 T@U) (t0@@26 T@U) (h@@12 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@26) h@@12) (forall ((bx@@13 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@19 bx@@13)) ($IsAllocBox BoxType bx@@13 t0@@26 h@@12))
 :qid |testbpl.358:19|
 :skolemid |68|
 :pattern ( (MapType0Select BoxType boolType v@@19 bx@@13))
)))
 :qid |testbpl.355:15|
 :skolemid |69|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@26) h@@12))
)))
(assert (forall ((o@@29 T@U) (T@@54 T@T) ) (! (= (U_2_int (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@29)) 0)
 :qid |testbpl.1038:18|
 :skolemid |186|
 :pattern ( (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@29))
)))
(assert (forall ((t0@@27 T@U) (heap@@4 T@U) (f@@17 T@U) ) (!  (=> (and ($IsGoodHeap heap@@4) ($Is HandleTypeType f@@17 (Tclass._System.___hFunc0 t0@@27))) (= (|Set#Equal| BoxType (Reads0 t0@@27 $OneHeap f@@17) (|Set#Empty| BoxType)) (|Set#Equal| BoxType (Reads0 t0@@27 heap@@4 f@@17) (|Set#Empty| BoxType))))
 :qid |testbpl.2459:15|
 :skolemid |432|
 :pattern ( (Reads0 t0@@27 $OneHeap f@@17) ($IsGoodHeap heap@@4))
 :pattern ( (Reads0 t0@@27 heap@@4 f@@17))
)))
(assert (forall ((m@@18 T@U) (item T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@18) item))  (and (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType m@@18) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType m@@18) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item)))))
 :qid |testbpl.1515:15|
 :skolemid |287|
 :pattern ( (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@18) item))
)))
(assert (forall ((m@@19 T@U) (item@@0 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@19) item@@0))  (and (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))))
 :qid |testbpl.1647:15|
 :skolemid |317|
 :pattern ( (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@19) item@@0))
)))
(assert (forall ((m@@20 T@U) (v@@20 T@U) (U@@15 T@T) (V@@15 T@T) ) (! (= (U_2_bool (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@20) v@@20)) (exists ((u@@5 T@U) ) (!  (and (U_2_bool (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@20) u@@5)) (= v@@20 (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@20) u@@5)))
 :qid |testbpl.1503:17|
 :skolemid |285|
 :pattern ( (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@20) u@@5))
 :pattern ( (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@20) u@@5))
)))
 :qid |testbpl.1500:20|
 :skolemid |286|
 :pattern ( (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@20) v@@20))
)))
(assert (forall ((m@@21 T@U) (v@@21 T@U) (U@@16 T@T) (V@@16 T@T) ) (! (= (U_2_bool (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@21) v@@21)) (exists ((u@@6 T@U) ) (!  (and (U_2_bool (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@21) u@@6)) (= v@@21 (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@21) u@@6)))
 :qid |testbpl.1641:17|
 :skolemid |315|
 :pattern ( (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@21) u@@6))
 :pattern ( (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@21) u@@6))
)))
 :qid |testbpl.1638:20|
 :skolemid |316|
 :pattern ( (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@21) v@@21))
)))
(assert (forall ((t0@@28 T@U) (t1@@13 T@U) (heap@@5 T@U) (h@@13 T@U) (r@@4 T@U) (rd@@1 T@U) (bx0@@9 T@U) (bx@@14 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@28 t1@@13 heap@@5 (Handle1 h@@13 r@@4 rd@@1) bx0@@9) bx@@14)) (U_2_bool (MapType0Select BoxType boolType (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType (MapType0Type BoxType boolType) rd@@1 heap@@5 bx0@@9) bx@@14)))
 :qid |testbpl.2062:15|
 :skolemid |375|
 :pattern ( (MapType0Select BoxType boolType (Reads1 t0@@28 t1@@13 heap@@5 (Handle1 h@@13 r@@4 rd@@1) bx0@@9) bx@@14))
)))
(assert  (and (and (forall ((arg0@@9 T@T) (arg1@@2 T@T) ) (! (= (Ctor (MapType arg0@@9 arg1@@2)) 11)
 :qid |ctor:MapType|
)) (forall ((arg0@@10 T@T) (arg1@@3 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@10 arg1@@3)) arg0@@10)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@10 arg1@@3))
))) (forall ((arg0@@11 T@T) (arg1@@4 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@11 arg1@@4)) arg1@@4)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@11 arg1@@4))
))))
(assert (forall ((v@@22 T@U) (t0@@29 T@U) (t1@@14 T@U) (h@@14 T@U) ) (! (= ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@29 t1@@14) h@@14) (forall ((bx@@15 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@15)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@15) t1@@14 h@@14) ($IsAllocBox BoxType bx@@15 t0@@29 h@@14)))
 :qid |testbpl.375:19|
 :skolemid |74|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@15))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@15))
)))
 :qid |testbpl.372:15|
 :skolemid |75|
 :pattern ( ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@29 t1@@14) h@@14))
)))
(assert  (and (and (forall ((arg0@@12 T@T) (arg1@@5 T@T) ) (! (= (Ctor (IMapType arg0@@12 arg1@@5)) 12)
 :qid |ctor:IMapType|
)) (forall ((arg0@@13 T@T) (arg1@@6 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@13 arg1@@6)) arg0@@13)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@13 arg1@@6))
))) (forall ((arg0@@14 T@T) (arg1@@7 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@14 arg1@@7)) arg1@@7)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@14 arg1@@7))
))))
(assert (forall ((v@@23 T@U) (t0@@30 T@U) (t1@@15 T@U) (h@@15 T@U) ) (! (= ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@30 t1@@15) h@@15) (forall ((bx@@16 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@16)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@16) t1@@15 h@@15) ($IsAllocBox BoxType bx@@16 t0@@30 h@@15)))
 :qid |testbpl.383:19|
 :skolemid |76|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@16))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@16))
)))
 :qid |testbpl.380:15|
 :skolemid |77|
 :pattern ( ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@30 t1@@15) h@@15))
)))
(assert (forall ((o@@30 T@U) (p@@3 T@U) ) (!  (and (=> (= o@@30 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@30 p@@3) p@@3)) (=> (= p@@3 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@30 p@@3) o@@30)))
 :qid |testbpl.524:15|
 :skolemid |93|
 :pattern ( (|ORD#Plus| o@@30 p@@3))
)))
(assert (forall ((x@@17 Int) (y@@1 Int) ) (! (= (INTERNAL_div_boogie x@@17 y@@1) (div x@@17 y@@1))
 :qid |testbpl.1748:15|
 :skolemid |335|
 :pattern ( (INTERNAL_div_boogie x@@17 y@@1))
)))
(assert (forall ((x@@18 Int) (y@@2 Int) ) (! (= (Div x@@18 y@@2) (div x@@18 y@@2))
 :qid |testbpl.1795:15|
 :skolemid |342|
 :pattern ( (Div x@@18 y@@2))
)))
(assert (forall ((o@@31 T@U) (p@@4 T@U) ) (! (= (|ORD#LessThanLimit| o@@31 p@@4) (|ORD#Less| o@@31 p@@4))
 :qid |testbpl.506:15|
 :skolemid |90|
 :pattern ( (|ORD#LessThanLimit| o@@31 p@@4))
)))
(assert (forall (($ly@@2 T@U) (|q#0@@2| Int) ) (! (= (_module.__default.secretPredicate $ly@@2 |q#0@@2|) (_module.__default.secretPredicate $LZ |q#0@@2|))
 :qid |testbpl.2860:15|
 :skolemid |486|
 :pattern ( (_module.__default.secretPredicate (AsFuelBottom $ly@@2) |q#0@@2|))
)))
(assert (forall ((a@@48 T@U) (b@@31 T@U) (T@@55 T@T) ) (!  (=> (|Set#Equal| T@@55 a@@48 b@@31) (= a@@48 b@@31))
 :qid |testbpl.903:18|
 :skolemid |152|
 :pattern ( (|Set#Equal| T@@55 a@@48 b@@31))
)))
(assert (forall ((a@@49 T@U) (b@@32 T@U) (T@@56 T@T) ) (!  (=> (|ISet#Equal| T@@56 a@@49 b@@32) (= a@@49 b@@32))
 :qid |testbpl.993:18|
 :skolemid |174|
 :pattern ( (|ISet#Equal| T@@56 a@@49 b@@32))
)))
(assert (forall ((a@@50 T@U) (b@@33 T@U) (T@@57 T@T) ) (!  (=> (|MultiSet#Equal| T@@57 a@@50 b@@33) (= a@@50 b@@33))
 :qid |testbpl.1135:18|
 :skolemid |208|
 :pattern ( (|MultiSet#Equal| T@@57 a@@50 b@@33))
)))
(assert (forall ((a@@51 T@U) (b@@34 T@U) (T@@58 T@T) ) (!  (=> (|Seq#Equal| T@@58 a@@51 b@@34) (= a@@51 b@@34))
 :qid |testbpl.1328:18|
 :skolemid |247|
 :pattern ( (|Seq#Equal| T@@58 a@@51 b@@34))
)))
(assert (forall ((m@@22 T@U) (|m'@@0| T@U) (U@@17 T@T) (V@@17 T@T) ) (!  (=> (|Map#Equal| U@@17 V@@17 m@@22 |m'@@0|) (= m@@22 |m'@@0|))
 :qid |testbpl.1592:20|
 :skolemid |303|
 :pattern ( (|Map#Equal| U@@17 V@@17 m@@22 |m'@@0|))
)))
(assert (forall ((m@@23 T@U) (|m'@@1| T@U) (U@@18 T@T) (V@@18 T@T) ) (!  (=> (|IMap#Equal| U@@18 V@@18 m@@23 |m'@@1|) (= m@@23 |m'@@1|))
 :qid |testbpl.1696:20|
 :skolemid |327|
 :pattern ( (|IMap#Equal| U@@18 V@@18 m@@23 |m'@@1|))
)))
(assert (forall ((a@@52 T@U) (x@@19 T@U) (y@@3 T@U) (T@@59 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@59 boolType a@@52 y@@3)) (U_2_bool (MapType0Select T@@59 boolType (|Set#UnionOne| T@@59 a@@52 x@@19) y@@3)))
 :qid |testbpl.814:18|
 :skolemid |132|
 :pattern ( (|Set#UnionOne| T@@59 a@@52 x@@19) (MapType0Select T@@59 boolType a@@52 y@@3))
)))
(assert (forall ((a@@53 T@U) (b@@35 T@U) (y@@4 T@U) (T@@60 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@60 boolType a@@53 y@@4)) (U_2_bool (MapType0Select T@@60 boolType (|Set#Union| T@@60 a@@53 b@@35) y@@4)))
 :qid |testbpl.832:18|
 :skolemid |136|
 :pattern ( (|Set#Union| T@@60 a@@53 b@@35) (MapType0Select T@@60 boolType a@@53 y@@4))
)))
(assert (forall ((a@@54 T@U) (b@@36 T@U) (y@@5 T@U) (T@@61 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@61 boolType b@@36 y@@5)) (U_2_bool (MapType0Select T@@61 boolType (|Set#Union| T@@61 a@@54 b@@36) y@@5)))
 :qid |testbpl.836:18|
 :skolemid |137|
 :pattern ( (|Set#Union| T@@61 a@@54 b@@36) (MapType0Select T@@61 boolType b@@36 y@@5))
)))
(assert (forall ((a@@55 T@U) (x@@20 T@U) (y@@6 T@U) (T@@62 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@62 boolType a@@55 y@@6)) (U_2_bool (MapType0Select T@@62 boolType (|ISet#UnionOne| T@@62 a@@55 x@@20) y@@6)))
 :qid |testbpl.925:18|
 :skolemid |158|
 :pattern ( (|ISet#UnionOne| T@@62 a@@55 x@@20) (MapType0Select T@@62 boolType a@@55 y@@6))
)))
(assert (forall ((a@@56 T@U) (b@@37 T@U) (y@@7 T@U) (T@@63 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@63 boolType a@@56 y@@7)) (U_2_bool (MapType0Select T@@63 boolType (|ISet#Union| T@@63 a@@56 b@@37) y@@7)))
 :qid |testbpl.935:18|
 :skolemid |160|
 :pattern ( (|ISet#Union| T@@63 a@@56 b@@37) (MapType0Select T@@63 boolType a@@56 y@@7))
)))
(assert (forall ((a@@57 T@U) (b@@38 T@U) (y@@8 T@U) (T@@64 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@64 boolType b@@38 y@@8)) (U_2_bool (MapType0Select T@@64 boolType (|ISet#Union| T@@64 a@@57 b@@38) y@@8)))
 :qid |testbpl.939:18|
 :skolemid |161|
 :pattern ( (|ISet#Union| T@@64 a@@57 b@@38) (MapType0Select T@@64 boolType b@@38 y@@8))
)))
(assert (forall ((x@@21 Int) ) (! (= (q@Real x@@21) (to_real x@@21))
 :qid |testbpl.679:15|
 :skolemid |113|
 :pattern ( (q@Real x@@21))
)))
(assert (forall ((a@@58 T@U) (x@@22 T@U) (o@@32 T@U) (T@@65 T@T) ) (! (= (U_2_bool (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@58 x@@22) o@@32))  (or (= o@@32 x@@22) (U_2_bool (MapType0Select T@@65 boolType a@@58 o@@32))))
 :qid |testbpl.808:18|
 :skolemid |130|
 :pattern ( (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@58 x@@22) o@@32))
)))
(assert (forall ((a@@59 T@U) (x@@23 T@U) (o@@33 T@U) (T@@66 T@T) ) (! (= (U_2_bool (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@59 x@@23) o@@33))  (or (= o@@33 x@@23) (U_2_bool (MapType0Select T@@66 boolType a@@59 o@@33))))
 :qid |testbpl.919:18|
 :skolemid |156|
 :pattern ( (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@59 x@@23) o@@33))
)))
(assert (forall ((s@@22 T@U) (n@@11 Int) (T@@67 T@T) ) (!  (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| T@@67 s@@22))) (= (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)) n@@11))
 :qid |testbpl.1341:18|
 :skolemid |250|
 :pattern ( (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)))
)))
(assert (forall ((a@@60 T@U) (b@@39 T@U) (c T@U) ) (!  (=> (or (not (= a@@60 c)) (not true)) (=> (and ($HeapSucc a@@60 b@@39) ($HeapSucc b@@39 c)) ($HeapSucc a@@60 c)))
 :qid |testbpl.718:15|
 :skolemid |116|
 :pattern ( ($HeapSucc a@@60 b@@39) ($HeapSucc b@@39 c))
)))
(assert (forall ((a@@61 T@U) (b@@40 T@U) (y@@9 T@U) (T@@68 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@68 boolType b@@40 y@@9)) (not (U_2_bool (MapType0Select T@@68 boolType (|Set#Difference| T@@68 a@@61 b@@40) y@@9))))
 :qid |testbpl.879:18|
 :skolemid |146|
 :pattern ( (|Set#Difference| T@@68 a@@61 b@@40) (MapType0Select T@@68 boolType b@@40 y@@9))
)))
(assert (forall ((a@@62 T@U) (b@@41 T@U) (y@@10 T@U) (T@@69 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@69 boolType b@@41 y@@10)) (not (U_2_bool (MapType0Select T@@69 boolType (|ISet#Difference| T@@69 a@@62 b@@41) y@@10))))
 :qid |testbpl.977:18|
 :skolemid |169|
 :pattern ( (|ISet#Difference| T@@69 a@@62 b@@41) (MapType0Select T@@69 boolType b@@41 y@@10))
)))
(assert (forall ((f@@18 T@U) (t0@@31 T@U) (t1@@16 T@U) ) (! (= ($Is HandleTypeType f@@18 (Tclass._System.___hFunc1 t0@@31 t1@@16)) (forall ((h@@16 T@U) (bx0@@10 T@U) ) (!  (=> (and (and ($IsGoodHeap h@@16) ($IsBox BoxType bx0@@10 t0@@31)) (Requires1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10)) ($IsBox BoxType (Apply1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10) t1@@16))
 :qid |testbpl.2195:19|
 :skolemid |390|
 :pattern ( (Apply1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10))
)))
 :qid |testbpl.2192:15|
 :skolemid |391|
 :pattern ( ($Is HandleTypeType f@@18 (Tclass._System.___hFunc1 t0@@31 t1@@16)))
)))
(assert (forall ((m@@24 T@U) (U@@19 T@T) (V@@19 T@T) ) (! (= (= m@@24 (|IMap#Empty| U@@19 V@@19)) (= (|IMap#Domain| U@@19 V@@19 m@@24) (|ISet#Empty| U@@19)))
 :qid |testbpl.1624:20|
 :skolemid |312|
 :pattern ( (|IMap#Domain| U@@19 V@@19 m@@24))
)))
(assert (forall ((m@@25 T@U) (U@@20 T@T) (V@@20 T@T) ) (! (= (= m@@25 (|IMap#Empty| U@@20 V@@20)) (= (|IMap#Values| U@@20 V@@20 m@@25) (|ISet#Empty| V@@20)))
 :qid |testbpl.1628:20|
 :skolemid |313|
 :pattern ( (|IMap#Values| U@@20 V@@20 m@@25))
)))
(assert (forall ((m@@26 T@U) (U@@21 T@T) (V@@21 T@T) ) (! (= (= m@@26 (|IMap#Empty| U@@21 V@@21)) (= (|IMap#Items| U@@21 V@@21 m@@26) (|ISet#Empty| BoxType)))
 :qid |testbpl.1632:20|
 :skolemid |314|
 :pattern ( (|IMap#Items| U@@21 V@@21 m@@26))
)))
(assert (forall ((m@@27 T@U) (U@@22 T@T) (V@@22 T@T) ) (!  (or (= m@@27 (|Map#Empty| U@@22 V@@22)) (exists ((k@@5 T@U) (v@@24 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|Map#Items| U@@22 V@@22 m@@27) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@5 v@@24))))
 :qid |testbpl.1484:17|
 :skolemid |280|
)))
 :qid |testbpl.1481:20|
 :skolemid |281|
 :pattern ( (|Map#Items| U@@22 V@@22 m@@27))
)))
(assert (forall ((m@@28 T@U) (U@@23 T@T) (V@@23 T@T) ) (!  (or (= m@@28 (|IMap#Empty| U@@23 V@@23)) (exists ((k@@6 T@U) (v@@25 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| U@@23 V@@23 m@@28) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@6 v@@25))))
 :qid |testbpl.1622:17|
 :skolemid |310|
)))
 :qid |testbpl.1619:20|
 :skolemid |311|
 :pattern ( (|IMap#Items| U@@23 V@@23 m@@28))
)))
(assert (forall ((cl T@U) (nm T@U) (T@@70 T@T) ) (!  (and (= (DeclType T@@70 (FieldOfDecl T@@70 cl nm)) cl) (= (DeclName T@@70 (FieldOfDecl T@@70 cl nm)) nm))
 :qid |testbpl.638:18|
 :skolemid |106|
 :pattern ( (FieldOfDecl T@@70 cl nm))
)))
(assert (forall ((bx@@17 T@U) ) (!  (=> ($IsBox BoxType bx@@17 TInt) (and (= ($Box intType ($Unbox intType bx@@17)) bx@@17) ($Is intType ($Unbox intType bx@@17) TInt)))
 :qid |testbpl.202:15|
 :skolemid |26|
 :pattern ( ($IsBox BoxType bx@@17 TInt))
)))
(assert (forall ((bx@@18 T@U) ) (!  (=> ($IsBox BoxType bx@@18 TReal) (and (= ($Box realType ($Unbox realType bx@@18)) bx@@18) ($Is realType ($Unbox realType bx@@18) TReal)))
 :qid |testbpl.206:15|
 :skolemid |27|
 :pattern ( ($IsBox BoxType bx@@18 TReal))
)))
(assert (forall ((bx@@19 T@U) ) (!  (=> ($IsBox BoxType bx@@19 TBool) (and (= ($Box boolType ($Unbox boolType bx@@19)) bx@@19) ($Is boolType ($Unbox boolType bx@@19) TBool)))
 :qid |testbpl.211:15|
 :skolemid |28|
 :pattern ( ($IsBox BoxType bx@@19 TBool))
)))
(assert (= (Ctor charType) 13))
(assert (forall ((bx@@20 T@U) ) (!  (=> ($IsBox BoxType bx@@20 TChar) (and (= ($Box charType ($Unbox charType bx@@20)) bx@@20) ($Is charType ($Unbox charType bx@@20) TChar)))
 :qid |testbpl.216:15|
 :skolemid |29|
 :pattern ( ($IsBox BoxType bx@@20 TChar))
)))
(assert (forall ((a@@63 T@U) (b@@42 T@U) (T@@71 T@T) ) (!  (and (= (+ (+ (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)) (|Set#Card| T@@71 (|Set#Difference| T@@71 b@@42 a@@63))) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@63 b@@42))) (|Set#Card| T@@71 (|Set#Union| T@@71 a@@63 b@@42))) (= (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)) (- (|Set#Card| T@@71 a@@63) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@63 b@@42)))))
 :qid |testbpl.883:18|
 :skolemid |147|
 :pattern ( (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)))
)))
(assert (forall (($ly@@3 T@U) (|q#0@@3| Int) ) (! (= (_module.__default.secretPredicate ($LS $ly@@3) |q#0@@3|) (_module.__default.secretPredicate $ly@@3 |q#0@@3|))
 :qid |testbpl.2854:15|
 :skolemid |485|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@3) |q#0@@3|))
)))
(assert (forall ((v@@26 T@U) (t@@8 T@U) (T@@72 T@T) ) (! (= ($IsBox BoxType ($Box T@@72 v@@26) t@@8) ($Is T@@72 v@@26 t@@8))
 :qid |testbpl.258:18|
 :skolemid |37|
 :pattern ( ($IsBox BoxType ($Box T@@72 v@@26) t@@8))
)))
(assert (forall ((t0@@32 T@U) (t1@@17 T@U) (heap@@6 T@U) (h@@17 T@U) (r@@5 T@U) (rd@@2 T@U) (bx0@@11 T@U) ) (!  (=> (U_2_bool (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType boolType r@@5 heap@@6 bx0@@11)) (Requires1 t0@@32 t1@@17 heap@@6 (Handle1 h@@17 r@@5 rd@@2) bx0@@11))
 :qid |testbpl.2052:15|
 :skolemid |374|
 :pattern ( (Requires1 t0@@32 t1@@17 heap@@6 (Handle1 h@@17 r@@5 rd@@2) bx0@@11))
)))
(assert (forall ((s@@23 T@U) (a@@64 T@U) (T@@73 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64)) 0)  (not (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@64)))) (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64)) 1) (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@64))))
 :qid |testbpl.1148:18|
 :skolemid |211|
 :pattern ( (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64))
)))
(assert (forall ((t@@9 T@U) (T@@74 T@T) ) (! (= (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0) t@@9)
 :qid |testbpl.1260:18|
 :skolemid |232|
 :pattern ( (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0))
)))
(assert (forall ((s@@24 T@U) (i@@11 Int) (v@@27 T@U) (n@@12 Int) (T@@75 T@T) ) (!  (=> (and (<= n@@12 i@@11) (< i@@11 (|Seq#Length| T@@75 s@@24))) (= (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12) (|Seq#Take| T@@75 s@@24 n@@12)))
 :qid |testbpl.1400:18|
 :skolemid |262|
 :pattern ( (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12))
)))
(assert (forall ((r@@6 T@U) (o@@34 T@U) (T@@76 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34)) 1) (= r@@6 o@@34)) (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34)) 0)  (or (not (= r@@6 o@@34)) (not true))))
 :qid |testbpl.1047:18|
 :skolemid |189|
 :pattern ( (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34))
)))
(assert (forall ((o@@35 T@U) ) (! (<= 0 (|ORD#Offset| o@@35))
 :qid |testbpl.464:15|
 :skolemid |84|
 :pattern ( (|ORD#Offset| o@@35))
)))
(assert (forall ((o@@36 T@U) ) (! (<= 0 (_System.array.Length o@@36))
 :qid |testbpl.670:15|
 :skolemid |111|
 :pattern ( (_System.array.Length o@@36))
)))
(assert (forall ((s@@25 T@U) (T@@77 T@T) ) (! (<= 0 (|Set#Card| T@@77 s@@25))
 :qid |testbpl.783:18|
 :skolemid |123|
 :pattern ( (|Set#Card| T@@77 s@@25))
)))
(assert (forall ((s@@26 T@U) (T@@78 T@T) ) (! (<= 0 (|MultiSet#Card| T@@78 s@@26))
 :qid |testbpl.1030:18|
 :skolemid |184|
 :pattern ( (|MultiSet#Card| T@@78 s@@26))
)))
(assert (forall ((s@@27 T@U) (T@@79 T@T) ) (! (<= 0 (|Seq#Length| T@@79 s@@27))
 :qid |testbpl.1198:18|
 :skolemid |221|
 :pattern ( (|Seq#Length| T@@79 s@@27))
)))
(assert (forall ((m@@29 T@U) (U@@24 T@T) (V@@24 T@T) ) (! (<= 0 (|Map#Card| U@@24 V@@24 m@@29))
 :qid |testbpl.1467:20|
 :skolemid |274|
 :pattern ( (|Map#Card| U@@24 V@@24 m@@29))
)))
(assert (forall ((ty@@0 T@U) ) (!  (=> ($AlwaysAllocated ty@@0) (forall ((h@@18 T@U) (v@@28 T@U) ) (!  (=> ($IsBox BoxType v@@28 ty@@0) ($IsAllocBox BoxType v@@28 ty@@0 h@@18))
 :qid |testbpl.393:18|
 :skolemid |78|
 :pattern ( ($IsAllocBox BoxType v@@28 ty@@0 h@@18))
)))
 :qid |testbpl.390:15|
 :skolemid |79|
 :pattern ( ($AlwaysAllocated ty@@0))
)))
(assert (forall ((s@@28 T@U) (i@@12 Int) (j@@2 Int) (T@@80 T@T) ) (!  (=> (and (and (<= 0 i@@12) (< i@@12 j@@2)) (<= j@@2 (|Seq#Length| T@@80 s@@28))) (< (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))) (|Seq#Rank| T@@80 s@@28)))
 :qid |testbpl.1441:18|
 :skolemid |270|
 :pattern ( (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))))
)))
(assert (forall ((a@@65 T@U) (b@@43 T@U) (o@@37 T@U) (T@@81 T@T) ) (! (= (U_2_int (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@65 b@@43) o@@37)) (|Math#min| (U_2_int (MapType0Select T@@81 intType a@@65 o@@37)) (U_2_int (MapType0Select T@@81 intType b@@43 o@@37))))
 :qid |testbpl.1090:18|
 :skolemid |198|
 :pattern ( (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@65 b@@43) o@@37))
)))
(assert (forall ((t@@10 T@U) (u@@7 T@U) ) (! (= (Inv0_TMap (TMap t@@10 u@@7)) t@@10)
 :qid |testbpl.68:15|
 :skolemid |9|
 :pattern ( (TMap t@@10 u@@7))
)))
(assert (forall ((t@@11 T@U) (u@@8 T@U) ) (! (= (Inv1_TMap (TMap t@@11 u@@8)) u@@8)
 :qid |testbpl.70:15|
 :skolemid |10|
 :pattern ( (TMap t@@11 u@@8))
)))
(assert (forall ((t@@12 T@U) (u@@9 T@U) ) (! (= (Tag (TMap t@@12 u@@9)) TagMap)
 :qid |testbpl.72:15|
 :skolemid |11|
 :pattern ( (TMap t@@12 u@@9))
)))
(assert (forall ((t@@13 T@U) (u@@10 T@U) ) (! (= (Inv0_TIMap (TIMap t@@13 u@@10)) t@@13)
 :qid |testbpl.76:15|
 :skolemid |12|
 :pattern ( (TIMap t@@13 u@@10))
)))
(assert (forall ((t@@14 T@U) (u@@11 T@U) ) (! (= (Inv1_TIMap (TIMap t@@14 u@@11)) u@@11)
 :qid |testbpl.78:15|
 :skolemid |13|
 :pattern ( (TIMap t@@14 u@@11))
)))
(assert (forall ((t@@15 T@U) (u@@12 T@U) ) (! (= (Tag (TIMap t@@15 u@@12)) TagIMap)
 :qid |testbpl.80:15|
 :skolemid |14|
 :pattern ( (TIMap t@@15 u@@12))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$R@@6| T@U) ) (! (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@6|)) |#$T0@@1|)
 :qid |testbpl.2018:15|
 :skolemid |370|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@6|))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$R@@7| T@U) ) (! (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@7|)) |#$R@@7|)
 :qid |testbpl.2025:15|
 :skolemid |371|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@7|))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$R@@8| T@U) ) (! (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@8|)) |#$T0@@3|)
 :qid |testbpl.2245:15|
 :skolemid |401|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@8|))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$R@@9| T@U) ) (! (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@9|)) |#$R@@9|)
 :qid |testbpl.2253:15|
 :skolemid |402|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@9|))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$R@@10| T@U) ) (! (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@5| |#$R@@10|)) |#$T0@@5|)
 :qid |testbpl.2293:15|
 :skolemid |408|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@5| |#$R@@10|))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$R@@11| T@U) ) (! (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@6| |#$R@@11|)) |#$R@@11|)
 :qid |testbpl.2301:15|
 :skolemid |409|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@6| |#$R@@11|))
)))
(assert (forall ((|a#0#0#0| T@U) (|a#0#1#0| T@U) ) (! (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|)) |##_System._tuple#2._#Make2|)
 :qid |testbpl.2580:15|
 :skolemid |451|
 :pattern ( (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|))
)))
(assert (forall ((|_System._tuple#2$T0@@4| T@U) (|_System._tuple#2$T1@@4| T@U) ) (! (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|)) |_System._tuple#2$T0@@4|)
 :qid |testbpl.2614:15|
 :skolemid |456|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|))
)))
(assert (forall ((|_System._tuple#2$T0@@5| T@U) (|_System._tuple#2$T1@@5| T@U) ) (! (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|)) |_System._tuple#2$T1@@5|)
 :qid |testbpl.2622:15|
 :skolemid |457|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|))
)))
(assert (forall ((|a#4#0#0| T@U) (|a#4#1#0| T@U) ) (! (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|)) |a#4#0#0|)
 :qid |testbpl.2688:15|
 :skolemid |466|
 :pattern ( (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|))
)))
(assert (forall ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (! (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|)) |a#6#1#0|)
 :qid |testbpl.2698:15|
 :skolemid |468|
 :pattern ( (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))
)))
(assert (forall (($o@@3 T@U) ) (! ($Is refType $o@@3 Tclass._System.object?)
 :qid |testbpl.1849:15|
 :skolemid |350|
 :pattern ( ($Is refType $o@@3 Tclass._System.object?))
)))
(assert (forall ((v@@29 T@U) (t0@@33 T@U) (h@@19 T@U) ) (! (= ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@33) h@@19) (forall ((i@@13 Int) ) (!  (=> (and (<= 0 i@@13) (< i@@13 (|Seq#Length| BoxType v@@29))) ($IsAllocBox BoxType (|Seq#Index| BoxType v@@29 i@@13) t0@@33 h@@19))
 :qid |testbpl.368:19|
 :skolemid |72|
 :pattern ( (|Seq#Index| BoxType v@@29 i@@13))
)))
 :qid |testbpl.365:15|
 :skolemid |73|
 :pattern ( ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@33) h@@19))
)))
(assert (forall ((a@@66 T@U) (x@@24 T@U) (T@@82 T@T) ) (! (U_2_bool (MapType0Select T@@82 boolType (|Set#UnionOne| T@@82 a@@66 x@@24) x@@24))
 :qid |testbpl.812:18|
 :skolemid |131|
 :pattern ( (|Set#UnionOne| T@@82 a@@66 x@@24))
)))
(assert (forall ((a@@67 T@U) (x@@25 T@U) (T@@83 T@T) ) (! (U_2_bool (MapType0Select T@@83 boolType (|ISet#UnionOne| T@@83 a@@67 x@@25) x@@25))
 :qid |testbpl.923:18|
 :skolemid |157|
 :pattern ( (|ISet#UnionOne| T@@83 a@@67 x@@25))
)))
(assert  (and (forall ((t0@@34 T@T) (t1@@18 T@T) (t2@@0 T@T) (val@@7 T@U) (m@@30 T@U) (x0@@7 T@U) (x1@@2 T@U) ) (! (= (MapType3Select t0@@34 t1@@18 t2@@0 (MapType3Store t0@@34 t1@@18 t2@@0 m@@30 x0@@7 x1@@2 val@@7) x0@@7 x1@@2) val@@7)
 :qid |mapAx0:MapType3Select|
 :weight 0
)) (and (and (forall ((u0@@5 T@T) (u1@@3 T@T) (s0@@4 T@T) (t0@@35 T@T) (val@@8 T@U) (m@@31 T@U) (x0@@8 T@U) (x1@@3 T@U) (y0@@4 T@U) (y1@@1 T@U) ) (!  (or (= s0@@4 t0@@35) (= (MapType3Select t0@@35 u0@@5 u1@@3 (MapType3Store s0@@4 u0@@5 u1@@3 m@@31 x0@@8 x1@@3 val@@8) y0@@4 y1@@1) (MapType3Select t0@@35 u0@@5 u1@@3 m@@31 y0@@4 y1@@1)))
 :qid |mapAx1:MapType3Select:0|
 :weight 0
)) (forall ((u0@@6 T@T) (u1@@4 T@T) (s0@@5 T@T) (t0@@36 T@T) (val@@9 T@U) (m@@32 T@U) (x0@@9 T@U) (x1@@4 T@U) (y0@@5 T@U) (y1@@2 T@U) ) (!  (or (= x0@@9 y0@@5) (= (MapType3Select t0@@36 u0@@6 u1@@4 (MapType3Store s0@@5 u0@@6 u1@@4 m@@32 x0@@9 x1@@4 val@@9) y0@@5 y1@@2) (MapType3Select t0@@36 u0@@6 u1@@4 m@@32 y0@@5 y1@@2)))
 :qid |mapAx1:MapType3Select:1|
 :weight 0
))) (forall ((u0@@7 T@T) (u1@@5 T@T) (s0@@6 T@T) (t0@@37 T@T) (val@@10 T@U) (m@@33 T@U) (x0@@10 T@U) (x1@@5 T@U) (y0@@6 T@U) (y1@@3 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType3Select t0@@37 u0@@7 u1@@5 (MapType3Store s0@@6 u0@@7 u1@@5 m@@33 x0@@10 x1@@5 val@@10) y0@@6 y1@@3) (MapType3Select t0@@37 u0@@7 u1@@5 m@@33 y0@@6 y1@@3)))
 :qid |mapAx1:MapType3Select:2|
 :weight 0
)))))
(assert (forall ((|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ($o@@4 T@U) ($f T@U) (alpha@@0 T@T) ) (! (= (U_2_bool (MapType3Select alpha@@0 refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@4 $f))  (=> (and (or (not (= $o@@4 |l#0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) |l#1| $o@@4) |l#2|)))) |l#3|))
 :qid |testbpl.186:1|
 :skolemid |488|
 :pattern ( (MapType3Select alpha@@0 refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@4 $f))
)))
(assert (forall ((|l#0@@0| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ($o@@5 T@U) ($f@@0 T@U) (alpha@@1 T@T) ) (! (= (U_2_bool (MapType3Select alpha@@1 refType boolType (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@5 $f@@0))  (=> (and (or (not (= $o@@5 |l#0@@0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) |l#1@@0| $o@@5) |l#2@@0|)))) |l#3@@0|))
 :qid |testbpl.186:1|
 :skolemid |489|
 :pattern ( (MapType3Select alpha@@1 refType boolType (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@5 $f@@0))
)))
(assert (forall ((a@@68 T@U) (x@@26 T@U) (T@@84 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@84 boolType a@@68 x@@26)) (= (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@68 x@@26)) (|Set#Card| T@@84 a@@68)))
 :qid |testbpl.818:18|
 :skolemid |133|
 :pattern ( (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@68 x@@26)))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |testbpl.40:15|
 :skolemid |0|
 :pattern ( (TBitvector w))
)))
(assert (forall ((t@@16 T@U) ) (! (= (Inv0_TSet (TSet t@@16)) t@@16)
 :qid |testbpl.44:15|
 :skolemid |1|
 :pattern ( (TSet t@@16))
)))
(assert (forall ((t@@17 T@U) ) (! (= (Tag (TSet t@@17)) TagSet)
 :qid |testbpl.46:15|
 :skolemid |2|
 :pattern ( (TSet t@@17))
)))
(assert (forall ((t@@18 T@U) ) (! (= (Inv0_TISet (TISet t@@18)) t@@18)
 :qid |testbpl.50:15|
 :skolemid |3|
 :pattern ( (TISet t@@18))
)))
(assert (forall ((t@@19 T@U) ) (! (= (Tag (TISet t@@19)) TagISet)
 :qid |testbpl.52:15|
 :skolemid |4|
 :pattern ( (TISet t@@19))
)))
(assert (forall ((t@@20 T@U) ) (! (= (Inv0_TMultiSet (TMultiSet t@@20)) t@@20)
 :qid |testbpl.56:15|
 :skolemid |5|
 :pattern ( (TMultiSet t@@20))
)))
(assert (forall ((t@@21 T@U) ) (! (= (Tag (TMultiSet t@@21)) TagMultiSet)
 :qid |testbpl.58:15|
 :skolemid |6|
 :pattern ( (TMultiSet t@@21))
)))
(assert (forall ((t@@22 T@U) ) (! (= (Inv0_TSeq (TSeq t@@22)) t@@22)
 :qid |testbpl.62:15|
 :skolemid |7|
 :pattern ( (TSeq t@@22))
)))
(assert (forall ((t@@23 T@U) ) (! (= (Tag (TSeq t@@23)) TagSeq)
 :qid |testbpl.64:15|
 :skolemid |8|
 :pattern ( (TSeq t@@23))
)))
(assert (forall ((i@@14 Int) ) (! (= (FDim BoxType (IndexField i@@14)) 1)
 :qid |testbpl.606:15|
 :skolemid |102|
 :pattern ( (IndexField i@@14))
)))
(assert (forall ((i@@15 Int) ) (! (= (IndexField_Inverse BoxType (IndexField i@@15)) i@@15)
 :qid |testbpl.610:15|
 :skolemid |103|
 :pattern ( (IndexField i@@15))
)))
(assert (forall ((i@@16 Int) ) (! (= (q@Int (q@Real i@@16)) i@@16)
 :qid |testbpl.682:15|
 :skolemid |114|
 :pattern ( (q@Int (q@Real i@@16)))
)))
(assert (forall ((_System.array$arg@@6 T@U) ) (! (= (Tclass._System.array?_0 (Tclass._System.array? _System.array$arg@@6)) _System.array$arg@@6)
 :qid |testbpl.1903:15|
 :skolemid |356|
 :pattern ( (Tclass._System.array? _System.array$arg@@6))
)))
(assert (forall ((_System.array$arg@@7 T@U) ) (! (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@7)) _System.array$arg@@7)
 :qid |testbpl.1981:15|
 :skolemid |365|
 :pattern ( (Tclass._System.array _System.array$arg@@7))
)))
(assert (forall ((|#$R@@12| T@U) ) (! (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@12|)) |#$R@@12|)
 :qid |testbpl.2339:15|
 :skolemid |415|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@12|))
)))
(assert (forall ((|#$R@@13| T@U) ) (! (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@13|)) |#$R@@13|)
 :qid |testbpl.2517:15|
 :skolemid |442|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@13|))
)))
(assert (forall ((|#$R@@14| T@U) ) (! (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@14|)) |#$R@@14|)
 :qid |testbpl.2554:15|
 :skolemid |447|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@14|))
)))
(assert (forall ((x@@27 T@U) (T@@85 T@T) ) (! (= ($Unbox T@@85 ($Box T@@85 x@@27)) x@@27)
 :qid |testbpl.196:18|
 :skolemid |25|
 :pattern ( ($Box T@@85 x@@27))
)))
(assert (forall ((r@@7 T@U) (T@@86 T@T) ) (! (= (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@7)) 1)
 :qid |testbpl.802:18|
 :skolemid |129|
 :pattern ( (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@7)))
)))
(assert (forall ((t@@24 T@U) (T@@87 T@T) ) (! (= (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)) 1)
 :qid |testbpl.1211:18|
 :skolemid |224|
 :pattern ( (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)))
)))
(assert (forall ((v@@30 T@U) (t0@@38 T@U) (t1@@19 T@U) ) (! (= ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@38 t1@@19)) (forall ((bx@@21 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@21)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@21) t1@@19) ($IsBox BoxType bx@@21 t0@@38)))
 :qid |testbpl.307:19|
 :skolemid |54|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@21))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@21))
)))
 :qid |testbpl.304:15|
 :skolemid |55|
 :pattern ( ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@38 t1@@19)))
)))
(assert (forall ((v@@31 T@U) (t0@@39 T@U) (t1@@20 T@U) ) (! (= ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@39 t1@@20)) (forall ((bx@@22 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@22)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@22) t1@@20) ($IsBox BoxType bx@@22 t0@@39)))
 :qid |testbpl.321:19|
 :skolemid |57|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@22))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@22))
)))
 :qid |testbpl.318:15|
 :skolemid |58|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@39 t1@@20)))
)))
(assert (forall ((o@@38 T@U) (p@@5 T@U) ) (!  (and (and (and (=> (|ORD#Less| o@@38 p@@5) (or (not (= o@@38 p@@5)) (not true))) (=> (and (|ORD#IsNat| o@@38) (not (|ORD#IsNat| p@@5))) (|ORD#Less| o@@38 p@@5))) (=> (and (|ORD#IsNat| o@@38) (|ORD#IsNat| p@@5)) (= (|ORD#Less| o@@38 p@@5) (< (|ORD#Offset| o@@38) (|ORD#Offset| p@@5))))) (=> (and (|ORD#Less| o@@38 p@@5) (|ORD#IsNat| p@@5)) (|ORD#IsNat| o@@38)))
 :qid |testbpl.488:15|
 :skolemid |87|
 :pattern ( (|ORD#Less| o@@38 p@@5))
)))
(assert (forall ((h@@20 T@U) (i@@17 Int) (v@@32 T@U) (a@@69 T@U) ) (!  (=> (and (<= 0 i@@17) (< i@@17 (_System.array.Length a@@69))) (= (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@20 a@@69 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@20 a@@69) (IndexField i@@17) ($Box BoxType v@@32))) a@@69) (|Seq#Update| BoxType (|Seq#FromArray| h@@20 a@@69) i@@17 v@@32)))
 :qid |testbpl.1389:15|
 :skolemid |260|
 :pattern ( (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@20 a@@69 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@20 a@@69) (IndexField i@@17) ($Box BoxType v@@32))) a@@69))
)))
(assert (forall ((r@@8 T@U) (T@@88 T@T) ) (! (U_2_bool (MapType0Select T@@88 boolType (|Set#Singleton| T@@88 r@@8) r@@8))
 :qid |testbpl.796:18|
 :skolemid |127|
 :pattern ( (|Set#Singleton| T@@88 r@@8))
)))
(assert (forall ((x@@28 Int) (y@@11 Int) ) (! (= (INTERNAL_lt_boogie x@@28 y@@11) (< x@@28 y@@11))
 :qid |testbpl.1762:15|
 :skolemid |337|
 :pattern ( (INTERNAL_lt_boogie x@@28 y@@11))
)))
(assert (forall ((x@@29 Int) (y@@12 Int) ) (! (= (INTERNAL_gt_boogie x@@29 y@@12) (> x@@29 y@@12))
 :qid |testbpl.1776:15|
 :skolemid |339|
 :pattern ( (INTERNAL_gt_boogie x@@29 y@@12))
)))
(assert (forall ((m@@34 T@U) (n@@13 T@U) (u@@13 T@U) (U@@25 T@T) (V@@25 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13)) (and (=> (not (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13))) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 m@@34) u@@13))) (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13)) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 n@@13) u@@13)))))
 :qid |testbpl.1567:20|
 :skolemid |297|
 :pattern ( (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13))
)))
(assert (forall ((m@@35 T@U) (n@@14 T@U) (u@@14 T@U) (U@@26 T@T) (V@@26 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14)) (and (=> (not (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14))) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 m@@35) u@@14))) (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14)) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 n@@14) u@@14)))))
 :qid |testbpl.1706:20|
 :skolemid |329|
 :pattern ( (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14))
)))
(assert (forall ((s@@29 T@U) (i@@18 Int) (v@@33 T@U) (x@@30 T@U) (T@@89 T@T) ) (!  (=> (and (<= 0 i@@18) (< i@@18 (|Seq#Length| T@@89 s@@29))) (= (U_2_int (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30)) (U_2_int (MapType0Select T@@89 intType (|MultiSet#Union| T@@89 (|MultiSet#Difference| T@@89 (|MultiSet#FromSeq| T@@89 s@@29) (|MultiSet#Singleton| T@@89 (|Seq#Index| T@@89 s@@29 i@@18))) (|MultiSet#Singleton| T@@89 v@@33)) x@@30))))
 :qid |testbpl.1180:18|
 :skolemid |218|
 :pattern ( (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30))
)))
(assert (forall ((_System.array$arg@@8 T@U) ($h@@11 T@U) ($o@@6 T@U) ($i0 Int) ) (!  (=> (and (and (and (and (and ($IsGoodHeap $h@@11) (or (not (= $o@@6 null)) (not true))) (= (dtype $o@@6) (Tclass._System.array? _System.array$arg@@8))) (<= 0 $i0)) (< $i0 (_System.array.Length $o@@6))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) alloc)))) ($IsAllocBox BoxType ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) (IndexField $i0))) _System.array$arg@@8 $h@@11))
 :qid |testbpl.1928:15|
 :skolemid |359|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) (IndexField $i0))) (Tclass._System.array? _System.array$arg@@8))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (! (< (BoxRank |a#5#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)))
 :qid |testbpl.2693:15|
 :skolemid |467|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (! (< (BoxRank |a#7#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|)))
 :qid |testbpl.2703:15|
 :skolemid |469|
 :pattern ( (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|))
)))
(assert (forall ((a@@70 T@U) (b@@44 T@U) (T@@90 T@T) ) (! (= (|Set#Union| T@@90 a@@70 (|Set#Union| T@@90 a@@70 b@@44)) (|Set#Union| T@@90 a@@70 b@@44))
 :qid |testbpl.856:18|
 :skolemid |141|
 :pattern ( (|Set#Union| T@@90 a@@70 (|Set#Union| T@@90 a@@70 b@@44)))
)))
(assert (forall ((a@@71 T@U) (b@@45 T@U) (T@@91 T@T) ) (! (= (|Set#Intersection| T@@91 a@@71 (|Set#Intersection| T@@91 a@@71 b@@45)) (|Set#Intersection| T@@91 a@@71 b@@45))
 :qid |testbpl.864:18|
 :skolemid |143|
 :pattern ( (|Set#Intersection| T@@91 a@@71 (|Set#Intersection| T@@91 a@@71 b@@45)))
)))
(assert (forall ((a@@72 T@U) (b@@46 T@U) (T@@92 T@T) ) (! (= (|ISet#Union| T@@92 a@@72 (|ISet#Union| T@@92 a@@72 b@@46)) (|ISet#Union| T@@92 a@@72 b@@46))
 :qid |testbpl.959:18|
 :skolemid |165|
 :pattern ( (|ISet#Union| T@@92 a@@72 (|ISet#Union| T@@92 a@@72 b@@46)))
)))
(assert (forall ((a@@73 T@U) (b@@47 T@U) (T@@93 T@T) ) (! (= (|ISet#Intersection| T@@93 a@@73 (|ISet#Intersection| T@@93 a@@73 b@@47)) (|ISet#Intersection| T@@93 a@@73 b@@47))
 :qid |testbpl.967:18|
 :skolemid |167|
 :pattern ( (|ISet#Intersection| T@@93 a@@73 (|ISet#Intersection| T@@93 a@@73 b@@47)))
)))
(assert (forall ((a@@74 T@U) (b@@48 T@U) (T@@94 T@T) ) (! (= (|MultiSet#Intersection| T@@94 a@@74 (|MultiSet#Intersection| T@@94 a@@74 b@@48)) (|MultiSet#Intersection| T@@94 a@@74 b@@48))
 :qid |testbpl.1099:18|
 :skolemid |200|
 :pattern ( (|MultiSet#Intersection| T@@94 a@@74 (|MultiSet#Intersection| T@@94 a@@74 b@@48)))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$R@@15| T@U) (|f#0@@3| T@U) ) (! (= ($Is HandleTypeType |f#0@@3| (Tclass._System.___hTotalFunc1 |#$T0@@7| |#$R@@15|))  (and ($Is HandleTypeType |f#0@@3| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@15|)) (forall ((|x0#0| T@U) ) (!  (=> ($IsBox BoxType |x0#0| |#$T0@@7|) (Requires1 |#$T0@@7| |#$R@@15| $OneHeap |f#0@@3| |x0#0|))
 :qid |testbpl.2317:19|
 :skolemid |411|
))))
 :qid |testbpl.2313:15|
 :skolemid |412|
 :pattern ( ($Is HandleTypeType |f#0@@3| (Tclass._System.___hTotalFunc1 |#$T0@@7| |#$R@@15|)))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$R@@16| T@U) (|f#0@@4| T@U) ) (! (= ($Is HandleTypeType |f#0@@4| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@16|))  (and ($Is HandleTypeType |f#0@@4| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@16|)) (forall ((|x0#0@@0| T@U) ) (!  (=> ($IsBox BoxType |x0#0@@0| |#$T0@@8|) (|Set#Equal| BoxType (Reads1 |#$T0@@8| |#$R@@16| $OneHeap |f#0@@4| |x0#0@@0|) (|Set#Empty| BoxType)))
 :qid |testbpl.2270:19|
 :skolemid |404|
))))
 :qid |testbpl.2266:15|
 :skolemid |405|
 :pattern ( ($Is HandleTypeType |f#0@@4| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@16|)))
)))
(assert (forall ((m@@36 T@U) (u@@15 T@U) (|u'| T@U) (v@@34 T@U) (U@@27 T@T) (V@@27 T@T) ) (!  (and (=> (= |u'| u@@15) (and (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|)) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|) v@@34))) (=> (or (not (= |u'| u@@15)) (not true)) (and (= (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|)) (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 m@@36) |u'|))) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|) (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 m@@36) |u'|)))))
 :qid |testbpl.1545:20|
 :skolemid |293|
 :pattern ( (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|))
 :pattern ( (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|))
)))
(assert (forall ((m@@37 T@U) (u@@16 T@U) (|u'@@0| T@U) (v@@35 T@U) (U@@28 T@T) (V@@28 T@T) ) (!  (and (=> (= |u'@@0| u@@16) (and (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|)) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|) v@@35))) (=> (or (not (= |u'@@0| u@@16)) (not true)) (and (= (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|)) (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 m@@37) |u'@@0|))) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|) (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 m@@37) |u'@@0|)))))
 :qid |testbpl.1677:20|
 :skolemid |323|
 :pattern ( (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|))
 :pattern ( (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|))
)))
(assert (forall ((f@@19 T@U) (ly@@0 T@U) (A@@0 T@T) ) (! (= (AtLayer A@@0 f@@19 ($LS ly@@0)) (AtLayer A@@0 f@@19 ly@@0))
 :qid |testbpl.593:18|
 :skolemid |101|
 :pattern ( (AtLayer A@@0 f@@19 ($LS ly@@0)))
)))
(assert (forall ((n@@15 Int) ) (!  (=> (or (and (<= 0 n@@15) (< n@@15 55296)) (and (<= 57344 n@@15) (< n@@15 1114112))) (= (|char#ToInt| (|char#FromInt| n@@15)) n@@15))
 :qid |testbpl.162:15|
 :skolemid |21|
 :pattern ( (|char#FromInt| n@@15))
)))
(assert (forall ((bx@@23 T@U) (s@@30 T@U) (t@@25 T@U) ) (!  (=> ($IsBox BoxType bx@@23 (TMap s@@30 t@@25)) (and (= ($Box (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@23)) bx@@23) ($Is (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@23) (TMap s@@30 t@@25))))
 :qid |testbpl.247:15|
 :skolemid |35|
 :pattern ( ($IsBox BoxType bx@@23 (TMap s@@30 t@@25)))
)))
(assert (forall ((bx@@24 T@U) (s@@31 T@U) (t@@26 T@U) ) (!  (=> ($IsBox BoxType bx@@24 (TIMap s@@31 t@@26)) (and (= ($Box (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@24)) bx@@24) ($Is (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@24) (TIMap s@@31 t@@26))))
 :qid |testbpl.252:15|
 :skolemid |36|
 :pattern ( ($IsBox BoxType bx@@24 (TIMap s@@31 t@@26)))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$R@@17| T@U) (bx@@25 T@U) ) (!  (=> ($IsBox BoxType bx@@25 (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@25)) bx@@25) ($Is HandleTypeType ($Unbox HandleTypeType bx@@25) (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|))))
 :qid |testbpl.2030:15|
 :skolemid |372|
 :pattern ( ($IsBox BoxType bx@@25 (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|)))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$R@@18| T@U) (bx@@26 T@U) ) (!  (=> ($IsBox BoxType bx@@26 (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@26)) bx@@26) ($Is HandleTypeType ($Unbox HandleTypeType bx@@26) (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|))))
 :qid |testbpl.2259:15|
 :skolemid |403|
 :pattern ( ($IsBox BoxType bx@@26 (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|)))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$R@@19| T@U) (bx@@27 T@U) ) (!  (=> ($IsBox BoxType bx@@27 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@27)) bx@@27) ($Is HandleTypeType ($Unbox HandleTypeType bx@@27) (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|))))
 :qid |testbpl.2306:15|
 :skolemid |410|
 :pattern ( ($IsBox BoxType bx@@27 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|)))
)))
(assert (forall ((|_System._tuple#2$T0@@6| T@U) (|_System._tuple#2$T1@@6| T@U) (bx@@28 T@U) ) (!  (=> ($IsBox BoxType bx@@28 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|)) (and (= ($Box DatatypeTypeType ($Unbox DatatypeTypeType bx@@28)) bx@@28) ($Is DatatypeTypeType ($Unbox DatatypeTypeType bx@@28) (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|))))
 :qid |testbpl.2628:15|
 :skolemid |458|
 :pattern ( ($IsBox BoxType bx@@28 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|)))
)))
(assert (forall ((a@@75 T@U) (b@@49 T@U) (T@@95 T@T) ) (! (= (|MultiSet#Disjoint| T@@95 a@@75 b@@49) (forall ((o@@39 T@U) ) (!  (or (= (U_2_int (MapType0Select T@@95 intType a@@75 o@@39)) 0) (= (U_2_int (MapType0Select T@@95 intType b@@49 o@@39)) 0))
 :qid |testbpl.1144:19|
 :skolemid |209|
 :pattern ( (MapType0Select T@@95 intType a@@75 o@@39))
 :pattern ( (MapType0Select T@@95 intType b@@49 o@@39))
)))
 :qid |testbpl.1141:18|
 :skolemid |210|
 :pattern ( (|MultiSet#Disjoint| T@@95 a@@75 b@@49))
)))
(assert (forall ((o@@40 T@U) (T@@96 T@T) ) (!  (not (U_2_bool (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@40)))
 :qid |testbpl.787:18|
 :skolemid |124|
 :pattern ( (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@40))
)))
(assert (forall ((o@@41 T@U) (T@@97 T@T) ) (!  (not (U_2_bool (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@41)))
 :qid |testbpl.915:18|
 :skolemid |155|
 :pattern ( (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@41))
)))
(assert (forall ((t0@@40 T@U) (t1@@21 T@U) (heap@@7 T@U) (f@@20 T@U) (bx0@@12 T@U) ) (!  (=> (and (and ($IsGoodHeap heap@@7) ($IsBox BoxType bx0@@12 t0@@40)) ($Is HandleTypeType f@@20 (Tclass._System.___hFunc1 t0@@40 t1@@21))) (= (|Set#Equal| BoxType (Reads1 t0@@40 t1@@21 $OneHeap f@@20 bx0@@12) (|Set#Empty| BoxType)) (|Set#Equal| BoxType (Reads1 t0@@40 t1@@21 heap@@7 f@@20 bx0@@12) (|Set#Empty| BoxType))))
 :qid |testbpl.2174:15|
 :skolemid |388|
 :pattern ( (Reads1 t0@@40 t1@@21 $OneHeap f@@20 bx0@@12) ($IsGoodHeap heap@@7))
 :pattern ( (Reads1 t0@@40 t1@@21 heap@@7 f@@20 bx0@@12))
)))
(assert (forall ((h0@@9 T@U) (h1@@9 T@U) (a@@76 T@U) ) (!  (=> (and (and (and ($IsGoodHeap h0@@9) ($IsGoodHeap h1@@9)) ($HeapSucc h0@@9 h1@@9)) (= (MapType0Select refType (MapType1Type BoxType) h0@@9 a@@76) (MapType0Select refType (MapType1Type BoxType) h1@@9 a@@76))) (= (|Seq#FromArray| h0@@9 a@@76) (|Seq#FromArray| h1@@9 a@@76)))
 :qid |testbpl.1384:15|
 :skolemid |259|
 :pattern ( (|Seq#FromArray| h1@@9 a@@76) ($HeapSucc h0@@9 h1@@9))
)))
(assert (forall ((s@@32 T@U) (i@@19 Int) (v@@36 T@U) (T@@98 T@T) ) (!  (=> (and (<= 0 i@@19) (< i@@19 (|Seq#Length| T@@98 s@@32))) (= (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)) (|Seq#Length| T@@98 s@@32)))
 :qid |testbpl.1272:18|
 :skolemid |234|
 :pattern ( (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)))
)))
(assert (forall ((x@@31 Int) (y@@13 Int) ) (! (= (INTERNAL_mod_boogie x@@31 y@@13) (mod x@@31 y@@13))
 :qid |testbpl.1755:15|
 :skolemid |336|
 :pattern ( (INTERNAL_mod_boogie x@@31 y@@13))
)))
(assert (forall ((x@@32 Int) (y@@14 Int) ) (! (= (Mod x@@32 y@@14) (mod x@@32 y@@14))
 :qid |testbpl.1800:15|
 :skolemid |343|
 :pattern ( (Mod x@@32 y@@14))
)))
(assert (forall ((f@@21 T@U) (t0@@41 T@U) (h@@21 T@U) ) (!  (=> ($IsGoodHeap h@@21) (= ($IsAlloc HandleTypeType f@@21 (Tclass._System.___hFunc0 t0@@41) h@@21)  (=> (Requires0 t0@@41 h@@21 f@@21) (forall ((r@@9 T@U) ) (!  (=> (and (or (not (= r@@9 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@41 h@@21 f@@21) ($Box refType r@@9)))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@21 r@@9) alloc))))
 :qid |testbpl.2493:22|
 :skolemid |438|
 :pattern ( (MapType0Select BoxType boolType (Reads0 t0@@41 h@@21 f@@21) ($Box refType r@@9)))
)))))
 :qid |testbpl.2488:15|
 :skolemid |439|
 :pattern ( ($IsAlloc HandleTypeType f@@21 (Tclass._System.___hFunc0 t0@@41) h@@21))
)))
(assert (forall ((a@@77 T@U) (b@@50 T@U) (t0@@42 T@U) (t1@@22 T@U) ) (!  (=> (forall ((bx@@29 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@77 bx@@29)) (and ($IsBox BoxType bx@@29 t0@@42) ($IsBox BoxType (MapType0Select BoxType BoxType b@@50 bx@@29) t1@@22)))
 :qid |testbpl.1540:11|
 :skolemid |291|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@77 b@@50 (TMap t0@@42 t1@@22)) (TMap t0@@42 t1@@22)))
 :qid |testbpl.1538:15|
 :skolemid |292|
 :pattern ( (|Map#Glue| BoxType BoxType a@@77 b@@50 (TMap t0@@42 t1@@22)))
)))
(assert (forall ((a@@78 T@U) (b@@51 T@U) (t0@@43 T@U) (t1@@23 T@U) ) (!  (=> (forall ((bx@@30 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@78 bx@@30)) (and ($IsBox BoxType bx@@30 t0@@43) ($IsBox BoxType (MapType0Select BoxType BoxType b@@51 bx@@30) t1@@23)))
 :qid |testbpl.1672:11|
 :skolemid |321|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@78 b@@51 (TIMap t0@@43 t1@@23)) (TIMap t0@@43 t1@@23)))
 :qid |testbpl.1670:15|
 :skolemid |322|
 :pattern ( (|IMap#Glue| BoxType BoxType a@@78 b@@51 (TIMap t0@@43 t1@@23)))
)))
(assert (forall ((|#$R@@20| T@U) (|f#0@@5| T@U) ) (! (= ($Is HandleTypeType |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@20|))  (and ($Is HandleTypeType |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@20|)) (Requires0 |#$R@@20| $OneHeap |f#0@@5|)))
 :qid |testbpl.2566:15|
 :skolemid |449|
 :pattern ( ($Is HandleTypeType |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@20|)))
)))
(assert (forall ((h@@22 T@U) (a@@79 T@U) ) (! (= (|Seq#Length| BoxType (|Seq#FromArray| h@@22 a@@79)) (_System.array.Length a@@79))
 :qid |testbpl.1373:15|
 :skolemid |256|
 :pattern ( (|Seq#Length| BoxType (|Seq#FromArray| h@@22 a@@79)))
)))
(assert (forall ((a@@80 T@U) (b@@52 T@U) ) (!  (and (= (TypeTupleCar (TypeTuple a@@80 b@@52)) a@@80) (= (TypeTupleCdr (TypeTuple a@@80 b@@52)) b@@52))
 :qid |testbpl.428:15|
 :skolemid |80|
 :pattern ( (TypeTuple a@@80 b@@52))
)))
(assert (forall ((f@@22 T@U) (i@@20 Int) ) (!  (and (= (MultiIndexField_Inverse0 BoxType (MultiIndexField f@@22 i@@20)) f@@22) (= (MultiIndexField_Inverse1 BoxType (MultiIndexField f@@22 i@@20)) i@@20))
 :qid |testbpl.622:15|
 :skolemid |105|
 :pattern ( (MultiIndexField f@@22 i@@20))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$R@@21| T@U) ) (!  (and (= (Tag (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|)) Tagclass._System.___hFunc1) (= (TagFamily (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|)) |tytagFamily$_#Func1|))
 :qid |testbpl.2010:15|
 :skolemid |369|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$R@@22| T@U) ) (!  (and (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|)) Tagclass._System.___hPartialFunc1) (= (TagFamily (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|)) |tytagFamily$_#PartialFunc1|))
 :qid |testbpl.2235:15|
 :skolemid |400|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$R@@23| T@U) ) (!  (and (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|)) Tagclass._System.___hTotalFunc1) (= (TagFamily (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|)) |tytagFamily$_#TotalFunc1|))
 :qid |testbpl.2285:15|
 :skolemid |407|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|))
)))
(assert (forall ((|_System._tuple#2$T0@@7| T@U) (|_System._tuple#2$T1@@7| T@U) ) (!  (and (= (Tag (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|)) Tagclass._System.Tuple2) (= (TagFamily (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|)) |tytagFamily$_tuple#2|))
 :qid |testbpl.2604:15|
 :skolemid |455|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|))
)))
(assert (forall ((s@@33 T@U) (val@@11 T@U) (T@@99 T@T) ) (!  (and (= (|Seq#Build_inv0| T@@99 (|Seq#Build| T@@99 s@@33 val@@11)) s@@33) (= (|Seq#Build_inv1| T@@99 (|Seq#Build| T@@99 s@@33 val@@11)) val@@11))
 :qid |testbpl.1221:18|
 :skolemid |225|
 :pattern ( (|Seq#Build| T@@99 s@@33 val@@11))
)))
(assert (forall ((m@@38 T@U) (|m'@@2| T@U) (U@@29 T@T) (V@@29 T@T) ) (! (= (|Map#Equal| U@@29 V@@29 m@@38 |m'@@2|)  (and (forall ((u@@17 T@U) ) (! (= (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@38) u@@17)) (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 |m'@@2|) u@@17)))
 :qid |testbpl.1589:19|
 :skolemid |300|
)) (forall ((u@@18 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@38) u@@18)) (= (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 m@@38) u@@18) (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 |m'@@2|) u@@18)))
 :qid |testbpl.1590:19|
 :skolemid |301|
))))
 :qid |testbpl.1586:20|
 :skolemid |302|
 :pattern ( (|Map#Equal| U@@29 V@@29 m@@38 |m'@@2|))
)))
(assert (forall ((m@@39 T@U) (|m'@@3| T@U) (U@@30 T@T) (V@@30 T@T) ) (! (= (|IMap#Equal| U@@30 V@@30 m@@39 |m'@@3|)  (and (forall ((u@@19 T@U) ) (! (= (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@39) u@@19)) (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 |m'@@3|) u@@19)))
 :qid |testbpl.1692:19|
 :skolemid |324|
)) (forall ((u@@20 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@39) u@@20)) (= (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 m@@39) u@@20) (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 |m'@@3|) u@@20)))
 :qid |testbpl.1693:19|
 :skolemid |325|
))))
 :qid |testbpl.1689:20|
 :skolemid |326|
 :pattern ( (|IMap#Equal| U@@30 V@@30 m@@39 |m'@@3|))
)))
(assert (forall ((o@@42 T@U) (m@@40 Int) (n@@16 Int) ) (!  (=> (and (<= 0 m@@40) (<= 0 n@@16)) (= (|ORD#Plus| (|ORD#Plus| o@@42 (|ORD#FromNat| m@@40)) (|ORD#FromNat| n@@16)) (|ORD#Plus| o@@42 (|ORD#FromNat| (+ m@@40 n@@16)))))
 :qid |testbpl.543:15|
 :skolemid |96|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@42 (|ORD#FromNat| m@@40)) (|ORD#FromNat| n@@16)))
)))
(assert (forall ((x@@33 Int) (y@@15 Int) ) (! (= (INTERNAL_le_boogie x@@33 y@@15) (<= x@@33 y@@15))
 :qid |testbpl.1769:15|
 :skolemid |338|
 :pattern ( (INTERNAL_le_boogie x@@33 y@@15))
)))
(assert (forall ((x@@34 Int) (y@@16 Int) ) (! (= (INTERNAL_ge_boogie x@@34 y@@16) (>= x@@34 y@@16))
 :qid |testbpl.1783:15|
 :skolemid |340|
 :pattern ( (INTERNAL_ge_boogie x@@34 y@@16))
)))
(assert (forall ((x@@35 Int) (y@@17 Int) ) (! (= (INTERNAL_sub_boogie x@@35 y@@17) (- x@@35 y@@17))
 :qid |testbpl.1734:15|
 :skolemid |333|
 :pattern ( (INTERNAL_sub_boogie x@@35 y@@17))
)))
(assert (forall ((x@@36 Int) (y@@18 Int) ) (! (= (Sub x@@36 y@@18) (- x@@36 y@@18))
 :qid |testbpl.1810:15|
 :skolemid |345|
 :pattern ( (Sub x@@36 y@@18))
)))
(assert (forall ((x@@37 Int) (y@@19 Int) ) (! (= (INTERNAL_add_boogie x@@37 y@@19) (+ x@@37 y@@19))
 :qid |testbpl.1727:15|
 :skolemid |332|
 :pattern ( (INTERNAL_add_boogie x@@37 y@@19))
)))
(assert (forall ((x@@38 Int) (y@@20 Int) ) (! (= (Add x@@38 y@@20) (+ x@@38 y@@20))
 :qid |testbpl.1805:15|
 :skolemid |344|
 :pattern ( (Add x@@38 y@@20))
)))
(assert (forall ((x@@39 Int) (y@@21 Int) ) (! (= (INTERNAL_mul_boogie x@@39 y@@21) (* x@@39 y@@21))
 :qid |testbpl.1741:15|
 :skolemid |334|
 :pattern ( (INTERNAL_mul_boogie x@@39 y@@21))
)))
(assert (forall ((x@@40 Int) (y@@22 Int) ) (! (= (Mul x@@40 y@@22) (* x@@40 y@@22))
 :qid |testbpl.1790:15|
 :skolemid |341|
 :pattern ( (Mul x@@40 y@@22))
)))
(assert (forall ((d@@9 T@U) ) (! (= (BoxRank ($Box DatatypeTypeType d@@9)) (DtRank d@@9))
 :qid |testbpl.456:15|
 :skolemid |83|
 :pattern ( (BoxRank ($Box DatatypeTypeType d@@9)))
)))
(assert (forall ((r@@10 T@U) (T@@100 T@T) ) (! (= (|MultiSet#Singleton| T@@100 r@@10) (|MultiSet#UnionOne| T@@100 (|MultiSet#Empty| T@@100) r@@10))
 :qid |testbpl.1052:18|
 :skolemid |190|
 :pattern ( (|MultiSet#Singleton| T@@100 r@@10))
)))
(assert (forall ((s@@34 T@U) (T@@101 T@T) ) (! (= (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)) (|Set#Card| T@@101 s@@34))
 :qid |testbpl.1153:18|
 :skolemid |212|
 :pattern ( (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)))
)))
(assert (forall ((s@@35 T@U) (T@@102 T@T) ) (! (= (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)) (|Seq#Length| T@@102 s@@35))
 :qid |testbpl.1167:18|
 :skolemid |215|
 :pattern ( (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)))
)))
(assert (forall ((m@@41 T@U) (U@@31 T@T) (V@@31 T@T) ) (! (= (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@41)) (|Map#Card| U@@31 V@@31 m@@41))
 :qid |testbpl.1486:20|
 :skolemid |282|
 :pattern ( (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@41)))
 :pattern ( (|Map#Card| U@@31 V@@31 m@@41))
)))
(assert (forall ((m@@42 T@U) (U@@32 T@T) (V@@32 T@T) ) (! (= (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@42)) (|Map#Card| U@@32 V@@32 m@@42))
 :qid |testbpl.1494:20|
 :skolemid |284|
 :pattern ( (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@42)))
 :pattern ( (|Map#Card| U@@32 V@@32 m@@42))
)))
(assert (forall ((m@@43 T@U) (U@@33 T@T) (V@@33 T@T) ) (! (<= (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@43)) (|Map#Card| U@@33 V@@33 m@@43))
 :qid |testbpl.1490:20|
 :skolemid |283|
 :pattern ( (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@43)))
 :pattern ( (|Map#Card| U@@33 V@@33 m@@43))
)))
(assert (forall ((s@@36 T@U) (n@@17 Int) (x@@41 T@U) (T@@103 T@T) ) (! (= (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41) (exists ((i@@21 Int) ) (!  (and (and (and (<= 0 n@@17) (<= n@@17 i@@21)) (< i@@21 (|Seq#Length| T@@103 s@@36))) (= (|Seq#Index| T@@103 s@@36 i@@21) x@@41))
 :qid |testbpl.1314:19|
 :skolemid |243|
 :pattern ( (|Seq#Index| T@@103 s@@36 i@@21))
)))
 :qid |testbpl.1311:18|
 :skolemid |244|
 :pattern ( (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41))
)))
(assert (forall ((a@@81 Int) (b@@53 Int) ) (! (= (<= a@@81 b@@53) (= (|Math#min| a@@81 b@@53) a@@81))
 :qid |testbpl.1005:15|
 :skolemid |177|
 :pattern ( (|Math#min| a@@81 b@@53))
)))
(assert (forall ((a@@82 Int) (b@@54 Int) ) (! (= (<= b@@54 a@@82) (= (|Math#min| a@@82 b@@54) b@@54))
 :qid |testbpl.1007:15|
 :skolemid |178|
 :pattern ( (|Math#min| a@@82 b@@54))
)))
(assert (forall ((f@@23 T@U) (t0@@44 T@U) ) (! (= ($Is HandleTypeType f@@23 (Tclass._System.___hFunc0 t0@@44)) (forall ((h@@23 T@U) ) (!  (=> (and ($IsGoodHeap h@@23) (Requires0 t0@@44 h@@23 f@@23)) ($IsBox BoxType (Apply0 t0@@44 h@@23 f@@23) t0@@44))
 :qid |testbpl.2476:19|
 :skolemid |434|
 :pattern ( (Apply0 t0@@44 h@@23 f@@23))
)))
 :qid |testbpl.2473:15|
 :skolemid |435|
 :pattern ( ($Is HandleTypeType f@@23 (Tclass._System.___hFunc0 t0@@44)))
)))
(assert (forall ((o@@43 T@U) (m@@44 Int) (n@@18 Int) ) (!  (=> (and (and (<= 0 m@@44) (<= 0 n@@18)) (<= n@@18 (+ (|ORD#Offset| o@@43) m@@44))) (and (=> (<= 0 (- m@@44 n@@18)) (= (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)) (|ORD#Plus| o@@43 (|ORD#FromNat| (- m@@44 n@@18))))) (=> (<= (- m@@44 n@@18) 0) (= (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)) (|ORD#Minus| o@@43 (|ORD#FromNat| (- n@@18 m@@44)))))))
 :qid |testbpl.555:15|
 :skolemid |98|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)))
)))
(assert (forall ((o@@44 T@U) (m@@45 Int) (n@@19 Int) ) (!  (=> (and (and (<= 0 m@@45) (<= 0 n@@19)) (<= n@@19 (+ (|ORD#Offset| o@@44) m@@45))) (and (=> (<= 0 (- m@@45 n@@19)) (= (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)) (|ORD#Minus| o@@44 (|ORD#FromNat| (- m@@45 n@@19))))) (=> (<= (- m@@45 n@@19) 0) (= (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)) (|ORD#Plus| o@@44 (|ORD#FromNat| (- n@@19 m@@45)))))))
 :qid |testbpl.565:15|
 :skolemid |99|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)))
)))
(assert (forall ((bx@@31 T@U) ) (!  (=> ($IsBox BoxType bx@@31 (TBitvector 0)) (and (= ($Box intType ($Unbox intType bx@@31)) bx@@31) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@31) (TBitvector 0))))
 :qid |testbpl.221:15|
 :skolemid |30|
 :pattern ( ($IsBox BoxType bx@@31 (TBitvector 0)))
)))
(assert (forall ((bx@@32 T@U) (t@@27 T@U) ) (!  (=> ($IsBox BoxType bx@@32 (TSet t@@27)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@32)) bx@@32) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@32) (TSet t@@27))))
 :qid |testbpl.226:15|
 :skolemid |31|
 :pattern ( ($IsBox BoxType bx@@32 (TSet t@@27)))
)))
(assert (forall ((bx@@33 T@U) (t@@28 T@U) ) (!  (=> ($IsBox BoxType bx@@33 (TISet t@@28)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@33)) bx@@33) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@33) (TISet t@@28))))
 :qid |testbpl.231:15|
 :skolemid |32|
 :pattern ( ($IsBox BoxType bx@@33 (TISet t@@28)))
)))
(assert (forall ((bx@@34 T@U) (t@@29 T@U) ) (!  (=> ($IsBox BoxType bx@@34 (TMultiSet t@@29)) (and (= ($Box (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@34)) bx@@34) ($Is (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@34) (TMultiSet t@@29))))
 :qid |testbpl.236:15|
 :skolemid |33|
 :pattern ( ($IsBox BoxType bx@@34 (TMultiSet t@@29)))
)))
(assert (forall ((bx@@35 T@U) (t@@30 T@U) ) (!  (=> ($IsBox BoxType bx@@35 (TSeq t@@30)) (and (= ($Box (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@35)) bx@@35) ($Is (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@35) (TSeq t@@30))))
 :qid |testbpl.242:15|
 :skolemid |34|
 :pattern ( ($IsBox BoxType bx@@35 (TSeq t@@30)))
)))
(assert (forall ((_System.array$arg@@9 T@U) (bx@@36 T@U) ) (!  (=> ($IsBox BoxType bx@@36 (Tclass._System.array? _System.array$arg@@9)) (and (= ($Box refType ($Unbox refType bx@@36)) bx@@36) ($Is refType ($Unbox refType bx@@36) (Tclass._System.array? _System.array$arg@@9))))
 :qid |testbpl.1909:15|
 :skolemid |357|
 :pattern ( ($IsBox BoxType bx@@36 (Tclass._System.array? _System.array$arg@@9)))
)))
(assert (forall ((_System.array$arg@@10 T@U) (bx@@37 T@U) ) (!  (=> ($IsBox BoxType bx@@37 (Tclass._System.array _System.array$arg@@10)) (and (= ($Box refType ($Unbox refType bx@@37)) bx@@37) ($Is refType ($Unbox refType bx@@37) (Tclass._System.array _System.array$arg@@10))))
 :qid |testbpl.1987:15|
 :skolemid |366|
 :pattern ( ($IsBox BoxType bx@@37 (Tclass._System.array _System.array$arg@@10)))
)))
(assert (forall ((|#$R@@24| T@U) (bx@@38 T@U) ) (!  (=> ($IsBox BoxType bx@@38 (Tclass._System.___hFunc0 |#$R@@24|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@38)) bx@@38) ($Is HandleTypeType ($Unbox HandleTypeType bx@@38) (Tclass._System.___hFunc0 |#$R@@24|))))
 :qid |testbpl.2344:15|
 :skolemid |416|
 :pattern ( ($IsBox BoxType bx@@38 (Tclass._System.___hFunc0 |#$R@@24|)))
)))
(assert (forall ((|#$R@@25| T@U) (bx@@39 T@U) ) (!  (=> ($IsBox BoxType bx@@39 (Tclass._System.___hPartialFunc0 |#$R@@25|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@39)) bx@@39) ($Is HandleTypeType ($Unbox HandleTypeType bx@@39) (Tclass._System.___hPartialFunc0 |#$R@@25|))))
 :qid |testbpl.2522:15|
 :skolemid |443|
 :pattern ( ($IsBox BoxType bx@@39 (Tclass._System.___hPartialFunc0 |#$R@@25|)))
)))
(assert (forall ((|#$R@@26| T@U) (bx@@40 T@U) ) (!  (=> ($IsBox BoxType bx@@40 (Tclass._System.___hTotalFunc0 |#$R@@26|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@40)) bx@@40) ($Is HandleTypeType ($Unbox HandleTypeType bx@@40) (Tclass._System.___hTotalFunc0 |#$R@@26|))))
 :qid |testbpl.2559:15|
 :skolemid |448|
 :pattern ( ($IsBox BoxType bx@@40 (Tclass._System.___hTotalFunc0 |#$R@@26|)))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (T@@104 T@T) ) (! (= (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)) (|MultiSet#UnionOne| T@@104 (|MultiSet#FromSeq| T@@104 s@@37) v@@37))
 :qid |testbpl.1171:18|
 :skolemid |216|
 :pattern ( (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)))
)))
(assert (forall ((m@@46 T@U) (s@@38 T@U) (U@@34 T@T) (V@@34 T@T) ) (! (= (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@46 s@@38)) (|Set#Difference| U@@34 (|Map#Domain| U@@34 V@@34 m@@46) s@@38))
 :qid |testbpl.1575:20|
 :skolemid |298|
 :pattern ( (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@46 s@@38)))
)))
(assert (forall ((m@@47 T@U) (s@@39 T@U) (U@@35 T@T) (V@@35 T@T) ) (! (= (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@47 s@@39)) (|Set#Difference| U@@35 (|IMap#Domain| U@@35 V@@35 m@@47) s@@39))
 :qid |testbpl.1716:20|
 :skolemid |330|
 :pattern ( (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@47 s@@39)))
)))
(assert (forall ((ch T@U) ) (!  (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (or (and (<= 0 (|char#ToInt| ch)) (< (|char#ToInt| ch) 55296)) (and (<= 57344 (|char#ToInt| ch)) (< (|char#ToInt| ch) 1114112))))
 :qid |testbpl.168:15|
 :skolemid |22|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((o@@45 T@U) ) (!  (=> (|ORD#IsNat| o@@45) (= o@@45 (|ORD#FromNat| (|ORD#Offset| o@@45))))
 :qid |testbpl.482:15|
 :skolemid |86|
 :pattern ( (|ORD#Offset| o@@45))
 :pattern ( (|ORD#IsNat| o@@45))
)))
(assert (forall ((s@@40 T@U) (T@@105 T@T) ) (!  (and (= (= (|Set#Card| T@@105 s@@40) 0) (= s@@40 (|Set#Empty| T@@105))) (=> (or (not (= (|Set#Card| T@@105 s@@40) 0)) (not true)) (exists ((x@@42 T@U) ) (! (U_2_bool (MapType0Select T@@105 boolType s@@40 x@@42))
 :qid |testbpl.792:39|
 :skolemid |125|
))))
 :qid |testbpl.789:18|
 :skolemid |126|
 :pattern ( (|Set#Card| T@@105 s@@40))
)))
(assert (forall ((h@@24 T@U) (r@@11 T@U) (f@@24 T@U) (x@@43 T@U) (alpha@@2 T@T) ) (!  (=> ($IsGoodHeap (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43)))) ($HeapSucc h@@24 (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43)))))
 :qid |testbpl.714:22|
 :skolemid |115|
 :pattern ( (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43))))
)))
(assert (forall ((a@@83 T@U) (b@@55 T@U) (T@@106 T@T) ) (! (= (|Set#Subset| T@@106 a@@83 b@@55) (forall ((o@@46 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@106 boolType a@@83 o@@46)) (U_2_bool (MapType0Select T@@106 boolType b@@55 o@@46)))
 :qid |testbpl.895:33|
 :skolemid |148|
 :pattern ( (MapType0Select T@@106 boolType a@@83 o@@46))
 :pattern ( (MapType0Select T@@106 boolType b@@55 o@@46))
)))
 :qid |testbpl.893:18|
 :skolemid |149|
 :pattern ( (|Set#Subset| T@@106 a@@83 b@@55))
)))
(assert (forall ((a@@84 T@U) (b@@56 T@U) (T@@107 T@T) ) (! (= (|ISet#Subset| T@@107 a@@84 b@@56) (forall ((o@@47 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@107 boolType a@@84 o@@47)) (U_2_bool (MapType0Select T@@107 boolType b@@56 o@@47)))
 :qid |testbpl.985:34|
 :skolemid |170|
 :pattern ( (MapType0Select T@@107 boolType a@@84 o@@47))
 :pattern ( (MapType0Select T@@107 boolType b@@56 o@@47))
)))
 :qid |testbpl.983:18|
 :skolemid |171|
 :pattern ( (|ISet#Subset| T@@107 a@@84 b@@56))
)))
(assert (forall ((d@@10 T@U) ($h@@12 T@U) ) (!  (=> (and ($IsGoodHeap $h@@12) ($Is DatatypeTypeType d@@10 Tclass._System.Tuple0)) ($IsAlloc DatatypeTypeType d@@10 Tclass._System.Tuple0 $h@@12))
 :qid |testbpl.2786:15|
 :skolemid |477|
 :pattern ( ($IsAlloc DatatypeTypeType d@@10 Tclass._System.Tuple0 $h@@12))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (= (TagFamily Tclass._System.object?) tytagFamily$object))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (= (TagFamily Tclass._System.nat) tytagFamily$nat))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (= (TagFamily Tclass._System.object) tytagFamily$object))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (= (TagFamily Tclass._System.Tuple0) |tytagFamily$_tuple#0|))
(assert (forall ((_System.array$arg@@11 T@U) ($h@@13 T@U) ($o@@7 T@U) ($i0@@0 Int) ) (!  (=> (and (and (and (and ($IsGoodHeap $h@@13) (or (not (= $o@@7 null)) (not true))) (= (dtype $o@@7) (Tclass._System.array? _System.array$arg@@11))) (<= 0 $i0@@0)) (< $i0@@0 (_System.array.Length $o@@7))) ($IsBox BoxType ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@13 $o@@7) (IndexField $i0@@0))) _System.array$arg@@11))
 :qid |testbpl.1916:15|
 :skolemid |358|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@13 $o@@7) (IndexField $i0@@0))) (Tclass._System.array? _System.array$arg@@11))
)))
(assert (forall ((ty@@1 T@U) (heap@@8 T@U) (len@@0 Int) (init@@0 T@U) ) (!  (=> (and ($IsGoodHeap heap@@8) (<= 0 len@@0)) (= (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@8 len@@0 init@@0)) len@@0))
 :qid |testbpl.1241:15|
 :skolemid |229|
 :pattern ( (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@8 len@@0 init@@0)))
)))
(assert (forall ((s@@41 T@U) (n@@20 Int) (k@@7 Int) (T@@108 T@T) ) (!  (=> (and (and (<= 0 n@@20) (<= n@@20 k@@7)) (< k@@7 (|Seq#Length| T@@108 s@@41))) (= (|Seq#Index| T@@108 (|Seq#Drop| T@@108 s@@41 n@@20) (- k@@7 n@@20)) (|Seq#Index| T@@108 s@@41 k@@7)))
 :qid |testbpl.1361:18|
 :weight 25
 :skolemid |254|
 :pattern ( (|Seq#Index| T@@108 s@@41 k@@7) (|Seq#Drop| T@@108 s@@41 n@@20))
)))
(assert (forall ((v@@38 T@U) (t0@@45 T@U) (h@@25 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@45) h@@25) (forall ((bx@@41 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@38 bx@@41))) ($IsAllocBox BoxType bx@@41 t0@@45 h@@25))
 :qid |testbpl.363:19|
 :skolemid |70|
 :pattern ( (MapType0Select BoxType intType v@@38 bx@@41))
)))
 :qid |testbpl.360:15|
 :skolemid |71|
 :pattern ( ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@45) h@@25))
)))
(assert (forall ((t0@@46 T@U) (heap@@9 T@U) (h@@26 T@U) (r@@12 T@U) (rd@@3 T@U) (bx@@42 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@46 heap@@9 (Handle0 h@@26 r@@12 rd@@3)) bx@@42)) (U_2_bool (MapType0Select BoxType boolType (MapType0Select (MapType0Type refType (MapType1Type BoxType)) (MapType0Type BoxType boolType) rd@@3 heap@@9) bx@@42)))
 :qid |testbpl.2366:15|
 :skolemid |419|
 :pattern ( (MapType0Select BoxType boolType (Reads0 t0@@46 heap@@9 (Handle0 h@@26 r@@12 rd@@3)) bx@@42))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit DatatypeTypeType |#_System._tuple#0._#Make0|)))
(assert (forall ((o@@48 T@U) (p@@6 T@U) ) (!  (=> (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@48))) (or (and (= p@@6 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@48 p@@6) o@@48)) (and (or (not (= p@@6 (|ORD#FromNat| 0))) (not true)) (|ORD#Less| (|ORD#Minus| o@@48 p@@6) o@@48))))
 :qid |testbpl.537:15|
 :skolemid |95|
 :pattern ( (|ORD#Minus| o@@48 p@@6))
)))
(assert (forall ((a@@85 T@U) (x@@44 T@U) (T@@109 T@T) ) (!  (=> (not (U_2_bool (MapType0Select T@@109 boolType a@@85 x@@44))) (= (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@85 x@@44)) (+ (|Set#Card| T@@109 a@@85) 1)))
 :qid |testbpl.822:18|
 :skolemid |134|
 :pattern ( (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@85 x@@44)))
)))
(assert (forall ((s@@42 T@U) ) (! ($Is (MapType0Type BoxType boolType) (SetRef_to_SetBox s@@42) (TSet Tclass._System.object?))
 :qid |testbpl.440:15|
 :skolemid |82|
 :pattern ( (SetRef_to_SetBox s@@42))
)))
(assert (forall ((f@@25 T@U) (t0@@47 T@U) (h@@27 T@U) ) (!  (=> (and ($IsGoodHeap h@@27) ($IsAlloc HandleTypeType f@@25 (Tclass._System.___hFunc0 t0@@47) h@@27)) (=> (Requires0 t0@@47 h@@27 f@@25) ($IsAllocBox BoxType (Apply0 t0@@47 h@@27 f@@25) t0@@47 h@@27)))
 :qid |testbpl.2497:15|
 :skolemid |440|
 :pattern ( ($IsAlloc HandleTypeType f@@25 (Tclass._System.___hFunc0 t0@@47) h@@27))
)))
(assert (forall ((_System.array$arg@@12 T@U) ($h@@14 T@U) ($o@@8 T@U) ) (!  (=> (and (and (and ($IsGoodHeap $h@@14) (or (not (= $o@@8 null)) (not true))) (= (dtype $o@@8) (Tclass._System.array? _System.array$arg@@12))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@14 $o@@8) alloc)))) ($IsAlloc intType (int_2_U (_System.array.Length $o@@8)) TInt $h@@14))
 :qid |testbpl.1959:15|
 :skolemid |363|
 :pattern ( (_System.array.Length $o@@8) ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@14 $o@@8) alloc)) (Tclass._System.array? _System.array$arg@@12))
)))
(assert (forall ((s@@43 T@U) (m@@48 Int) (n@@21 Int) (T@@110 T@T) ) (!  (=> (and (and (<= 0 m@@48) (<= 0 n@@21)) (<= (+ m@@48 n@@21) (|Seq#Length| T@@110 s@@43))) (= (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@48) n@@21) (|Seq#Drop| T@@110 s@@43 (+ m@@48 n@@21))))
 :qid |testbpl.1454:18|
 :skolemid |273|
 :pattern ( (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@48) n@@21))
)))
(assert (forall ((s0@@7 T@U) (s1@@2 T@U) (n@@22 Int) (T@@111 T@T) ) (! (= (|Seq#SameUntil| T@@111 s0@@7 s1@@2 n@@22) (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 n@@22)) (= (|Seq#Index| T@@111 s0@@7 j@@3) (|Seq#Index| T@@111 s1@@2 j@@3)))
 :qid |testbpl.1335:19|
 :skolemid |248|
 :pattern ( (|Seq#Index| T@@111 s0@@7 j@@3))
 :pattern ( (|Seq#Index| T@@111 s1@@2 j@@3))
)))
 :qid |testbpl.1332:18|
 :skolemid |249|
 :pattern ( (|Seq#SameUntil| T@@111 s0@@7 s1@@2 n@@22))
)))
(assert (forall ((a@@86 T@U) (b@@57 T@U) (T@@112 T@T) ) (! (= (|Set#Disjoint| T@@112 a@@86 b@@57) (forall ((o@@49 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@112 boolType a@@86 o@@49))) (not (U_2_bool (MapType0Select T@@112 boolType b@@57 o@@49))))
 :qid |testbpl.909:35|
 :skolemid |153|
 :pattern ( (MapType0Select T@@112 boolType a@@86 o@@49))
 :pattern ( (MapType0Select T@@112 boolType b@@57 o@@49))
)))
 :qid |testbpl.907:18|
 :skolemid |154|
 :pattern ( (|Set#Disjoint| T@@112 a@@86 b@@57))
)))
(assert (forall ((a@@87 T@U) (b@@58 T@U) (T@@113 T@T) ) (! (= (|ISet#Disjoint| T@@113 a@@87 b@@58) (forall ((o@@50 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@113 boolType a@@87 o@@50))) (not (U_2_bool (MapType0Select T@@113 boolType b@@58 o@@50))))
 :qid |testbpl.1001:36|
 :skolemid |175|
 :pattern ( (MapType0Select T@@113 boolType a@@87 o@@50))
 :pattern ( (MapType0Select T@@113 boolType b@@58 o@@50))
)))
 :qid |testbpl.999:18|
 :skolemid |176|
 :pattern ( (|ISet#Disjoint| T@@113 a@@87 b@@58))
)))
(assert (forall ((a@@88 T@U) (x@@45 T@U) (y@@23 T@U) (T@@114 T@T) ) (!  (=> (or (not (= x@@45 y@@23)) (not true)) (= (U_2_int (MapType0Select T@@114 intType a@@88 y@@23)) (U_2_int (MapType0Select T@@114 intType (|MultiSet#UnionOne| T@@114 a@@88 x@@45) y@@23))))
 :qid |testbpl.1070:18|
 :skolemid |194|
 :pattern ( (|MultiSet#UnionOne| T@@114 a@@88 x@@45) (MapType0Select T@@114 intType a@@88 y@@23))
)))
(assert (forall ((s0@@8 T@U) (s1@@3 T@U) (n@@23 Int) (T@@115 T@T) ) (!  (and (=> (< n@@23 (|Seq#Length| T@@115 s0@@8)) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23) (|Seq#Index| T@@115 s0@@8 n@@23))) (=> (<= (|Seq#Length| T@@115 s0@@8) n@@23) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23) (|Seq#Index| T@@115 s1@@3 (- n@@23 (|Seq#Length| T@@115 s0@@8))))))
 :qid |testbpl.1264:18|
 :skolemid |233|
 :pattern ( (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23))
)))
(assert (forall ((o@@51 T@U) (p@@7 T@U) ) (!  (and (=> (|ORD#IsNat| (|ORD#Plus| o@@51 p@@7)) (and (|ORD#IsNat| o@@51) (|ORD#IsNat| p@@7))) (=> (|ORD#IsNat| p@@7) (and (= (|ORD#IsNat| (|ORD#Plus| o@@51 p@@7)) (|ORD#IsNat| o@@51)) (= (|ORD#Offset| (|ORD#Plus| o@@51 p@@7)) (+ (|ORD#Offset| o@@51) (|ORD#Offset| p@@7))))))
 :qid |testbpl.512:15|
 :skolemid |91|
 :pattern ( (|ORD#Plus| o@@51 p@@7))
)))
(assert (forall ((f@@26 T@U) (t0@@48 T@U) (u0@@8 T@U) ) (!  (=> (and ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 t0@@48)) (forall ((bx@@43 T@U) ) (!  (=> ($IsBox BoxType bx@@43 t0@@48) ($IsBox BoxType bx@@43 u0@@8))
 :qid |testbpl.2483:19|
 :skolemid |436|
 :pattern ( ($IsBox BoxType bx@@43 t0@@48))
 :pattern ( ($IsBox BoxType bx@@43 u0@@8))
))) ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 u0@@8)))
 :qid |testbpl.2480:15|
 :skolemid |437|
 :pattern ( ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 t0@@48)) ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 u0@@8)))
)))
(assert (forall ((a@@89 Int) ) (!  (=> (< a@@89 0) (= (|Math#clip| a@@89) 0))
 :qid |testbpl.1017:15|
 :skolemid |181|
 :pattern ( (|Math#clip| a@@89))
)))
(assert (forall ((|a#3#0#0| T@U) (|a#3#1#0| T@U) ) (! (= (|#_System._tuple#2._#Make2| (Lit BoxType |a#3#0#0|) (Lit BoxType |a#3#1#0|)) (Lit DatatypeTypeType (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|)))
 :qid |testbpl.2682:15|
 :skolemid |465|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit BoxType |a#3#0#0|) (Lit BoxType |a#3#1#0|)))
)))
(assert (forall ((x@@46 Int) ) (! (= ($Box intType (int_2_U (LitInt x@@46))) (Lit BoxType ($Box intType (int_2_U x@@46))))
 :qid |testbpl.144:15|
 :skolemid |18|
 :pattern ( ($Box intType (int_2_U (LitInt x@@46))))
)))
(assert (forall ((x@@47 Real) ) (! (= ($Box realType (real_2_U (LitReal x@@47))) (Lit BoxType ($Box realType (real_2_U x@@47))))
 :qid |testbpl.151:15|
 :skolemid |20|
 :pattern ( ($Box realType (real_2_U (LitReal x@@47))))
)))
(assert (forall ((x@@48 T@U) (T@@116 T@T) ) (! (= ($Box T@@116 (Lit T@@116 x@@48)) (Lit BoxType ($Box T@@116 x@@48)))
 :qid |testbpl.137:18|
 :skolemid |16|
 :pattern ( ($Box T@@116 (Lit T@@116 x@@48)))
)))
(assert (forall ((a@@90 T@U) (b@@59 T@U) (T@@117 T@T) ) (! (= (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@90 b@@59)) (|MultiSet#Union| T@@117 (|MultiSet#FromSeq| T@@117 a@@90) (|MultiSet#FromSeq| T@@117 b@@59)))
 :qid |testbpl.1175:18|
 :skolemid |217|
 :pattern ( (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@90 b@@59)))
)))
(assert (forall ((m@@49 T@U) (n@@24 T@U) (U@@36 T@T) (V@@36 T@T) ) (! (= (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@49 n@@24)) (|Set#Union| U@@36 (|Map#Domain| U@@36 V@@36 m@@49) (|Map#Domain| U@@36 V@@36 n@@24)))
 :qid |testbpl.1563:20|
 :skolemid |296|
 :pattern ( (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@49 n@@24)))
)))
(assert (forall ((m@@50 T@U) (n@@25 T@U) (U@@37 T@T) (V@@37 T@T) ) (! (= (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@50 n@@25)) (|Set#Union| U@@37 (|IMap#Domain| U@@37 V@@37 m@@50) (|IMap#Domain| U@@37 V@@37 n@@25)))
 :qid |testbpl.1702:20|
 :skolemid |328|
 :pattern ( (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@50 n@@25)))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@4 T@U) (|q#0@@4| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0@@4|) (< 0 $FunctionContextHeight)) true)
 :qid |testbpl.2832:16|
 :skolemid |482|
 :pattern ( (_module.__default.secretPredicate $ly@@4 |q#0@@4|))
))))
(assert (forall ((s@@44 T@U) (T@@118 T@T) ) (!  (=> (= (|Seq#Length| T@@118 s@@44) 0) (= s@@44 (|Seq#Empty| T@@118)))
 :qid |testbpl.1205:18|
 :skolemid |223|
 :pattern ( (|Seq#Length| T@@118 s@@44))
)))
(assert (forall ((s@@45 T@U) (n@@26 Int) (T@@119 T@T) ) (!  (=> (= n@@26 0) (= (|Seq#Take| T@@119 s@@45 n@@26) (|Seq#Empty| T@@119)))
 :qid |testbpl.1450:18|
 :skolemid |272|
 :pattern ( (|Seq#Take| T@@119 s@@45 n@@26))
)))
(assert (forall ((t0@@49 T@U) (heap@@10 T@U) (h@@28 T@U) (r@@13 T@U) (rd@@4 T@U) ) (!  (=> (U_2_bool (MapType0Select (MapType0Type refType (MapType1Type BoxType)) boolType r@@13 heap@@10)) (Requires0 t0@@49 heap@@10 (Handle0 h@@28 r@@13 rd@@4)))
 :qid |testbpl.2362:15|
 :skolemid |418|
 :pattern ( (Requires0 t0@@49 heap@@10 (Handle0 h@@28 r@@13 rd@@4)))
)))
(assert (forall ((s@@46 T@U) (x@@49 T@U) (n@@27 T@U) (T@@120 T@T) ) (!  (=> (<= 0 (U_2_int n@@27)) (= (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)) (+ (- (|MultiSet#Card| T@@120 s@@46) (U_2_int (MapType0Select T@@120 intType s@@46 x@@49))) (U_2_int n@@27))))
 :qid |testbpl.1032:18|
 :skolemid |185|
 :pattern ( (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)))
)))
(assert (forall ((t0@@50 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@27 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@10 h1@@10) ($IsGoodHeap h0@@10)) ($IsGoodHeap h1@@10)) ($Is HandleTypeType f@@27 (Tclass._System.___hFunc0 t0@@50))) (forall ((o@@52 T@U) (fld@@9 T@U) (a@@91 T@T) ) (!  (=> (and (or (not (= o@@52 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@50 h0@@10 f@@27) ($Box refType o@@52)))) (= ($Unbox a@@91 (MapType1Select a@@91 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@10 o@@52) fld@@9)) ($Unbox a@@91 (MapType1Select a@@91 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@10 o@@52) fld@@9))))
 :qid |testbpl.2414:22|
 :skolemid |424|
))) (= (Requires0 t0@@50 h0@@10 f@@27) (Requires0 t0@@50 h1@@10 f@@27)))
 :qid |testbpl.2407:15|
 :skolemid |425|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Requires0 t0@@50 h1@@10 f@@27))
)))
(assert (forall ((t0@@51 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@28 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@11 h1@@11) ($IsGoodHeap h0@@11)) ($IsGoodHeap h1@@11)) ($Is HandleTypeType f@@28 (Tclass._System.___hFunc0 t0@@51))) (forall ((o@@53 T@U) (fld@@10 T@U) (a@@92 T@T) ) (!  (=> (and (or (not (= o@@53 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@51 h1@@11 f@@28) ($Box refType o@@53)))) (= ($Unbox a@@92 (MapType1Select a@@92 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@11 o@@53) fld@@10)) ($Unbox a@@92 (MapType1Select a@@92 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@11 o@@53) fld@@10))))
 :qid |testbpl.2427:22|
 :skolemid |426|
))) (= (Requires0 t0@@51 h0@@11 f@@28) (Requires0 t0@@51 h1@@11 f@@28)))
 :qid |testbpl.2420:15|
 :skolemid |427|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Requires0 t0@@51 h1@@11 f@@28))
)))
(assert (= |_module.__default.magicNum#requires| true))
(assert (forall ((a@@93 T@U) (b@@60 T@U) (o@@54 T@U) (T@@121 T@T) ) (! (= (U_2_bool (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@93 b@@60) o@@54))  (or (U_2_bool (MapType0Select T@@121 boolType a@@93 o@@54)) (U_2_bool (MapType0Select T@@121 boolType b@@60 o@@54))))
 :qid |testbpl.828:18|
 :skolemid |135|
 :pattern ( (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@93 b@@60) o@@54))
)))
(assert (forall ((a@@94 T@U) (b@@61 T@U) (o@@55 T@U) (T@@122 T@T) ) (! (= (U_2_bool (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@94 b@@61) o@@55))  (or (U_2_bool (MapType0Select T@@122 boolType a@@94 o@@55)) (U_2_bool (MapType0Select T@@122 boolType b@@61 o@@55))))
 :qid |testbpl.931:18|
 :skolemid |159|
 :pattern ( (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@94 b@@61) o@@55))
)))
(assert (forall ((h@@29 T@U) (v@@39 T@U) ) (! ($IsAlloc intType v@@39 TInt h@@29)
 :qid |testbpl.334:15|
 :skolemid |60|
 :pattern ( ($IsAlloc intType v@@39 TInt h@@29))
)))
(assert (forall ((h@@30 T@U) (v@@40 T@U) ) (! ($IsAlloc realType v@@40 TReal h@@30)
 :qid |testbpl.336:15|
 :skolemid |61|
 :pattern ( ($IsAlloc realType v@@40 TReal h@@30))
)))
(assert (forall ((h@@31 T@U) (v@@41 T@U) ) (! ($IsAlloc boolType v@@41 TBool h@@31)
 :qid |testbpl.338:15|
 :skolemid |62|
 :pattern ( ($IsAlloc boolType v@@41 TBool h@@31))
)))
(assert (forall ((h@@32 T@U) (v@@42 T@U) ) (! ($IsAlloc charType v@@42 TChar h@@32)
 :qid |testbpl.340:15|
 :skolemid |63|
 :pattern ( ($IsAlloc charType v@@42 TChar h@@32))
)))
(assert (forall ((h@@33 T@U) (v@@43 T@U) ) (! ($IsAlloc BoxType v@@43 TORDINAL h@@33)
 :qid |testbpl.342:15|
 :skolemid |64|
 :pattern ( ($IsAlloc BoxType v@@43 TORDINAL h@@33))
)))
(assert (forall ((s@@47 T@U) (i@@22 Int) (v@@44 T@U) (n@@28 Int) (T@@123 T@T) ) (!  (=> (and (and (<= 0 i@@22) (< i@@22 n@@28)) (<= n@@28 (|Seq#Length| T@@123 s@@47))) (= (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28) (|Seq#Update| T@@123 (|Seq#Take| T@@123 s@@47 n@@28) i@@22 v@@44)))
 :qid |testbpl.1395:18|
 :skolemid |261|
 :pattern ( (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28))
)))
(assert (forall ((v@@45 T@U) (t0@@52 T@U) ) (! (= ($Is (SeqType BoxType) v@@45 (TSeq t0@@52)) (forall ((i@@23 Int) ) (!  (=> (and (<= 0 i@@23) (< i@@23 (|Seq#Length| BoxType v@@45))) ($IsBox BoxType (|Seq#Index| BoxType v@@45 i@@23) t0@@52))
 :qid |testbpl.300:19|
 :skolemid |52|
 :pattern ( (|Seq#Index| BoxType v@@45 i@@23))
)))
 :qid |testbpl.297:15|
 :skolemid |53|
 :pattern ( ($Is (SeqType BoxType) v@@45 (TSeq t0@@52)))
)))
(assert (forall ((|#$R@@27| T@U) (|f#0@@6| T@U) ) (! (= ($Is HandleTypeType |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|))  (and ($Is HandleTypeType |f#0@@6| (Tclass._System.___hFunc0 |#$R@@27|)) (|Set#Equal| BoxType (Reads0 |#$R@@27| $OneHeap |f#0@@6|) (|Set#Empty| BoxType))))
 :qid |testbpl.2529:15|
 :skolemid |444|
 :pattern ( ($Is HandleTypeType |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|)))
)))
(assert (forall ((s@@48 T@U) (i@@24 Int) ) (!  (=> (and (<= 0 i@@24) (< i@@24 (|Seq#Length| BoxType s@@48))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))) (|Seq#Rank| BoxType s@@48)))
 :qid |testbpl.1428:15|
 :skolemid |267|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))))
)))
(assert (forall ((v@@46 T@U) (t0@@53 T@U) (t1@@24 T@U) ) (!  (=> ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@53 t1@@24)) (and (and ($Is (MapType0Type BoxType boolType) (|Map#Domain| BoxType BoxType v@@46) (TSet t0@@53)) ($Is (MapType0Type BoxType boolType) (|Map#Values| BoxType BoxType v@@46) (TSet t1@@24))) ($Is (MapType0Type BoxType boolType) (|Map#Items| BoxType BoxType v@@46) (TSet (Tclass._System.Tuple2 t0@@53 t1@@24)))))
 :qid |testbpl.311:15|
 :skolemid |56|
 :pattern ( ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@53 t1@@24)))
)))
(assert (forall ((v@@47 T@U) (t0@@54 T@U) (t1@@25 T@U) ) (!  (=> ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@54 t1@@25)) (and (and ($Is (MapType0Type BoxType boolType) (|IMap#Domain| BoxType BoxType v@@47) (TISet t0@@54)) ($Is (MapType0Type BoxType boolType) (|IMap#Values| BoxType BoxType v@@47) (TISet t1@@25))) ($Is (MapType0Type BoxType boolType) (|IMap#Items| BoxType BoxType v@@47) (TISet (Tclass._System.Tuple2 t0@@54 t1@@25)))))
 :qid |testbpl.325:15|
 :skolemid |59|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@54 t1@@25)))
)))
(assert (forall ((v@@48 T@U) ) (! ($Is intType v@@48 TInt)
 :qid |testbpl.268:15|
 :skolemid |39|
 :pattern ( ($Is intType v@@48 TInt))
)))
(assert (forall ((v@@49 T@U) ) (! ($Is realType v@@49 TReal)
 :qid |testbpl.270:15|
 :skolemid |40|
 :pattern ( ($Is realType v@@49 TReal))
)))
(assert (forall ((v@@50 T@U) ) (! ($Is boolType v@@50 TBool)
 :qid |testbpl.272:15|
 :skolemid |41|
 :pattern ( ($Is boolType v@@50 TBool))
)))
(assert (forall ((v@@51 T@U) ) (! ($Is charType v@@51 TChar)
 :qid |testbpl.274:15|
 :skolemid |42|
 :pattern ( ($Is charType v@@51 TChar))
)))
(assert (forall ((v@@52 T@U) ) (! ($Is BoxType v@@52 TORDINAL)
 :qid |testbpl.276:15|
 :skolemid |43|
 :pattern ( ($Is BoxType v@@52 TORDINAL))
)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $Heap@0 () T@U)
(declare-fun $IsHeapAnchor (T@U) Bool)
(declare-fun $Heap () T@U)
(declare-fun MoreFuel__module._default.secretPredicate2 () T@U)
(declare-fun reveal__module._default.secretPredicate () Bool)
(declare-fun |##q#0@0| () Int)
(declare-fun $_ReadsFrame@0 () T@U)
(set-info :boogie-vc-id CheckWellformed$$_module.__default.magicNum)
(set-option :timeout 0)
(set-option :rlimit 0)
(assert (not
 (=> (= (ControlFlow 0 0) 5) (let ((anon3_Else_correct  (=> (and (and ($IsGoodHeap $Heap@0) ($IsHeapAnchor $Heap@0)) (and (= $Heap $Heap@0) (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate2)))) (=> (and (and (and (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate2))) reveal__module._default.secretPredicate) (and (= (AsFuelBottom MoreFuel__module._default.secretPredicate2) MoreFuel__module._default.secretPredicate2) (= |##q#0@0| (LitInt 31984823)))) (and (and ($IsAlloc intType (int_2_U |##q#0@0|) TInt $Heap@0) (|_module.__default.secretPredicate#canCall| (LitInt 31984823))) (and (|_module.__default.secretPredicate#canCall| (LitInt 31984823)) (= (ControlFlow 0 3) (- 0 2))))) (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate (LitInt 31984823))))))
(let ((anon3_Then_correct true))
(let ((anon0_correct  (=> (= $_ReadsFrame@0 (|lambda#0| null $Heap alloc false)) (=> (and (= (AsFuelBottom StartFuel__module._default.secretPredicate) StartFuel__module._default.secretPredicate) (= (AsFuelBottom StartFuelAssert__module._default.secretPredicate) StartFuelAssert__module._default.secretPredicate)) (and (=> (= (ControlFlow 0 4) 1) anon3_Then_correct) (=> (= (ControlFlow 0 4) 3) anon3_Else_correct))))))
(let ((PreconditionGeneratedEntry_correct  (=> (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (and (= 1 $FunctionContextHeight) (= (ControlFlow 0 5) 4))) anon0_correct)))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)
(pop 1)
; Valid
(get-info :rlimit)
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun TBool () T@U)
(declare-fun TChar () T@U)
(declare-fun TInt () T@U)
(declare-fun TReal () T@U)
(declare-fun TORDINAL () T@U)
(declare-fun TagBool () T@U)
(declare-fun TagChar () T@U)
(declare-fun TagInt () T@U)
(declare-fun TagReal () T@U)
(declare-fun TagORDINAL () T@U)
(declare-fun TagSet () T@U)
(declare-fun TagISet () T@U)
(declare-fun TagMultiSet () T@U)
(declare-fun TagSeq () T@U)
(declare-fun TagMap () T@U)
(declare-fun TagIMap () T@U)
(declare-fun TagClass () T@U)
(declare-fun class._System.int () T@U)
(declare-fun class._System.bool () T@U)
(declare-fun class._System.set () T@U)
(declare-fun class._System.seq () T@U)
(declare-fun class._System.multiset () T@U)
(declare-fun alloc () T@U)
(declare-fun allocName () T@U)
(declare-fun Tagclass._System.nat () T@U)
(declare-fun class._System.object? () T@U)
(declare-fun Tagclass._System.object? () T@U)
(declare-fun Tagclass._System.object () T@U)
(declare-fun class._System.array? () T@U)
(declare-fun Tagclass._System.array? () T@U)
(declare-fun Tagclass._System.array () T@U)
(declare-fun Tagclass._System.___hFunc1 () T@U)
(declare-fun Tagclass._System.___hPartialFunc1 () T@U)
(declare-fun Tagclass._System.___hTotalFunc1 () T@U)
(declare-fun Tagclass._System.___hFunc0 () T@U)
(declare-fun Tagclass._System.___hPartialFunc0 () T@U)
(declare-fun Tagclass._System.___hTotalFunc0 () T@U)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun class._module.__default () T@U)
(declare-fun tytagFamily$nat () T@U)
(declare-fun tytagFamily$object () T@U)
(declare-fun tytagFamily$array () T@U)
(declare-fun |tytagFamily$_#Func1| () T@U)
(declare-fun |tytagFamily$_#PartialFunc1| () T@U)
(declare-fun |tytagFamily$_#TotalFunc1| () T@U)
(declare-fun |tytagFamily$_#Func0| () T@U)
(declare-fun |tytagFamily$_#PartialFunc0| () T@U)
(declare-fun |tytagFamily$_#TotalFunc0| () T@U)
(declare-fun |tytagFamily$_tuple#2| () T@U)
(declare-fun |tytagFamily$_tuple#0| () T@U)
(declare-fun Ctor (T@T) Int)
(declare-fun boolType () T@T)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun |Map#Disjoint| (T@T T@T T@U T@U) Bool)
(declare-fun MapType0Select (T@T T@T T@U T@U) T@U)
(declare-fun |Map#Domain| (T@T T@T T@U) T@U)
(declare-fun MapType0Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun FDim (T@T T@U) Int)
(declare-fun Tag (T@U) T@U)
(declare-fun DeclName (T@T T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun Reads0 (T@U T@U T@U) T@U)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $Is (T@T T@U T@U) Bool)
(declare-fun HandleTypeType () T@T)
(declare-fun Tclass._System.___hFunc0 (T@U) T@U)
(declare-fun null () T@U)
(declare-fun BoxType () T@T)
(declare-fun $Box (T@T T@U) T@U)
(declare-fun refType () T@T)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType1Select (T@T T@T T@U T@U) T@U)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType1Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun Apply0 (T@U T@U T@U) T@U)
(declare-fun Requires1 (T@U T@U T@U T@U T@U) Bool)
(declare-fun $OneHeap () T@U)
(declare-fun $IsBox (T@T T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc1 (T@U T@U) T@U)
(declare-fun |Set#Equal| (T@T T@U T@U) Bool)
(declare-fun Reads1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun |Set#Empty| (T@T) T@U)
(declare-fun $IsAlloc (T@T T@U T@U T@U) Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun Tclass._System.array? (T@U) T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun |MultiSet#Card| (T@T T@U) Int)
(declare-fun |MultiSet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@T T@U T@U) T@U)
(declare-fun |ORD#Less| (T@U T@U) Bool)
(declare-fun Tclass._System.nat () T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun |MultiSet#FromSeq| (T@T T@U) T@U)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |MultiSet#Empty| (T@T) T@U)
(declare-fun |Seq#Contains| (T@T T@U T@U) Bool)
(declare-fun |Seq#Build| (T@T T@U T@U) T@U)
(declare-fun |Map#Glue| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |Map#Elements| (T@T T@T T@U) T@U)
(declare-fun |IMap#Domain| (T@T T@T T@U) T@U)
(declare-fun |IMap#Glue| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |IMap#Elements| (T@T T@T T@U) T@U)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun Tclass._System.object? () T@U)
(declare-fun Tclass._System.array (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0 (T@U) T@U)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#Offset| (T@U) Int)
(declare-fun DatatypeTypeType () T@T)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun _System.Tuple2._1 (T@U) T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun |Seq#Drop| (T@T T@U Int) T@U)
(declare-fun |Seq#Length| (T@T T@U) Int)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun TMultiSet (T@U) T@U)
(declare-fun $IsGoodMultiSet (T@T T@U) Bool)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun |Seq#Index| (T@T T@U Int) T@U)
(declare-fun |Seq#Update| (T@T T@U Int T@U) T@U)
(declare-fun |Set#Union| (T@T T@U T@U) T@U)
(declare-fun |Set#Intersection| (T@T T@U T@U) T@U)
(declare-fun |ISet#Union| (T@T T@U T@U) T@U)
(declare-fun |ISet#Intersection| (T@T T@U T@U) T@U)
(declare-fun |Seq#Take| (T@T T@U Int) T@U)
(declare-fun |Seq#Append| (T@T T@U T@U) T@U)
(declare-fun Tclass._System.object () T@U)
(declare-fun |Map#Card| (T@T T@T T@U) Int)
(declare-fun |Map#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |Set#Singleton| (T@T T@U) T@U)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun Handle0 (T@U T@U T@U) T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun _module.__default.secretPredicate (T@U Int) Bool)
(declare-fun $LS (T@U) T@U)
(declare-fun |_module.__default.secretPredicate#canCall| (Int) Bool)
(declare-fun |Set#Card| (T@T T@U) Int)
(declare-fun |Map#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun IndexField (Int) T@U)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun TSet (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun |Math#clip| (Int) Int)
(declare-fun q@Int (Real) Int)
(declare-fun LitInt (Int) Int)
(declare-fun LitReal (Real) Real)
(declare-fun Lit (T@T T@U) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun TSeq (T@U) T@U)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun $$Language$Dafny () Bool)
(declare-fun $IsAllocBox (T@T T@U T@U T@U) Bool)
(declare-fun |Seq#Equal| (T@T T@U T@U) Bool)
(declare-fun |_module.__default.magicNum#canCall| () Bool)
(declare-fun |Seq#Rank| (T@T T@U) Int)
(declare-fun Requires0 (T@U T@U T@U) Bool)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun |MultiSet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun AtLayer (T@T T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun $IsGhostField (T@T T@U) Bool)
(declare-fun |Seq#Create| (T@U T@U Int T@U) T@U)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun TagFamily (T@U) T@U)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |ISet#Equal| (T@T T@U T@U) Bool)
(declare-fun Tclass._System.___hPartialFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1 (T@U T@U) T@U)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun Handle1 (T@U T@U T@U) T@U)
(declare-fun MapType2Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |Map#Values| (T@T T@T T@U) T@U)
(declare-fun |IMap#Values| (T@T T@T T@U) T@U)
(declare-fun StartFuel__module._default.secretPredicate () T@U)
(declare-fun MoreFuel__module._default.secretPredicate0 () T@U)
(declare-fun StartFuelAssert__module._default.secretPredicate () T@U)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun _module.__default.magicNum () Int)
(declare-fun MoreFuel__module._default.secretPredicate1 () T@U)
(declare-fun |Set#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |Set#Difference| (T@T T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |ISet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Equal| (T@T T@U T@U) Bool)
(declare-fun |MultiSet#Subset| (T@T T@U T@U) Bool)
(declare-fun |_module.__default.secretPredicate#requires| (T@U Int) Bool)
(declare-fun |Map#Items| (T@T T@T T@U) T@U)
(declare-fun |IMap#Items| (T@T T@T T@U) T@U)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun TMap (T@U T@U) T@U)
(declare-fun MapTypeInv0 (T@T) T@T)
(declare-fun MapTypeInv1 (T@T) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun TIMap (T@U T@U) T@U)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-fun |ORD#LessThanLimit| (T@U T@U) Bool)
(declare-fun $LZ () T@U)
(declare-fun |Map#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |IMap#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |Set#UnionOne| (T@T T@U T@U) T@U)
(declare-fun |ISet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun q@Real (Int) Real)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun FieldOfDecl (T@T T@U T@U) T@U)
(declare-fun DeclType (T@T T@U) T@U)
(declare-fun charType () T@T)
(declare-fun |MultiSet#FromSet| (T@T T@U) T@U)
(declare-fun |Seq#Singleton| (T@T T@U) T@U)
(declare-fun |MultiSet#Singleton| (T@T T@U) T@U)
(declare-fun $AlwaysAllocated (T@U) Bool)
(declare-fun Inv0_TMap (T@U) T@U)
(declare-fun Inv1_TMap (T@U) T@U)
(declare-fun Inv0_TIMap (T@U) T@U)
(declare-fun Inv1_TIMap (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun MapType3Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun MapType3Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun IndexField_Inverse (T@T T@U) Int)
(declare-fun Tclass._System.array?_0 (T@U) T@U)
(declare-fun Tclass._System.array_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0_0 (T@U) T@U)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun |Map#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun BoxRank (T@U) Int)
(declare-fun DtRank (T@U) Int)
(declare-fun |IMap#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |MultiSet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun TypeTuple (T@U T@U) T@U)
(declare-fun TypeTupleCar (T@U) T@U)
(declare-fun TypeTupleCdr (T@U) T@U)
(declare-fun MultiIndexField_Inverse0 (T@T T@U) T@U)
(declare-fun MultiIndexField_Inverse1 (T@T T@U) Int)
(declare-fun |Seq#Build_inv0| (T@T T@U) T@U)
(declare-fun |Seq#Build_inv1| (T@T T@U) T@U)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun |Set#Subset| (T@T T@U T@U) Bool)
(declare-fun |ISet#Subset| (T@T T@U T@U) Bool)
(declare-fun |Seq#SameUntil| (T@T T@U T@U Int) Bool)
(declare-fun |_module.__default.magicNum#requires| () Bool)
(assert  (and (and (and (and (and (and (and (and (= (Ctor boolType) 0) (= (Ctor intType) 1)) (= (Ctor realType) 2)) (forall ((arg0 Bool) ) (! (= (U_2_bool (bool_2_U arg0)) arg0)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0))
))) (forall ((x T@U) ) (! (= (bool_2_U (U_2_bool x)) x)
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x))
))) (forall ((arg0@@0 Int) ) (! (= (U_2_int (int_2_U arg0@@0)) arg0@@0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((x@@0 T@U) ) (! (= (int_2_U (U_2_int x@@0)) x@@0)
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@1 T@U) ) (! (= (real_2_U (U_2_real x@@1)) x@@1)
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@1))
))))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 class._System.Tuple2 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._System.Tuple0 class._module.__default tytagFamily$nat tytagFamily$object tytagFamily$array |tytagFamily$_#Func1| |tytagFamily$_#PartialFunc1| |tytagFamily$_#TotalFunc1| |tytagFamily$_#Func0| |tytagFamily$_#PartialFunc0| |tytagFamily$_#TotalFunc0| |tytagFamily$_tuple#2| |tytagFamily$_tuple#0|)
)
(assert  (and (forall ((t0 T@T) (t1 T@T) (val T@U) (m T@U) (x0 T@U) ) (! (= (MapType0Select t0 t1 (MapType0Store t0 t1 m x0 val) x0) val)
 :qid |mapAx0:MapType0Select|
 :weight 0
)) (forall ((u0 T@T) (u1 T@T) (val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select u0 u1 (MapType0Store u0 u1 m@@0 x0@@0 val@@0) y0) (MapType0Select u0 u1 m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
))))
(assert (forall ((m@@1 T@U) (|m'| T@U) (U T@T) (V T@T) ) (! (= (|Map#Disjoint| U V m@@1 |m'|) (forall ((o T@U) ) (!  (or (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V m@@1) o))) (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V |m'|) o))))
 :qid |testbpl.1601:19|
 :skolemid |304|
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V m@@1) o))
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V |m'|) o))
)))
 :qid |testbpl.1598:20|
 :skolemid |305|
 :pattern ( (|Map#Disjoint| U V m@@1 |m'|))
)))
(assert (= (FDim boolType alloc) 0))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (= (DeclName boolType alloc) allocName))
(assert  (and (and (and (and (and (and (= (Ctor HandleTypeType) 3) (= (Ctor BoxType) 4)) (= (Ctor refType) 5)) (forall ((t0@@0 T@T) (t1@@0 T@T) (val@@1 T@U) (m@@2 T@U) (x0@@1 T@U) ) (! (= (MapType1Select t0@@0 t1@@0 (MapType1Store t0@@0 t1@@0 m@@2 x0@@1 val@@1) x0@@1) val@@1)
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((u0@@0 T@T) (s0 T@T) (t0@@1 T@T) (val@@2 T@U) (m@@3 T@U) (x0@@2 T@U) (y0@@0 T@U) ) (!  (or (= s0 t0@@1) (= (MapType1Select t0@@1 u0@@0 (MapType1Store s0 u0@@0 m@@3 x0@@2 val@@2) y0@@0) (MapType1Select t0@@1 u0@@0 m@@3 y0@@0)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((u0@@1 T@T) (s0@@0 T@T) (t0@@2 T@T) (val@@3 T@U) (m@@4 T@U) (x0@@3 T@U) (y0@@1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select t0@@2 u0@@1 (MapType1Store s0@@0 u0@@1 m@@4 x0@@3 val@@3) y0@@1) (MapType1Select t0@@2 u0@@1 m@@4 y0@@1)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
)))) (forall ((arg0@@2 T@T) ) (! (= (Ctor (MapType1Type arg0@@2)) 6)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@3 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@3)) arg0@@3)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@3))
))))
(assert (forall ((t0@@3 T@U) (h0 T@U) (h1 T@U) (f T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0 h1) ($IsGoodHeap h0)) ($IsGoodHeap h1)) ($Is HandleTypeType f (Tclass._System.___hFunc0 t0@@3))) (forall ((o@@0 T@U) (fld T@U) (a T@T) ) (!  (=> (and (or (not (= o@@0 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@3 h0 f) ($Box refType o@@0)))) (= ($Unbox a (MapType1Select a BoxType (MapType0Select refType (MapType1Type BoxType) h0 o@@0) fld)) ($Unbox a (MapType1Select a BoxType (MapType0Select refType (MapType1Type BoxType) h1 o@@0) fld))))
 :qid |testbpl.2388:22|
 :skolemid |420|
))) (= (Reads0 t0@@3 h0 f) (Reads0 t0@@3 h1 f)))
 :qid |testbpl.2381:15|
 :skolemid |421|
 :pattern ( ($HeapSucc h0 h1) (Reads0 t0@@3 h1 f))
)))
(assert (forall ((t0@@4 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@0 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@0 h1@@0) ($IsGoodHeap h0@@0)) ($IsGoodHeap h1@@0)) ($Is HandleTypeType f@@0 (Tclass._System.___hFunc0 t0@@4))) (forall ((o@@1 T@U) (fld@@0 T@U) (a@@0 T@T) ) (!  (=> (and (or (not (= o@@1 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@4 h1@@0 f@@0) ($Box refType o@@1)))) (= ($Unbox a@@0 (MapType1Select a@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@0 o@@1) fld@@0)) ($Unbox a@@0 (MapType1Select a@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@0 o@@1) fld@@0))))
 :qid |testbpl.2401:22|
 :skolemid |422|
))) (= (Reads0 t0@@4 h0@@0 f@@0) (Reads0 t0@@4 h1@@0 f@@0)))
 :qid |testbpl.2394:15|
 :skolemid |423|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads0 t0@@4 h1@@0 f@@0))
)))
(assert (forall ((t0@@5 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@1 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@1 h1@@1) ($IsGoodHeap h0@@1)) ($IsGoodHeap h1@@1)) ($Is HandleTypeType f@@1 (Tclass._System.___hFunc0 t0@@5))) (forall ((o@@2 T@U) (fld@@1 T@U) (a@@1 T@T) ) (!  (=> (and (or (not (= o@@2 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@5 h0@@1 f@@1) ($Box refType o@@2)))) (= ($Unbox a@@1 (MapType1Select a@@1 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@1 o@@2) fld@@1)) ($Unbox a@@1 (MapType1Select a@@1 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@1 o@@2) fld@@1))))
 :qid |testbpl.2440:22|
 :skolemid |428|
))) (= (Apply0 t0@@5 h0@@1 f@@1) (Apply0 t0@@5 h1@@1 f@@1)))
 :qid |testbpl.2433:15|
 :skolemid |429|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Apply0 t0@@5 h1@@1 f@@1))
)))
(assert (forall ((t0@@6 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@2 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@2 h1@@2) ($IsGoodHeap h0@@2)) ($IsGoodHeap h1@@2)) ($Is HandleTypeType f@@2 (Tclass._System.___hFunc0 t0@@6))) (forall ((o@@3 T@U) (fld@@2 T@U) (a@@2 T@T) ) (!  (=> (and (or (not (= o@@3 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@6 h1@@2 f@@2) ($Box refType o@@3)))) (= ($Unbox a@@2 (MapType1Select a@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@2 o@@3) fld@@2)) ($Unbox a@@2 (MapType1Select a@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@2 o@@3) fld@@2))))
 :qid |testbpl.2453:22|
 :skolemid |430|
))) (= (Apply0 t0@@6 h0@@2 f@@2) (Apply0 t0@@6 h1@@2 f@@2)))
 :qid |testbpl.2446:15|
 :skolemid |431|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Apply0 t0@@6 h1@@2 f@@2))
)))
(assert (forall ((t0@@7 T@U) (t1@@1 T@U) (heap T@U) (f@@3 T@U) (bx0 T@U) ) (!  (=> (and (and (and ($IsGoodHeap heap) ($IsBox BoxType bx0 t0@@7)) ($Is HandleTypeType f@@3 (Tclass._System.___hFunc1 t0@@7 t1@@1))) (|Set#Equal| BoxType (Reads1 t0@@7 t1@@1 $OneHeap f@@3 bx0) (|Set#Empty| BoxType))) (= (Requires1 t0@@7 t1@@1 $OneHeap f@@3 bx0) (Requires1 t0@@7 t1@@1 heap f@@3 bx0)))
 :qid |testbpl.2182:15|
 :skolemid |389|
 :pattern ( (Requires1 t0@@7 t1@@1 $OneHeap f@@3 bx0) ($IsGoodHeap heap))
 :pattern ( (Requires1 t0@@7 t1@@1 heap f@@3 bx0))
)))
(assert (forall ((v T@U) (h T@U) ) (! ($IsAlloc intType v (TBitvector 0) h)
 :qid |testbpl.346:15|
 :skolemid |65|
 :pattern ( ($IsAlloc intType v (TBitvector 0) h))
)))
(assert (forall ((_System.array$arg T@U) ($o T@U) ) (!  (=> (and (or (not (= $o null)) (not true)) (= (dtype $o) (Tclass._System.array? _System.array$arg))) ($Is intType (int_2_U (_System.array.Length $o)) TInt))
 :qid |testbpl.1953:15|
 :skolemid |362|
 :pattern ( (_System.array.Length $o) (Tclass._System.array? _System.array$arg))
)))
(assert (forall ((a@@3 T@U) (b T@U) (T T@T) ) (!  (and (= (+ (+ (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)) (|MultiSet#Card| T (|MultiSet#Difference| T b a@@3))) (* 2 (|MultiSet#Card| T (|MultiSet#Intersection| T a@@3 b)))) (|MultiSet#Card| T (|MultiSet#Union| T a@@3 b))) (= (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)) (- (|MultiSet#Card| T a@@3) (|MultiSet#Card| T (|MultiSet#Intersection| T a@@3 b)))))
 :qid |testbpl.1114:18|
 :skolemid |203|
 :pattern ( (|MultiSet#Card| T (|MultiSet#Difference| T a@@3 b)))
)))
(assert (forall ((h@@0 T@U) (k T@U) ) (!  (=> ($HeapSucc h@@0 k) (forall ((o@@4 T@U) ) (!  (=> (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@0 o@@4) alloc))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@4) alloc))))
 :qid |testbpl.725:18|
 :skolemid |117|
 :pattern ( ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@4) alloc)))
)))
 :qid |testbpl.722:15|
 :skolemid |118|
 :pattern ( ($HeapSucc h@@0 k))
)))
(assert (forall ((o@@5 T@U) (p T@U) (r T@U) ) (!  (=> (and (|ORD#Less| o@@5 p) (|ORD#Less| p r)) (|ORD#Less| o@@5 r))
 :qid |testbpl.500:15|
 :skolemid |89|
 :pattern ( (|ORD#Less| o@@5 p) (|ORD#Less| p r))
 :pattern ( (|ORD#Less| o@@5 p) (|ORD#Less| o@@5 r))
)))
(assert (forall ((|x#0| T@U) ($h T@U) ) (! ($IsAlloc intType |x#0| Tclass._System.nat $h)
 :qid |testbpl.1834:15|
 :skolemid |348|
 :pattern ( ($IsAlloc intType |x#0| Tclass._System.nat $h))
)))
(assert (forall ((d T@U) ) (!  (=> (|$IsA#_System.Tuple2| d) (_System.Tuple2.___hMake2_q d))
 :qid |testbpl.2711:15|
 :skolemid |470|
 :pattern ( (|$IsA#_System.Tuple2| d))
)))
(assert (forall ((d@@0 T@U) ) (!  (=> (|$IsA#_System.Tuple0| d@@0) (_System.Tuple0.___hMake0_q d@@0))
 :qid |testbpl.2795:15|
 :skolemid |478|
 :pattern ( (|$IsA#_System.Tuple0| d@@0))
)))
(assert (forall ((T@@0 T@T) ) (! (= (|MultiSet#FromSeq| T@@0 (|Seq#Empty| T@@0)) (|MultiSet#Empty| T@@0))
 :skolemid |213|
)))
(assert (forall ((_System.array$arg@@0 T@U) ($o@@0 T@U) ($h@@0 T@U) ) (! (= ($IsAlloc refType $o@@0 (Tclass._System.array? _System.array$arg@@0) $h@@0)  (or (= $o@@0 null) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@0 $o@@0) alloc)))))
 :qid |testbpl.1947:15|
 :skolemid |361|
 :pattern ( ($IsAlloc refType $o@@0 (Tclass._System.array? _System.array$arg@@0) $h@@0))
)))
(assert (forall ((s T@U) (v@@0 T@U) (x@@2 T@U) (T@@1 T@T) ) (! (= (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2)  (or (= v@@0 x@@2) (|Seq#Contains| T@@1 s x@@2)))
 :qid |testbpl.1300:18|
 :skolemid |240|
 :pattern ( (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2))
)))
(assert (forall ((a@@4 T@U) (b@@0 T@U) (t T@U) (U@@0 T@T) (V@@0 T@T) ) (! (= (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@4 b@@0 t)) a@@4)
 :qid |testbpl.1530:20|
 :skolemid |289|
 :pattern ( (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@4 b@@0 t)))
)))
(assert (forall ((a@@5 T@U) (b@@1 T@U) (t@@0 T@U) (U@@1 T@T) (V@@1 T@T) ) (! (= (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@5 b@@1 t@@0)) b@@1)
 :qid |testbpl.1534:20|
 :skolemid |290|
 :pattern ( (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@5 b@@1 t@@0)))
)))
(assert (forall ((a@@6 T@U) (b@@2 T@U) (t@@1 T@U) (U@@2 T@T) (V@@2 T@T) ) (! (= (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@6 b@@2 t@@1)) a@@6)
 :qid |testbpl.1662:20|
 :skolemid |319|
 :pattern ( (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@6 b@@2 t@@1)))
)))
(assert (forall ((a@@7 T@U) (b@@3 T@U) (t@@2 T@U) (U@@3 T@T) (V@@3 T@T) ) (! (= (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@7 b@@3 t@@2)) b@@3)
 :qid |testbpl.1666:20|
 :skolemid |320|
 :pattern ( (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@7 b@@3 t@@2)))
)))
(assert (forall ((v@@1 T@U) ) (! ($Is intType v@@1 (TBitvector 0))
 :qid |testbpl.278:15|
 :skolemid |44|
 :pattern ( ($Is intType v@@1 (TBitvector 0)))
)))
(assert (forall ((a@@8 Int) (b@@4 Int) ) (!  (or (= (|Math#min| a@@8 b@@4) a@@8) (= (|Math#min| a@@8 b@@4) b@@4))
 :qid |testbpl.1009:15|
 :skolemid |179|
 :pattern ( (|Math#min| a@@8 b@@4))
)))
(assert (forall (($o@@1 T@U) ($h@@1 T@U) ) (! (= ($IsAlloc refType $o@@1 Tclass._System.object? $h@@1)  (or (= $o@@1 null) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@1 $o@@1) alloc)))))
 :qid |testbpl.1854:15|
 :skolemid |351|
 :pattern ( ($IsAlloc refType $o@@1 Tclass._System.object? $h@@1))
)))
(assert (forall ((_System.array$arg@@1 T@U) (|c#0| T@U) ($h@@2 T@U) ) (! (= ($IsAlloc refType |c#0| (Tclass._System.array _System.array$arg@@1) $h@@2) ($IsAlloc refType |c#0| (Tclass._System.array? _System.array$arg@@1) $h@@2))
 :qid |testbpl.2000:15|
 :skolemid |368|
 :pattern ( ($IsAlloc refType |c#0| (Tclass._System.array _System.array$arg@@1) $h@@2))
)))
(assert (forall ((|#$R| T@U) (|f#0| T@U) ($h@@3 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hPartialFunc0 |#$R|) $h@@3) ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hFunc0 |#$R|) $h@@3))
 :qid |testbpl.2536:15|
 :skolemid |445|
 :pattern ( ($IsAlloc HandleTypeType |f#0| (Tclass._System.___hPartialFunc0 |#$R|) $h@@3))
)))
(assert (forall ((|#$R@@0| T@U) (|f#0@@0| T@U) ($h@@4 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hTotalFunc0 |#$R@@0|) $h@@4) ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hPartialFunc0 |#$R@@0|) $h@@4))
 :qid |testbpl.2572:15|
 :skolemid |450|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@0| (Tclass._System.___hTotalFunc0 |#$R@@0|) $h@@4))
)))
(assert (forall ((o@@6 T@U) (m@@5 Int) (n Int) ) (!  (=> (and (and (<= 0 m@@5) (<= 0 n)) (<= (+ m@@5 n) (|ORD#Offset| o@@6))) (= (|ORD#Minus| (|ORD#Minus| o@@6 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)) (|ORD#Minus| o@@6 (|ORD#FromNat| (+ m@@5 n)))))
 :qid |testbpl.549:15|
 :skolemid |97|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@6 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)))
)))
(assert (= (Ctor DatatypeTypeType) 7))
(assert (forall ((|_System._tuple#2$T0| T@U) (|_System._tuple#2$T1| T@U) (d@@1 T@U) ) (!  (=> ($Is DatatypeTypeType d@@1 (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)) (_System.Tuple2.___hMake2_q d@@1))
 :qid |testbpl.2716:15|
 :skolemid |471|
 :pattern ( (_System.Tuple2.___hMake2_q d@@1) ($Is DatatypeTypeType d@@1 (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)))
)))
(assert (forall ((a@@9 T@U) (b@@5 T@U) ) (!  (=> true (= (|_System.Tuple2#Equal| a@@9 b@@5)  (and (= (_System.Tuple2._0 a@@9) (_System.Tuple2._0 b@@5)) (= (_System.Tuple2._1 a@@9) (_System.Tuple2._1 b@@5)))))
 :qid |testbpl.2725:15|
 :skolemid |472|
 :pattern ( (|_System.Tuple2#Equal| a@@9 b@@5))
)))
(assert (forall ((x@@3 T@U) (T@@2 T@T) ) (!  (not (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
 :qid |testbpl.1291:18|
 :skolemid |238|
 :pattern ( (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
)))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((s@@0 T@U) (v@@2 T@U) (n@@0 Int) (T@@3 T@T) ) (!  (=> (and (<= 0 n@@0) (<= n@@0 (|Seq#Length| T@@3 s@@0))) (= (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0) (|Seq#Build| T@@3 (|Seq#Drop| T@@3 s@@0 n@@0) v@@2)))
 :qid |testbpl.1421:18|
 :skolemid |266|
 :pattern ( (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0))
)))
(assert  (and (and (forall ((arg0@@4 T@T) (arg1 T@T) ) (! (= (Ctor (MapType0Type arg0@@4 arg1)) 8)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@5 T@T) (arg1@@0 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@5 arg1@@0)) arg0@@5)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@5 arg1@@0))
))) (forall ((arg0@@6 T@T) (arg1@@1 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@6 arg1@@1)) arg1@@1)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@6 arg1@@1))
))))
(assert (forall ((v@@3 T@U) (t0@@8 T@U) ) (!  (=> ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@8)) ($IsGoodMultiSet BoxType v@@3))
 :qid |testbpl.293:15|
 :skolemid |51|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@8)))
)))
(assert (forall ((s@@1 T@U) (T@@4 T@T) ) (! ($IsGoodMultiSet T@@4 (|MultiSet#FromSeq| T@@4 s@@1))
 :qid |testbpl.1163:18|
 :skolemid |214|
 :pattern ( (|MultiSet#FromSeq| T@@4 s@@1))
)))
(assert (forall ((s@@2 T@U) (i Int) (v@@4 T@U) (n@@1 Int) (T@@5 T@T) ) (!  (=> (and (<= 0 n@@1) (< n@@1 (|Seq#Length| T@@5 s@@2))) (and (=> (= i n@@1) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) v@@4)) (=> (or (not (= i n@@1)) (not true)) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) (|Seq#Index| T@@5 s@@2 n@@1)))))
 :qid |testbpl.1276:18|
 :skolemid |235|
 :pattern ( (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1))
)))
(assert (forall ((a@@10 T@U) (b@@6 T@U) (T@@6 T@T) ) (! (= (|Set#Union| T@@6 (|Set#Union| T@@6 a@@10 b@@6) b@@6) (|Set#Union| T@@6 a@@10 b@@6))
 :qid |testbpl.852:18|
 :skolemid |140|
 :pattern ( (|Set#Union| T@@6 (|Set#Union| T@@6 a@@10 b@@6) b@@6))
)))
(assert (forall ((a@@11 T@U) (b@@7 T@U) (T@@7 T@T) ) (! (= (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@11 b@@7) b@@7) (|Set#Intersection| T@@7 a@@11 b@@7))
 :qid |testbpl.860:18|
 :skolemid |142|
 :pattern ( (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@11 b@@7) b@@7))
)))
(assert (forall ((a@@12 T@U) (b@@8 T@U) (T@@8 T@T) ) (! (= (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@12 b@@8) b@@8) (|ISet#Union| T@@8 a@@12 b@@8))
 :qid |testbpl.955:18|
 :skolemid |164|
 :pattern ( (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@12 b@@8) b@@8))
)))
(assert (forall ((a@@13 T@U) (b@@9 T@U) (T@@9 T@T) ) (! (= (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@13 b@@9) b@@9) (|ISet#Intersection| T@@9 a@@13 b@@9))
 :qid |testbpl.963:18|
 :skolemid |166|
 :pattern ( (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@13 b@@9) b@@9))
)))
(assert (forall ((a@@14 T@U) (b@@10 T@U) (T@@10 T@T) ) (! (= (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@14 b@@10) b@@10) (|MultiSet#Intersection| T@@10 a@@14 b@@10))
 :qid |testbpl.1094:18|
 :skolemid |199|
 :pattern ( (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@14 b@@10) b@@10))
)))
(assert (forall ((f@@4 T@U) (t0@@9 T@U) (t1@@2 T@U) (u0@@2 T@U) (u1@@0 T@U) ) (!  (=> (and (and ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 t0@@9 t1@@2)) (forall ((bx T@U) ) (!  (=> ($IsBox BoxType bx u0@@2) ($IsBox BoxType bx t0@@9))
 :qid |testbpl.2203:19|
 :skolemid |392|
 :pattern ( ($IsBox BoxType bx u0@@2))
 :pattern ( ($IsBox BoxType bx t0@@9))
))) (forall ((bx@@0 T@U) ) (!  (=> ($IsBox BoxType bx@@0 t1@@2) ($IsBox BoxType bx@@0 u1@@0))
 :qid |testbpl.2206:19|
 :skolemid |393|
 :pattern ( ($IsBox BoxType bx@@0 t1@@2))
 :pattern ( ($IsBox BoxType bx@@0 u1@@0))
))) ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 u0@@2 u1@@0)))
 :qid |testbpl.2200:15|
 :skolemid |394|
 :pattern ( ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 t0@@9 t1@@2)) ($Is HandleTypeType f@@4 (Tclass._System.___hFunc1 u0@@2 u1@@0)))
)))
(assert (forall ((s@@3 T@U) (t@@3 T@U) (n@@2 Int) (T@@11 T@T) ) (!  (=> (= n@@2 (|Seq#Length| T@@11 s@@3)) (and (= (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) s@@3) (= (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) t@@3)))
 :qid |testbpl.1366:18|
 :skolemid |255|
 :pattern ( (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
 :pattern ( (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@5 T@U) ) (! (= ($IsAlloc refType |c#0@@0| Tclass._System.object $h@@5) ($IsAlloc refType |c#0@@0| Tclass._System.object? $h@@5))
 :qid |testbpl.1883:15|
 :skolemid |354|
 :pattern ( ($IsAlloc refType |c#0@@0| Tclass._System.object $h@@5))
)))
(assert (forall ((m@@6 T@U) (u T@U) (v@@5 T@U) (U@@4 T@T) (V@@4 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@4 boolType (|Map#Domain| U@@4 V@@4 m@@6) u)) (= (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)) (|Map#Card| U@@4 V@@4 m@@6)))
 :qid |testbpl.1553:20|
 :skolemid |294|
 :pattern ( (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)))
)))
(assert (forall ((r@@0 T@U) (o@@7 T@U) (T@@12 T@T) ) (! (= (U_2_bool (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@7)) (= r@@0 o@@7))
 :qid |testbpl.798:18|
 :skolemid |128|
 :pattern ( (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@7))
)))
(assert (forall ((d@@2 T@U) ) (!  (=> ($Is DatatypeTypeType d@@2 Tclass._System.Tuple0) (_System.Tuple0.___hMake0_q d@@2))
 :qid |testbpl.2800:15|
 :skolemid |479|
 :pattern ( (_System.Tuple0.___hMake0_q d@@2) ($Is DatatypeTypeType d@@2 Tclass._System.Tuple0))
)))
(assert (forall ((s@@4 T@U) (x@@4 T@U) (T@@13 T@T) ) (! (= (exists ((i@@0 Int) ) (!  (and (and (<= 0 i@@0) (< i@@0 (|Seq#Length| T@@13 s@@4))) (= x@@4 (|Seq#Index| T@@13 s@@4 i@@0)))
 :qid |testbpl.1189:11|
 :skolemid |219|
 :pattern ( (|Seq#Index| T@@13 s@@4 i@@0))
)) (< 0 (U_2_int (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))))
 :qid |testbpl.1187:18|
 :skolemid |220|
 :pattern ( (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))
)))
(assert (forall ((|_System._tuple#2$T0@@0| T@U) (|_System._tuple#2$T1@@0| T@U) (|a#2#0#0| T@U) (|a#2#1#0| T@U) ) (! (= ($Is DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|))  (and ($IsBox BoxType |a#2#0#0| |_System._tuple#2$T0@@0|) ($IsBox BoxType |a#2#1#0| |_System._tuple#2$T1@@0|)))
 :qid |testbpl.2636:15|
 :skolemid |459|
 :pattern ( ($Is DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|)))
)))
(assert ($Is DatatypeTypeType |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall ((t0@@10 T@U) (heap@@0 T@U) (h@@1 T@U) (r@@1 T@U) (rd T@U) ) (! (= (Apply0 t0@@10 heap@@0 (Handle0 h@@1 r@@1 rd)) (MapType0Select (MapType0Type refType (MapType1Type BoxType)) BoxType h@@1 heap@@0))
 :qid |testbpl.2358:15|
 :skolemid |417|
 :pattern ( (Apply0 t0@@10 heap@@0 (Handle0 h@@1 r@@1 rd)))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly T@U) (|q#0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0|) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly) |q#0|) (> |q#0| 1234)))
 :qid |testbpl.2838:16|
 :skolemid |483|
 :pattern ( (_module.__default.secretPredicate ($LS $ly) |q#0|))
))))
(assert (forall ((a@@15 T@U) (b@@11 T@U) (T@@14 T@T) ) (! (= (+ (|Set#Card| T@@14 (|Set#Union| T@@14 a@@15 b@@11)) (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@15 b@@11))) (+ (|Set#Card| T@@14 a@@15) (|Set#Card| T@@14 b@@11)))
 :qid |testbpl.868:18|
 :skolemid |144|
 :pattern ( (|Set#Card| T@@14 (|Set#Union| T@@14 a@@15 b@@11)))
 :pattern ( (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@15 b@@11)))
)))
(assert (forall ((m@@7 T@U) (s@@5 T@U) (u@@0 T@U) (U@@5 T@T) (V@@5 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@5 boolType (|Map#Domain| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0)) (= (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0) (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 m@@7) u@@0)))
 :qid |testbpl.1579:20|
 :skolemid |299|
 :pattern ( (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0))
)))
(assert (forall ((m@@8 T@U) (s@@6 T@U) (u@@1 T@U) (U@@6 T@T) (V@@6 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@6 boolType (|IMap#Domain| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1)) (= (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1) (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 m@@8) u@@1)))
 :qid |testbpl.1720:20|
 :skolemid |331|
 :pattern ( (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1))
)))
(assert (forall ((h@@2 T@U) (a@@16 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@16))) (= (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n1) (|Seq#Build| BoxType (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n0) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@2 a@@16) (IndexField n0))))))
 :qid |testbpl.1415:15|
 :skolemid |265|
 :pattern ( (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n0) (|Seq#Take| BoxType (|Seq#FromArray| h@@2 a@@16) n1))
)))
(assert (forall ((s@@7 T@U) (i@@1 Int) (v@@6 T@U) (n@@3 Int) (T@@15 T@T) ) (!  (=> (and (and (<= 0 n@@3) (<= n@@3 i@@1)) (< i@@1 (|Seq#Length| T@@15 s@@7))) (= (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3) (|Seq#Update| T@@15 (|Seq#Drop| T@@15 s@@7 n@@3) (- i@@1 n@@3) v@@6)))
 :qid |testbpl.1405:18|
 :skolemid |263|
 :pattern ( (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) (o@@8 T@U) (T@@16 T@T) ) (! (= (U_2_int (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@17 b@@12) o@@8)) (+ (U_2_int (MapType0Select T@@16 intType a@@17 o@@8)) (U_2_int (MapType0Select T@@16 intType b@@12 o@@8))))
 :qid |testbpl.1080:18|
 :skolemid |196|
 :pattern ( (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@17 b@@12) o@@8))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) ) (! (= (|_System.Tuple2#Equal| a@@18 b@@13) (= a@@18 b@@13))
 :qid |testbpl.2733:15|
 :skolemid |473|
 :pattern ( (|_System.Tuple2#Equal| a@@18 b@@13))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) ) (! (= (|_System.Tuple0#Equal| a@@19 b@@14) (= a@@19 b@@14))
 :qid |testbpl.2813:15|
 :skolemid |481|
 :pattern ( (|_System.Tuple0#Equal| a@@19 b@@14))
)))
(assert (forall ((s@@8 T@U) (n@@4 Int) (T@@17 T@T) ) (!  (=> (= n@@4 0) (= (|Seq#Drop| T@@17 s@@8 n@@4) s@@8))
 :qid |testbpl.1446:18|
 :skolemid |271|
 :pattern ( (|Seq#Drop| T@@17 s@@8 n@@4))
)))
(assert (forall ((v@@7 T@U) (t0@@11 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@11)) (forall ((bx@@1 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@7 bx@@1)) ($IsBox BoxType bx@@1 t0@@11))
 :qid |testbpl.282:33|
 :skolemid |45|
 :pattern ( (MapType0Select BoxType boolType v@@7 bx@@1))
)))
 :qid |testbpl.280:15|
 :skolemid |46|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@11)))
)))
(assert (forall ((v@@8 T@U) (t0@@12 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@12)) (forall ((bx@@2 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@8 bx@@2)) ($IsBox BoxType bx@@2 t0@@12))
 :qid |testbpl.286:34|
 :skolemid |47|
 :pattern ( (MapType0Select BoxType boolType v@@8 bx@@2))
)))
 :qid |testbpl.284:15|
 :skolemid |48|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@12)))
)))
(assert (forall ((a@@20 Int) ) (!  (=> (<= 0 a@@20) (= (|Math#clip| a@@20) a@@20))
 :qid |testbpl.1015:15|
 :skolemid |180|
 :pattern ( (|Math#clip| a@@20))
)))
(assert (forall ((x@@5 Real) ) (! (= (q@Int x@@5) (to_int x@@5))
 :qid |testbpl.674:15|
 :skolemid |112|
 :pattern ( (q@Int x@@5))
)))
(assert (forall ((x@@6 Int) ) (! (= (LitInt x@@6) x@@6)
 :qid |testbpl.141:15|
 :skolemid |17|
 :pattern ( (LitInt x@@6))
)))
(assert (forall ((x@@7 Real) ) (! (= (LitReal x@@7) x@@7)
 :qid |testbpl.148:15|
 :skolemid |19|
 :pattern ( (LitReal x@@7))
)))
(assert (forall ((x@@8 T@U) (T@@18 T@T) ) (! (= (Lit T@@18 x@@8) x@@8)
 :qid |testbpl.134:18|
 :skolemid |15|
 :pattern ( (Lit T@@18 x@@8))
)))
(assert  (and (forall ((arg0@@7 T@T) ) (! (= (Ctor (SeqType arg0@@7)) 9)
 :qid |ctor:SeqType|
)) (forall ((arg0@@8 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@8)) arg0@@8)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@8))
))))
(assert (forall ((s@@9 T@U) (bx@@3 T@U) (t@@4 T@U) ) (!  (=> (and ($Is (SeqType BoxType) s@@9 (TSeq t@@4)) ($IsBox BoxType bx@@3 t@@4)) ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@3) (TSeq t@@4)))
 :qid |testbpl.1235:15|
 :skolemid |228|
 :pattern ( ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@3) (TSeq t@@4)))
)))
(assert $$Language$Dafny)
(assert (forall ((s@@10 T@U) (n@@5 Int) (j Int) (T@@19 T@T) ) (!  (=> (and (and (<= 0 j) (< j n@@5)) (< j (|Seq#Length| T@@19 s@@10))) (= (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j) (|Seq#Index| T@@19 s@@10 j)))
 :qid |testbpl.1345:18|
 :weight 25
 :skolemid |251|
 :pattern ( (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j))
 :pattern ( (|Seq#Index| T@@19 s@@10 j) (|Seq#Take| T@@19 s@@10 n@@5))
)))
(assert (forall ((|_System._tuple#2$T0@@1| T@U) (|_System._tuple#2$T1@@1| T@U) (|a#2#0#0@@0| T@U) (|a#2#1#0@@0| T@U) ($h@@6 T@U) ) (!  (=> ($IsGoodHeap $h@@6) (= ($IsAlloc DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0@@0| |a#2#1#0@@0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|) $h@@6)  (and ($IsAllocBox BoxType |a#2#0#0@@0| |_System._tuple#2$T0@@1| $h@@6) ($IsAllocBox BoxType |a#2#1#0@@0| |_System._tuple#2$T1@@1| $h@@6))))
 :qid |testbpl.2644:15|
 :skolemid |460|
 :pattern ( ($IsAlloc DatatypeTypeType (|#_System._tuple#2._#Make2| |a#2#0#0@@0| |a#2#1#0@@0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|) $h@@6))
)))
(assert (forall ((s@@11 T@U) (n@@6 Int) (T@@20 T@T) ) (!  (=> (and (<= 0 n@@6) (<= n@@6 (|Seq#Length| T@@20 s@@11))) (= (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)) (- (|Seq#Length| T@@20 s@@11) n@@6)))
 :qid |testbpl.1352:18|
 :skolemid |252|
 :pattern ( (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)))
)))
(assert (forall ((m@@9 T@U) (u@@2 T@U) (v@@9 T@U) (U@@7 T@T) (V@@7 T@T) ) (!  (=> (not (U_2_bool (MapType0Select U@@7 boolType (|Map#Domain| U@@7 V@@7 m@@9) u@@2))) (= (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)) (+ (|Map#Card| U@@7 V@@7 m@@9) 1)))
 :qid |testbpl.1557:20|
 :skolemid |295|
 :pattern ( (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)))
)))
(assert (forall ((d@@3 T@U) ) (! (= (_System.Tuple2.___hMake2_q d@@3) (= (DatatypeCtorId d@@3) |##_System._tuple#2._#Make2|))
 :qid |testbpl.2589:15|
 :skolemid |452|
 :pattern ( (_System.Tuple2.___hMake2_q d@@3))
)))
(assert (forall ((d@@4 T@U) ) (! (= (_System.Tuple0.___hMake0_q d@@4) (= (DatatypeCtorId d@@4) |##_System._tuple#0._#Make0|))
 :qid |testbpl.2759:15|
 :skolemid |474|
 :pattern ( (_System.Tuple0.___hMake0_q d@@4))
)))
(assert (forall ((s0@@1 T@U) (s1 T@U) (T@@21 T@T) ) (! (= (|Seq#Equal| T@@21 s0@@1 s1)  (and (= (|Seq#Length| T@@21 s0@@1) (|Seq#Length| T@@21 s1)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| T@@21 s0@@1))) (= (|Seq#Index| T@@21 s0@@1 j@@0) (|Seq#Index| T@@21 s1 j@@0)))
 :qid |testbpl.1324:19|
 :skolemid |245|
 :pattern ( (|Seq#Index| T@@21 s0@@1 j@@0))
 :pattern ( (|Seq#Index| T@@21 s1 j@@0))
))))
 :qid |testbpl.1320:18|
 :skolemid |246|
 :pattern ( (|Seq#Equal| T@@21 s0@@1 s1))
)))
(assert (forall ((a@@21 T@U) (b@@15 T@U) (o@@9 T@U) (T@@22 T@T) ) (! (= (U_2_int (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@21 b@@15) o@@9)) (|Math#clip| (- (U_2_int (MapType0Select T@@22 intType a@@21 o@@9)) (U_2_int (MapType0Select T@@22 intType b@@15 o@@9)))))
 :qid |testbpl.1106:18|
 :skolemid |201|
 :pattern ( (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@21 b@@15) o@@9))
)))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) true)))
(assert (forall ((s@@12 T@U) (i@@2 Int) (T@@23 T@T) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| T@@23 s@@12))) (< (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)) (|Seq#Rank| T@@23 s@@12)))
 :qid |testbpl.1437:18|
 :skolemid |269|
 :pattern ( (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)))
)))
(assert (forall ((t0@@13 T@U) (heap@@1 T@U) (f@@5 T@U) ) (!  (=> (and (and ($IsGoodHeap heap@@1) ($Is HandleTypeType f@@5 (Tclass._System.___hFunc0 t0@@13))) (|Set#Equal| BoxType (Reads0 t0@@13 $OneHeap f@@5) (|Set#Empty| BoxType))) (= (Requires0 t0@@13 $OneHeap f@@5) (Requires0 t0@@13 heap@@1 f@@5)))
 :qid |testbpl.2466:15|
 :skolemid |433|
 :pattern ( (Requires0 t0@@13 $OneHeap f@@5) ($IsGoodHeap heap@@1))
 :pattern ( (Requires0 t0@@13 heap@@1 f@@5))
)))
(assert (forall ((d@@5 T@U) ) (!  (=> (_System.Tuple2.___hMake2_q d@@5) (exists ((|a#1#0#0| T@U) (|a#1#1#0| T@U) ) (! (= d@@5 (|#_System._tuple#2._#Make2| |a#1#0#0| |a#1#1#0|))
 :qid |testbpl.2598:18|
 :skolemid |453|
)))
 :qid |testbpl.2595:15|
 :skolemid |454|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5))
)))
(assert (forall ((T@@24 T@T) ) (! (= (|Seq#Length| T@@24 (|Seq#Empty| T@@24)) 0)
 :skolemid |222|
 :pattern ( (|Seq#Empty| T@@24))
)))
(assert (forall ((s@@13 T@U) (bx@@4 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@4)) (U_2_bool (MapType0Select refType boolType s@@13 ($Unbox refType bx@@4))))
 :qid |testbpl.436:15|
 :skolemid |81|
 :pattern ( (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@4))
)))
(assert (forall ((d@@6 T@U) ) (!  (=> (_System.Tuple0.___hMake0_q d@@6) (= d@@6 |#_System._tuple#0._#Make0|))
 :qid |testbpl.2765:15|
 :skolemid |475|
 :pattern ( (_System.Tuple0.___hMake0_q d@@6))
)))
(assert (forall ((f@@6 T@U) (i@@3 Int) ) (! (= (FDim BoxType (MultiIndexField f@@6 i@@3)) (+ (FDim BoxType f@@6) 1))
 :qid |testbpl.614:15|
 :skolemid |104|
 :pattern ( (MultiIndexField f@@6 i@@3))
)))
(assert (forall ((a@@22 T@U) (x@@9 T@U) (T@@25 T@T) ) (! (= (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@22 x@@9)) (+ (|MultiSet#Card| T@@25 a@@22) 1))
 :qid |testbpl.1074:18|
 :skolemid |195|
 :pattern ( (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@22 x@@9)))
)))
(assert (forall ((s@@14 T@U) (i@@4 Int) (T@@26 T@T) ) (!  (=> (and (< 0 i@@4) (<= i@@4 (|Seq#Length| T@@26 s@@14))) (< (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)) (|Seq#Rank| T@@26 s@@14)))
 :qid |testbpl.1433:18|
 :skolemid |268|
 :pattern ( (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)))
)))
(assert (= (Ctor LayerTypeType) 10))
(assert (forall ((f@@7 T@U) (ly T@U) (A T@T) ) (! (= (AtLayer A f@@7 ly) (MapType0Select LayerTypeType A f@@7 ly))
 :qid |testbpl.589:18|
 :skolemid |100|
 :pattern ( (AtLayer A f@@7 ly))
)))
(assert (forall ((|x#0@@0| T@U) ) (! (= ($Is intType |x#0@@0| Tclass._System.nat) (<= (LitInt 0) (U_2_int |x#0@@0|)))
 :qid |testbpl.1829:15|
 :skolemid |347|
 :pattern ( ($Is intType |x#0@@0| Tclass._System.nat))
)))
(assert ($IsGhostField boolType alloc))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((s@@15 T@U) (v@@10 T@U) (T@@27 T@T) ) (! (= (|Seq#Length| T@@27 (|Seq#Build| T@@27 s@@15 v@@10)) (+ 1 (|Seq#Length| T@@27 s@@15)))
 :qid |testbpl.1226:18|
 :skolemid |226|
 :pattern ( (|Seq#Build| T@@27 s@@15 v@@10))
)))
(assert (forall ((ty T@U) (heap@@2 T@U) (len Int) (init T@U) (i@@5 Int) ) (!  (=> (and (and ($IsGoodHeap heap@@2) (<= 0 i@@5)) (< i@@5 len)) (= (|Seq#Index| BoxType (|Seq#Create| ty heap@@2 len init) i@@5) (Apply1 TInt ty heap@@2 init ($Box intType (int_2_U i@@5)))))
 :qid |testbpl.1246:15|
 :skolemid |230|
 :pattern ( (|Seq#Index| BoxType (|Seq#Create| ty heap@@2 len init) i@@5))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@0 T@U) (|q#0@@0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| (LitInt |q#0@@0|)) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)) (U_2_bool (Lit boolType (bool_2_U (> |q#0@@0| 1234))))))
 :qid |testbpl.2844:16|
 :weight 3
 :skolemid |484|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)))
))))
(assert (forall ((_System.array$arg@@2 T@U) (|c#0@@1| T@U) ) (! (= ($Is refType |c#0@@1| (Tclass._System.array _System.array$arg@@2))  (and ($Is refType |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (or (not (= |c#0@@1| null)) (not true))))
 :qid |testbpl.1994:15|
 :skolemid |367|
 :pattern ( ($Is refType |c#0@@1| (Tclass._System.array _System.array$arg@@2)))
)))
(assert (forall ((v@@11 T@U) (t@@5 T@U) (h@@3 T@U) (T@@28 T@T) ) (! (= ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@3) ($IsAlloc T@@28 v@@11 t@@5 h@@3))
 :qid |testbpl.262:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@3))
)))
(assert (forall ((h@@4 T@U) (k@@0 T@U) (bx@@5 T@U) (t@@6 T@U) ) (!  (=> ($HeapSucc h@@4 k@@0) (=> ($IsAllocBox BoxType bx@@5 t@@6 h@@4) ($IsAllocBox BoxType bx@@5 t@@6 k@@0)))
 :qid |testbpl.660:15|
 :skolemid |110|
 :pattern ( ($HeapSucc h@@4 k@@0) ($IsAllocBox BoxType bx@@5 t@@6 h@@4))
)))
(assert (forall ((h@@5 T@U) (k@@1 T@U) (v@@12 T@U) (t@@7 T@U) (T@@29 T@T) ) (!  (=> ($HeapSucc h@@5 k@@1) (=> ($IsAlloc T@@29 v@@12 t@@7 h@@5) ($IsAlloc T@@29 v@@12 t@@7 k@@1)))
 :qid |testbpl.656:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@5 k@@1) ($IsAlloc T@@29 v@@12 t@@7 h@@5))
)))
(assert (forall ((d@@7 T@U) (|_System._tuple#2$T0@@2| T@U) ($h@@7 T@U) ) (!  (=> (and (and ($IsGoodHeap $h@@7) (_System.Tuple2.___hMake2_q d@@7)) (exists ((|_System._tuple#2$T1@@2| T@U) ) (! ($IsAlloc DatatypeTypeType d@@7 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|) $h@@7)
 :qid |testbpl.2665:19|
 :skolemid |461|
 :pattern ( ($IsAlloc DatatypeTypeType d@@7 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|) $h@@7))
))) ($IsAllocBox BoxType (_System.Tuple2._0 d@@7) |_System._tuple#2$T0@@2| $h@@7))
 :qid |testbpl.2660:15|
 :skolemid |462|
 :pattern ( ($IsAllocBox BoxType (_System.Tuple2._0 d@@7) |_System._tuple#2$T0@@2| $h@@7))
)))
(assert (forall ((d@@8 T@U) (|_System._tuple#2$T1@@3| T@U) ($h@@8 T@U) ) (!  (=> (and (and ($IsGoodHeap $h@@8) (_System.Tuple2.___hMake2_q d@@8)) (exists ((|_System._tuple#2$T0@@3| T@U) ) (! ($IsAlloc DatatypeTypeType d@@8 (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|) $h@@8)
 :qid |testbpl.2676:19|
 :skolemid |463|
 :pattern ( ($IsAlloc DatatypeTypeType d@@8 (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|) $h@@8))
))) ($IsAllocBox BoxType (_System.Tuple2._1 d@@8) |_System._tuple#2$T1@@3| $h@@8))
 :qid |testbpl.2671:15|
 :skolemid |464|
 :pattern ( ($IsAllocBox BoxType (_System.Tuple2._1 d@@8) |_System._tuple#2$T1@@3| $h@@8))
)))
(assert (forall ((s@@16 T@U) (n@@7 Int) (j@@1 Int) (T@@30 T@T) ) (!  (=> (and (and (<= 0 n@@7) (<= 0 j@@1)) (< j@@1 (- (|Seq#Length| T@@30 s@@16) n@@7))) (= (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1) (|Seq#Index| T@@30 s@@16 (+ j@@1 n@@7))))
 :qid |testbpl.1356:18|
 :weight 25
 :skolemid |253|
 :pattern ( (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1))
)))
(assert (forall ((s@@17 T@U) (T@@31 T@T) ) (!  (and (= (= (|MultiSet#Card| T@@31 s@@17) 0) (= s@@17 (|MultiSet#Empty| T@@31))) (=> (or (not (= (|MultiSet#Card| T@@31 s@@17) 0)) (not true)) (exists ((x@@10 T@U) ) (! (< 0 (U_2_int (MapType0Select T@@31 intType s@@17 x@@10)))
 :qid |testbpl.1043:44|
 :skolemid |187|
))))
 :qid |testbpl.1040:18|
 :skolemid |188|
 :pattern ( (|MultiSet#Card| T@@31 s@@17))
)))
(assert (forall ((_System.array$arg@@3 T@U) ) (!  (and (= (Tag (Tclass._System.array? _System.array$arg@@3)) Tagclass._System.array?) (= (TagFamily (Tclass._System.array? _System.array$arg@@3)) tytagFamily$array))
 :qid |testbpl.1895:15|
 :skolemid |355|
 :pattern ( (Tclass._System.array? _System.array$arg@@3))
)))
(assert (forall ((_System.array$arg@@4 T@U) ) (!  (and (= (Tag (Tclass._System.array _System.array$arg@@4)) Tagclass._System.array) (= (TagFamily (Tclass._System.array _System.array$arg@@4)) tytagFamily$array))
 :qid |testbpl.1973:15|
 :skolemid |364|
 :pattern ( (Tclass._System.array _System.array$arg@@4))
)))
(assert (forall ((|#$R@@1| T@U) ) (!  (and (= (Tag (Tclass._System.___hFunc0 |#$R@@1|)) Tagclass._System.___hFunc0) (= (TagFamily (Tclass._System.___hFunc0 |#$R@@1|)) |tytagFamily$_#Func0|))
 :qid |testbpl.2331:15|
 :skolemid |414|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@1|))
)))
(assert (forall ((|#$R@@2| T@U) ) (!  (and (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@2|)) Tagclass._System.___hPartialFunc0) (= (TagFamily (Tclass._System.___hPartialFunc0 |#$R@@2|)) |tytagFamily$_#PartialFunc0|))
 :qid |testbpl.2509:15|
 :skolemid |441|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@2|))
)))
(assert (forall ((|#$R@@3| T@U) ) (!  (and (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@3|)) Tagclass._System.___hTotalFunc0) (= (TagFamily (Tclass._System.___hTotalFunc0 |#$R@@3|)) |tytagFamily$_#TotalFunc0|))
 :qid |testbpl.2546:15|
 :skolemid |446|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@3|))
)))
(assert (forall ((a@@23 T@U) (b@@16 T@U) (y T@U) (T@@32 T@T) ) (!  (=> (<= (U_2_int (MapType0Select T@@32 intType a@@23 y)) (U_2_int (MapType0Select T@@32 intType b@@16 y))) (= (U_2_int (MapType0Select T@@32 intType (|MultiSet#Difference| T@@32 a@@23 b@@16) y)) 0))
 :qid |testbpl.1110:18|
 :skolemid |202|
 :pattern ( (|MultiSet#Difference| T@@32 a@@23 b@@16) (MapType0Select T@@32 intType b@@16 y) (MapType0Select T@@32 intType a@@23 y))
)))
(assert (forall ((u@@3 T@U) (U@@8 T@T) (V@@8 T@T) ) (!  (not (U_2_bool (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3)))
 :qid |testbpl.1524:20|
 :skolemid |288|
 :pattern ( (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3))
)))
(assert (forall ((u@@4 T@U) (U@@9 T@T) (V@@9 T@T) ) (!  (not (U_2_bool (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4)))
 :qid |testbpl.1656:20|
 :skolemid |318|
 :pattern ( (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4))
)))
(assert (forall ((h@@6 T@U) (k@@2 T@U) ) (!  (=> ($HeapSuccGhost h@@6 k@@2) (and ($HeapSucc h@@6 k@@2) (forall ((o@@10 T@U) (f@@8 T@U) (alpha T@T) ) (!  (=> (not ($IsGhostField alpha f@@8)) (= ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) h@@6 o@@10) f@@8)) ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@10) f@@8))))
 :qid |testbpl.652:26|
 :skolemid |107|
 :pattern ( ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@10) f@@8)))
))))
 :qid |testbpl.648:15|
 :skolemid |108|
 :pattern ( ($HeapSuccGhost h@@6 k@@2))
)))
(assert (forall ((o@@11 T@U) (p@@0 T@U) ) (!  (=> (and (|ORD#IsNat| p@@0) (<= (|ORD#Offset| p@@0) (|ORD#Offset| o@@11))) (and (= (|ORD#IsNat| (|ORD#Minus| o@@11 p@@0)) (|ORD#IsNat| o@@11)) (= (|ORD#Offset| (|ORD#Minus| o@@11 p@@0)) (- (|ORD#Offset| o@@11) (|ORD#Offset| p@@0)))))
 :qid |testbpl.531:15|
 :skolemid |94|
 :pattern ( (|ORD#Minus| o@@11 p@@0))
)))
(assert (forall ((a@@24 T@U) (b@@17 T@U) (T@@33 T@T) ) (! (= (|Set#Equal| T@@33 a@@24 b@@17) (forall ((o@@12 T@U) ) (! (= (U_2_bool (MapType0Select T@@33 boolType a@@24 o@@12)) (U_2_bool (MapType0Select T@@33 boolType b@@17 o@@12)))
 :qid |testbpl.901:32|
 :skolemid |150|
 :pattern ( (MapType0Select T@@33 boolType a@@24 o@@12))
 :pattern ( (MapType0Select T@@33 boolType b@@17 o@@12))
)))
 :qid |testbpl.899:18|
 :skolemid |151|
 :pattern ( (|Set#Equal| T@@33 a@@24 b@@17))
)))
(assert (forall ((a@@25 T@U) (b@@18 T@U) (T@@34 T@T) ) (! (= (|ISet#Equal| T@@34 a@@25 b@@18) (forall ((o@@13 T@U) ) (! (= (U_2_bool (MapType0Select T@@34 boolType a@@25 o@@13)) (U_2_bool (MapType0Select T@@34 boolType b@@18 o@@13)))
 :qid |testbpl.991:33|
 :skolemid |172|
 :pattern ( (MapType0Select T@@34 boolType a@@25 o@@13))
 :pattern ( (MapType0Select T@@34 boolType b@@18 o@@13))
)))
 :qid |testbpl.989:18|
 :skolemid |173|
 :pattern ( (|ISet#Equal| T@@34 a@@25 b@@18))
)))
(assert (forall ((t0@@14 T@U) (t1@@3 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@9 T@U) (bx0@@0 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@3 h1@@3) ($IsGoodHeap h0@@3)) ($IsGoodHeap h1@@3)) ($IsBox BoxType bx0@@0 t0@@14)) ($Is HandleTypeType f@@9 (Tclass._System.___hFunc1 t0@@14 t1@@3))) (forall ((o@@14 T@U) (fld@@3 T@U) (a@@26 T@T) ) (!  (=> (and (or (not (= o@@14 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@14 t1@@3 h0@@3 f@@9 bx0@@0) ($Box refType o@@14)))) (= ($Unbox a@@26 (MapType1Select a@@26 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@3 o@@14) fld@@3)) ($Unbox a@@26 (MapType1Select a@@26 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@3 o@@14) fld@@3))))
 :qid |testbpl.2123:22|
 :skolemid |380|
))) (= (Requires1 t0@@14 t1@@3 h0@@3 f@@9 bx0@@0) (Requires1 t0@@14 t1@@3 h1@@3 f@@9 bx0@@0)))
 :qid |testbpl.2114:15|
 :skolemid |381|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires1 t0@@14 t1@@3 h1@@3 f@@9 bx0@@0))
)))
(assert (forall ((t0@@15 T@U) (t1@@4 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@10 T@U) (bx0@@1 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@4 h1@@4) ($IsGoodHeap h0@@4)) ($IsGoodHeap h1@@4)) ($IsBox BoxType bx0@@1 t0@@15)) ($Is HandleTypeType f@@10 (Tclass._System.___hFunc1 t0@@15 t1@@4))) (forall ((o@@15 T@U) (fld@@4 T@U) (a@@27 T@T) ) (!  (=> (and (or (not (= o@@15 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1) ($Box refType o@@15)))) (= ($Unbox a@@27 (MapType1Select a@@27 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@4 o@@15) fld@@4)) ($Unbox a@@27 (MapType1Select a@@27 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@4 o@@15) fld@@4))))
 :qid |testbpl.2138:22|
 :skolemid |382|
))) (= (Requires1 t0@@15 t1@@4 h0@@4 f@@10 bx0@@1) (Requires1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1)))
 :qid |testbpl.2129:15|
 :skolemid |383|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Requires1 t0@@15 t1@@4 h1@@4 f@@10 bx0@@1))
)))
(assert (forall ((a@@28 T@U) (b@@19 T@U) (T@@35 T@T) ) (! (= (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@28 b@@19)) (+ (|MultiSet#Card| T@@35 a@@28) (|MultiSet#Card| T@@35 b@@19)))
 :qid |testbpl.1084:18|
 :skolemid |197|
 :pattern ( (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@28 b@@19)))
)))
(assert (forall ((s0@@2 T@U) (s1@@0 T@U) (T@@36 T@T) ) (! (= (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)) (+ (|Seq#Length| T@@36 s0@@2) (|Seq#Length| T@@36 s1@@0)))
 :qid |testbpl.1254:18|
 :skolemid |231|
 :pattern ( (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)))
)))
(assert (forall ((n@@8 Int) ) (!  (=> (<= 0 n@@8) (and (|ORD#IsNat| (|ORD#FromNat| n@@8)) (= (|ORD#Offset| (|ORD#FromNat| n@@8)) n@@8)))
 :qid |testbpl.478:15|
 :skolemid |85|
 :pattern ( (|ORD#FromNat| n@@8))
)))
(assert (forall ((|#$T0| T@U) (|#$R@@4| T@U) (|f#0@@1| T@U) ($h@@9 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0| |#$R@@4|) $h@@9) ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hFunc1 |#$T0| |#$R@@4|) $h@@9))
 :qid |testbpl.2275:15|
 :skolemid |406|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0| |#$R@@4|) $h@@9))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$R@@5| T@U) (|f#0@@2| T@U) ($h@@10 T@U) ) (! (= ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@0| |#$R@@5|) $h@@10) ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@0| |#$R@@5|) $h@@10))
 :qid |testbpl.2321:15|
 :skolemid |413|
 :pattern ( ($IsAlloc HandleTypeType |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@0| |#$R@@5|) $h@@10))
)))
(assert (forall ((ms T@U) (T@@37 T@T) ) (! (= ($IsGoodMultiSet T@@37 ms) (forall ((bx@@6 T@U) ) (!  (and (<= 0 (U_2_int (MapType0Select T@@37 intType ms bx@@6))) (<= (U_2_int (MapType0Select T@@37 intType ms bx@@6)) (|MultiSet#Card| T@@37 ms)))
 :qid |testbpl.1026:19|
 :skolemid |182|
 :pattern ( (MapType0Select T@@37 intType ms bx@@6))
)))
 :qid |testbpl.1023:18|
 :skolemid |183|
 :pattern ( ($IsGoodMultiSet T@@37 ms))
)))
(assert (forall ((o@@16 T@U) (p@@1 T@U) ) (!  (and (or (= o@@16 (|ORD#Plus| o@@16 p@@1)) (|ORD#Less| o@@16 (|ORD#Plus| o@@16 p@@1))) (or (= p@@1 (|ORD#Plus| o@@16 p@@1)) (|ORD#Less| p@@1 (|ORD#Plus| o@@16 p@@1))))
 :qid |testbpl.519:15|
 :skolemid |92|
 :pattern ( (|ORD#Plus| o@@16 p@@1))
)))
(assert  (and (forall ((t0@@16 T@T) (t1@@5 T@T) (t2 T@T) (val@@4 T@U) (m@@10 T@U) (x0@@4 T@U) (x1 T@U) ) (! (= (MapType2Select t0@@16 t1@@5 t2 (MapType2Store t0@@16 t1@@5 t2 m@@10 x0@@4 x1 val@@4) x0@@4 x1) val@@4)
 :qid |mapAx0:MapType2Select|
 :weight 0
)) (and (forall ((u0@@3 T@T) (u1@@1 T@T) (u2 T@T) (val@@5 T@U) (m@@11 T@U) (x0@@5 T@U) (x1@@0 T@U) (y0@@2 T@U) (y1 T@U) ) (!  (or (= x0@@5 y0@@2) (= (MapType2Select u0@@3 u1@@1 u2 (MapType2Store u0@@3 u1@@1 u2 m@@11 x0@@5 x1@@0 val@@5) y0@@2 y1) (MapType2Select u0@@3 u1@@1 u2 m@@11 y0@@2 y1)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
)) (forall ((u0@@4 T@T) (u1@@2 T@T) (u2@@0 T@T) (val@@6 T@U) (m@@12 T@U) (x0@@6 T@U) (x1@@1 T@U) (y0@@3 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType2Select u0@@4 u1@@2 u2@@0 (MapType2Store u0@@4 u1@@2 u2@@0 m@@12 x0@@6 x1@@1 val@@6) y0@@3 y1@@0) (MapType2Select u0@@4 u1@@2 u2@@0 m@@12 y0@@3 y1@@0)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
)))))
(assert (forall ((t0@@17 T@U) (t1@@6 T@U) (heap@@3 T@U) (h@@7 T@U) (r@@2 T@U) (rd@@0 T@U) (bx0@@2 T@U) ) (! (= (Apply1 t0@@17 t1@@6 heap@@3 (Handle1 h@@7 r@@2 rd@@0) bx0@@2) (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType BoxType h@@7 heap@@3 bx0@@2))
 :qid |testbpl.2042:15|
 :skolemid |373|
 :pattern ( (Apply1 t0@@17 t1@@6 heap@@3 (Handle1 h@@7 r@@2 rd@@0) bx0@@2))
)))
(assert (forall ((bx@@7 T@U) ) (!  (=> ($IsBox BoxType bx@@7 Tclass._System.nat) (and (= ($Box intType ($Unbox intType bx@@7)) bx@@7) ($Is intType ($Unbox intType bx@@7) Tclass._System.nat)))
 :qid |testbpl.1823:15|
 :skolemid |346|
 :pattern ( ($IsBox BoxType bx@@7 Tclass._System.nat))
)))
(assert (forall ((bx@@8 T@U) ) (!  (=> ($IsBox BoxType bx@@8 Tclass._System.object?) (and (= ($Box refType ($Unbox refType bx@@8)) bx@@8) ($Is refType ($Unbox refType bx@@8) Tclass._System.object?)))
 :qid |testbpl.1843:15|
 :skolemid |349|
 :pattern ( ($IsBox BoxType bx@@8 Tclass._System.object?))
)))
(assert (forall ((bx@@9 T@U) ) (!  (=> ($IsBox BoxType bx@@9 Tclass._System.object) (and (= ($Box refType ($Unbox refType bx@@9)) bx@@9) ($Is refType ($Unbox refType bx@@9) Tclass._System.object)))
 :qid |testbpl.1871:15|
 :skolemid |352|
 :pattern ( ($IsBox BoxType bx@@9 Tclass._System.object))
)))
(assert (forall ((bx@@10 T@U) ) (!  (=> ($IsBox BoxType bx@@10 Tclass._System.Tuple0) (and (= ($Box DatatypeTypeType ($Unbox DatatypeTypeType bx@@10)) bx@@10) ($Is DatatypeTypeType ($Unbox DatatypeTypeType bx@@10) Tclass._System.Tuple0)))
 :qid |testbpl.2779:15|
 :skolemid |476|
 :pattern ( ($IsBox BoxType bx@@10 Tclass._System.Tuple0))
)))
(assert (forall ((_System.array$arg@@5 T@U) ($o@@2 T@U) ) (! (= ($Is refType $o@@2 (Tclass._System.array? _System.array$arg@@5))  (or (= $o@@2 null) (= (dtype $o@@2) (Tclass._System.array? _System.array$arg@@5))))
 :qid |testbpl.1941:15|
 :skolemid |360|
 :pattern ( ($Is refType $o@@2 (Tclass._System.array? _System.array$arg@@5)))
)))
(assert (forall ((a@@29 T@U) (x@@11 T@U) (T@@38 T@T) ) (! (= (U_2_int (MapType0Select T@@38 intType (|MultiSet#UnionOne| T@@38 a@@29 x@@11) x@@11)) (+ (U_2_int (MapType0Select T@@38 intType a@@29 x@@11)) 1))
 :qid |testbpl.1062:18|
 :skolemid |192|
 :pattern ( (|MultiSet#UnionOne| T@@38 a@@29 x@@11))
)))
(assert (forall ((|c#0@@2| T@U) ) (! (= ($Is refType |c#0@@2| Tclass._System.object)  (and ($Is refType |c#0@@2| Tclass._System.object?) (or (not (= |c#0@@2| null)) (not true))))
 :qid |testbpl.1877:15|
 :skolemid |353|
 :pattern ( ($Is refType |c#0@@2| Tclass._System.object))
)))
(assert (forall ((s@@18 T@U) (i@@6 Int) (v@@13 T@U) (T@@39 T@T) ) (!  (and (=> (= i@@6 (|Seq#Length| T@@39 s@@18)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) v@@13)) (=> (or (not (= i@@6 (|Seq#Length| T@@39 s@@18))) (not true)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) (|Seq#Index| T@@39 s@@18 i@@6))))
 :qid |testbpl.1230:18|
 :skolemid |227|
 :pattern ( (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6))
)))
(assert (forall ((a@@30 T@U) (b@@20 T@U) ) (! (= (|char#Minus| a@@30 b@@20) (|char#FromInt| (- (|char#ToInt| a@@30) (|char#ToInt| b@@20))))
 :qid |testbpl.180:15|
 :skolemid |24|
 :pattern ( (|char#Minus| a@@30 b@@20))
)))
(assert (forall ((a@@31 T@U) (b@@21 T@U) ) (! (= (|char#Plus| a@@31 b@@21) (|char#FromInt| (+ (|char#ToInt| a@@31) (|char#ToInt| b@@21))))
 :qid |testbpl.174:15|
 :skolemid |23|
 :pattern ( (|char#Plus| a@@31 b@@21))
)))
(assert (forall ((a@@32 T@U) (x@@12 T@U) (y@@0 T@U) (T@@40 T@T) ) (!  (=> (< 0 (U_2_int (MapType0Select T@@40 intType a@@32 y@@0))) (< 0 (U_2_int (MapType0Select T@@40 intType (|MultiSet#UnionOne| T@@40 a@@32 x@@12) y@@0))))
 :qid |testbpl.1066:18|
 :skolemid |193|
 :pattern ( (|MultiSet#UnionOne| T@@40 a@@32 x@@12) (MapType0Select T@@40 intType a@@32 y@@0))
)))
(assert (forall ((m@@13 T@U) (U@@10 T@T) (V@@10 T@T) ) (!  (or (= m@@13 (|Map#Empty| U@@10 V@@10)) (exists ((k@@3 T@U) ) (! (U_2_bool (MapType0Select U@@10 boolType (|Map#Domain| U@@10 V@@10 m@@13) k@@3))
 :qid |testbpl.1475:31|
 :skolemid |276|
)))
 :qid |testbpl.1473:20|
 :skolemid |277|
 :pattern ( (|Map#Domain| U@@10 V@@10 m@@13))
)))
(assert (forall ((m@@14 T@U) (U@@11 T@T) (V@@11 T@T) ) (!  (or (= m@@14 (|Map#Empty| U@@11 V@@11)) (exists ((v@@14 T@U) ) (! (U_2_bool (MapType0Select V@@11 boolType (|Map#Values| U@@11 V@@11 m@@14) v@@14))
 :qid |testbpl.1479:31|
 :skolemid |278|
)))
 :qid |testbpl.1477:20|
 :skolemid |279|
 :pattern ( (|Map#Values| U@@11 V@@11 m@@14))
)))
(assert (forall ((m@@15 T@U) (U@@12 T@T) (V@@12 T@T) ) (!  (or (= m@@15 (|IMap#Empty| U@@12 V@@12)) (exists ((k@@4 T@U) ) (! (U_2_bool (MapType0Select U@@12 boolType (|IMap#Domain| U@@12 V@@12 m@@15) k@@4))
 :qid |testbpl.1613:32|
 :skolemid |306|
)))
 :qid |testbpl.1611:20|
 :skolemid |307|
 :pattern ( (|IMap#Domain| U@@12 V@@12 m@@15))
)))
(assert (forall ((m@@16 T@U) (U@@13 T@T) (V@@13 T@T) ) (!  (or (= m@@16 (|IMap#Empty| U@@13 V@@13)) (exists ((v@@15 T@U) ) (! (U_2_bool (MapType0Select V@@13 boolType (|IMap#Values| U@@13 V@@13 m@@16) v@@15))
 :qid |testbpl.1617:32|
 :skolemid |308|
)))
 :qid |testbpl.1615:20|
 :skolemid |309|
 :pattern ( (|IMap#Values| U@@13 V@@13 m@@16))
)))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate0)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate0)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate0) MoreFuel__module._default.secretPredicate0)) (= _module.__default.magicNum (LitInt 15213))))))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate1)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate1)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate1) MoreFuel__module._default.secretPredicate1)) (= _module.__default.magicNum (LitInt 15213))))))
(assert (forall ((a@@33 T@U) (x@@13 T@U) (o@@17 T@U) (T@@41 T@T) ) (! (= (< 0 (U_2_int (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@33 x@@13) o@@17)))  (or (= o@@17 x@@13) (< 0 (U_2_int (MapType0Select T@@41 intType a@@33 o@@17)))))
 :qid |testbpl.1058:18|
 :skolemid |191|
 :pattern ( (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@33 x@@13) o@@17))
)))
(assert (forall ((h@@8 T@U) (a@@34 T@U) ) (! (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (|Seq#Length| BoxType (|Seq#FromArray| h@@8 a@@34)))) (= (|Seq#Index| BoxType (|Seq#FromArray| h@@8 a@@34) i@@7) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@8 a@@34) (IndexField i@@7)))))
 :qid |testbpl.1379:11|
 :skolemid |257|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@8 a@@34) (IndexField i@@7))))
 :pattern ( (|Seq#Index| BoxType (|Seq#FromArray| h@@8 a@@34) i@@7))
))
 :qid |testbpl.1377:15|
 :skolemid |258|
 :pattern ( (|Seq#FromArray| h@@8 a@@34))
)))
(assert (forall ((v@@16 T@U) (t0@@18 T@U) ) (! (= ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@18)) (forall ((bx@@11 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@16 bx@@11))) ($IsBox BoxType bx@@11 t0@@18))
 :qid |testbpl.291:19|
 :skolemid |49|
 :pattern ( (MapType0Select BoxType intType v@@16 bx@@11))
)))
 :qid |testbpl.288:15|
 :skolemid |50|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@18)))
)))
(assert (forall ((s0@@3 T@U) (s1@@1 T@U) (x@@14 T@U) (T@@42 T@T) ) (! (= (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14)  (or (|Seq#Contains| T@@42 s0@@3 x@@14) (|Seq#Contains| T@@42 s1@@1 x@@14)))
 :qid |testbpl.1295:18|
 :skolemid |239|
 :pattern ( (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14))
)))
(assert (forall ((s@@19 T@U) (n@@9 Int) (x@@15 T@U) (T@@43 T@T) ) (! (= (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15) (exists ((i@@8 Int) ) (!  (and (and (and (<= 0 i@@8) (< i@@8 n@@9)) (< i@@8 (|Seq#Length| T@@43 s@@19))) (= (|Seq#Index| T@@43 s@@19 i@@8) x@@15))
 :qid |testbpl.1307:19|
 :skolemid |241|
 :pattern ( (|Seq#Index| T@@43 s@@19 i@@8))
)))
 :qid |testbpl.1304:18|
 :skolemid |242|
 :pattern ( (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15))
)))
(assert (forall ((a@@35 T@U) (b@@22 T@U) (T@@44 T@T) ) (!  (=> (|Set#Disjoint| T@@44 a@@35 b@@22) (and (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@35 b@@22) a@@35) b@@22) (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@35 b@@22) b@@22) a@@35)))
 :qid |testbpl.840:18|
 :skolemid |138|
 :pattern ( (|Set#Union| T@@44 a@@35 b@@22))
)))
(assert (forall ((a@@36 T@U) (b@@23 T@U) (T@@45 T@T) ) (!  (=> (|ISet#Disjoint| T@@45 a@@36 b@@23) (and (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@36 b@@23) a@@36) b@@23) (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@36 b@@23) b@@23) a@@36)))
 :qid |testbpl.943:18|
 :skolemid |162|
 :pattern ( (|ISet#Union| T@@45 a@@36 b@@23))
)))
(assert (forall ((f@@11 T@U) (t0@@19 T@U) (t1@@7 T@U) (h@@9 T@U) ) (!  (=> (and ($IsGoodHeap h@@9) ($IsAlloc HandleTypeType f@@11 (Tclass._System.___hFunc1 t0@@19 t1@@7) h@@9)) (forall ((bx0@@3 T@U) ) (!  (=> (and ($IsAllocBox BoxType bx0@@3 t0@@19 h@@9) (Requires1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3)) ($IsAllocBox BoxType (Apply1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3) t1@@7 h@@9))
 :qid |testbpl.2225:18|
 :skolemid |398|
 :pattern ( (Apply1 t0@@19 t1@@7 h@@9 f@@11 bx0@@3))
)))
 :qid |testbpl.2222:15|
 :skolemid |399|
 :pattern ( ($IsAlloc HandleTypeType f@@11 (Tclass._System.___hFunc1 t0@@19 t1@@7) h@@9))
)))
(assert (forall ((a@@37 T@U) (b@@24 T@U) (T@@46 T@T) ) (! (= (|MultiSet#Equal| T@@46 a@@37 b@@24) (forall ((o@@18 T@U) ) (! (= (U_2_int (MapType0Select T@@46 intType a@@37 o@@18)) (U_2_int (MapType0Select T@@46 intType b@@24 o@@18)))
 :qid |testbpl.1133:37|
 :skolemid |206|
 :pattern ( (MapType0Select T@@46 intType a@@37 o@@18))
 :pattern ( (MapType0Select T@@46 intType b@@24 o@@18))
)))
 :qid |testbpl.1131:18|
 :skolemid |207|
 :pattern ( (|MultiSet#Equal| T@@46 a@@37 b@@24))
)))
(assert (forall ((a@@38 T@U) (b@@25 T@U) (T@@47 T@T) ) (! (= (|MultiSet#Subset| T@@47 a@@38 b@@25) (forall ((o@@19 T@U) ) (! (<= (U_2_int (MapType0Select T@@47 intType a@@38 o@@19)) (U_2_int (MapType0Select T@@47 intType b@@25 o@@19)))
 :qid |testbpl.1127:38|
 :skolemid |204|
 :pattern ( (MapType0Select T@@47 intType a@@38 o@@19))
 :pattern ( (MapType0Select T@@47 intType b@@25 o@@19))
)))
 :qid |testbpl.1125:18|
 :skolemid |205|
 :pattern ( (|MultiSet#Subset| T@@47 a@@38 b@@25))
)))
(assert (forall ((t0@@20 T@U) (t1@@8 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@12 T@U) (bx0@@4 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@5 h1@@5) ($IsGoodHeap h0@@5)) ($IsGoodHeap h1@@5)) ($IsBox BoxType bx0@@4 t0@@20)) ($Is HandleTypeType f@@12 (Tclass._System.___hFunc1 t0@@20 t1@@8))) (forall ((o@@20 T@U) (fld@@5 T@U) (a@@39 T@T) ) (!  (=> (and (or (not (= o@@20 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@20 t1@@8 h0@@5 f@@12 bx0@@4) ($Box refType o@@20)))) (= ($Unbox a@@39 (MapType1Select a@@39 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@5 o@@20) fld@@5)) ($Unbox a@@39 (MapType1Select a@@39 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@5 o@@20) fld@@5))))
 :qid |testbpl.2093:22|
 :skolemid |376|
))) (= (Reads1 t0@@20 t1@@8 h0@@5 f@@12 bx0@@4) (Reads1 t0@@20 t1@@8 h1@@5 f@@12 bx0@@4)))
 :qid |testbpl.2084:15|
 :skolemid |377|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Reads1 t0@@20 t1@@8 h1@@5 f@@12 bx0@@4))
)))
(assert (forall ((t0@@21 T@U) (t1@@9 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@13 T@U) (bx0@@5 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@6 h1@@6) ($IsGoodHeap h0@@6)) ($IsGoodHeap h1@@6)) ($IsBox BoxType bx0@@5 t0@@21)) ($Is HandleTypeType f@@13 (Tclass._System.___hFunc1 t0@@21 t1@@9))) (forall ((o@@21 T@U) (fld@@6 T@U) (a@@40 T@T) ) (!  (=> (and (or (not (= o@@21 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5) ($Box refType o@@21)))) (= ($Unbox a@@40 (MapType1Select a@@40 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@6 o@@21) fld@@6)) ($Unbox a@@40 (MapType1Select a@@40 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@6 o@@21) fld@@6))))
 :qid |testbpl.2108:22|
 :skolemid |378|
))) (= (Reads1 t0@@21 t1@@9 h0@@6 f@@13 bx0@@5) (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5)))
 :qid |testbpl.2099:15|
 :skolemid |379|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads1 t0@@21 t1@@9 h1@@6 f@@13 bx0@@5))
)))
(assert (forall ((t0@@22 T@U) (t1@@10 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@14 T@U) (bx0@@6 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@7 h1@@7) ($IsGoodHeap h0@@7)) ($IsGoodHeap h1@@7)) ($IsBox BoxType bx0@@6 t0@@22)) ($Is HandleTypeType f@@14 (Tclass._System.___hFunc1 t0@@22 t1@@10))) (forall ((o@@22 T@U) (fld@@7 T@U) (a@@41 T@T) ) (!  (=> (and (or (not (= o@@22 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@22 t1@@10 h0@@7 f@@14 bx0@@6) ($Box refType o@@22)))) (= ($Unbox a@@41 (MapType1Select a@@41 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@7 o@@22) fld@@7)) ($Unbox a@@41 (MapType1Select a@@41 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@7 o@@22) fld@@7))))
 :qid |testbpl.2153:22|
 :skolemid |384|
))) (= (Apply1 t0@@22 t1@@10 h0@@7 f@@14 bx0@@6) (Apply1 t0@@22 t1@@10 h1@@7 f@@14 bx0@@6)))
 :qid |testbpl.2144:15|
 :skolemid |385|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Apply1 t0@@22 t1@@10 h1@@7 f@@14 bx0@@6))
)))
(assert (forall ((t0@@23 T@U) (t1@@11 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@15 T@U) (bx0@@7 T@U) ) (!  (=> (and (and (and (and (and ($HeapSucc h0@@8 h1@@8) ($IsGoodHeap h0@@8)) ($IsGoodHeap h1@@8)) ($IsBox BoxType bx0@@7 t0@@23)) ($Is HandleTypeType f@@15 (Tclass._System.___hFunc1 t0@@23 t1@@11))) (forall ((o@@23 T@U) (fld@@8 T@U) (a@@42 T@T) ) (!  (=> (and (or (not (= o@@23 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7) ($Box refType o@@23)))) (= ($Unbox a@@42 (MapType1Select a@@42 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@8 o@@23) fld@@8)) ($Unbox a@@42 (MapType1Select a@@42 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@8 o@@23) fld@@8))))
 :qid |testbpl.2168:22|
 :skolemid |386|
))) (= (Apply1 t0@@23 t1@@11 h0@@8 f@@15 bx0@@7) (Apply1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7)))
 :qid |testbpl.2159:15|
 :skolemid |387|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Apply1 t0@@23 t1@@11 h1@@8 f@@15 bx0@@7))
)))
(assert (forall ((m@@17 T@U) (U@@14 T@T) (V@@14 T@T) ) (! (= (= (|Map#Card| U@@14 V@@14 m@@17) 0) (= m@@17 (|Map#Empty| U@@14 V@@14)))
 :qid |testbpl.1469:20|
 :skolemid |275|
 :pattern ( (|Map#Card| U@@14 V@@14 m@@17))
)))
(assert (forall ((a@@43 T@U) (b@@26 T@U) ) (!  (=> true (= (|_System.Tuple0#Equal| a@@43 b@@26) true))
 :qid |testbpl.2808:15|
 :skolemid |480|
 :pattern ( (|_System.Tuple0#Equal| a@@43 b@@26))
)))
(assert (forall ((s@@20 T@U) (x@@16 T@U) (T@@48 T@T) ) (! (= (|Seq#Contains| T@@48 s@@20 x@@16) (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| T@@48 s@@20))) (= (|Seq#Index| T@@48 s@@20 i@@9) x@@16))
 :qid |testbpl.1287:19|
 :skolemid |236|
 :pattern ( (|Seq#Index| T@@48 s@@20 i@@9))
)))
 :qid |testbpl.1284:18|
 :skolemid |237|
 :pattern ( (|Seq#Contains| T@@48 s@@20 x@@16))
)))
(assert (forall (($ly@@1 T@U) (|q#0@@1| Int) ) (! (= (|_module.__default.secretPredicate#requires| $ly@@1 |q#0@@1|) true)
 :qid |testbpl.2868:15|
 :skolemid |487|
 :pattern ( (|_module.__default.secretPredicate#requires| $ly@@1 |q#0@@1|))
)))
(assert (forall ((f@@16 T@U) (t0@@24 T@U) (t1@@12 T@U) (h@@10 T@U) ) (!  (=> ($IsGoodHeap h@@10) (= ($IsAlloc HandleTypeType f@@16 (Tclass._System.___hFunc1 t0@@24 t1@@12) h@@10) (forall ((bx0@@8 T@U) ) (!  (=> (and (and ($IsBox BoxType bx0@@8 t0@@24) ($IsAllocBox BoxType bx0@@8 t0@@24 h@@10)) (Requires1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8)) (forall ((r@@3 T@U) ) (!  (=> (and (or (not (= r@@3 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8) ($Box refType r@@3)))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@10 r@@3) alloc))))
 :qid |testbpl.2218:24|
 :skolemid |395|
 :pattern ( (MapType0Select BoxType boolType (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8) ($Box refType r@@3)))
)))
 :qid |testbpl.2215:21|
 :skolemid |396|
 :pattern ( (Apply1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8))
 :pattern ( (Reads1 t0@@24 t1@@12 h@@10 f@@16 bx0@@8))
))))
 :qid |testbpl.2211:15|
 :skolemid |397|
 :pattern ( ($IsAlloc HandleTypeType f@@16 (Tclass._System.___hFunc1 t0@@24 t1@@12) h@@10))
)))
(assert (forall ((s@@21 T@U) (i@@10 Int) (v@@17 T@U) (n@@10 Int) (T@@49 T@T) ) (!  (=> (and (and (<= 0 i@@10) (< i@@10 n@@10)) (<= n@@10 (|Seq#Length| T@@49 s@@21))) (= (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10) (|Seq#Drop| T@@49 s@@21 n@@10)))
 :qid |testbpl.1410:18|
 :skolemid |264|
 :pattern ( (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10))
)))
(assert (forall ((a@@44 T@U) (b@@27 T@U) (o@@24 T@U) (T@@50 T@T) ) (! (= (U_2_bool (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@44 b@@27) o@@24))  (and (U_2_bool (MapType0Select T@@50 boolType a@@44 o@@24)) (U_2_bool (MapType0Select T@@50 boolType b@@27 o@@24))))
 :qid |testbpl.848:18|
 :skolemid |139|
 :pattern ( (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@44 b@@27) o@@24))
)))
(assert (forall ((a@@45 T@U) (b@@28 T@U) (o@@25 T@U) (T@@51 T@T) ) (! (= (U_2_bool (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@45 b@@28) o@@25))  (and (U_2_bool (MapType0Select T@@51 boolType a@@45 o@@25)) (U_2_bool (MapType0Select T@@51 boolType b@@28 o@@25))))
 :qid |testbpl.951:18|
 :skolemid |163|
 :pattern ( (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@45 b@@28) o@@25))
)))
(assert (forall ((o@@26 T@U) (p@@2 T@U) ) (!  (or (or (|ORD#Less| o@@26 p@@2) (= o@@26 p@@2)) (|ORD#Less| p@@2 o@@26))
 :qid |testbpl.496:15|
 :skolemid |88|
 :pattern ( (|ORD#Less| o@@26 p@@2) (|ORD#Less| p@@2 o@@26))
)))
(assert (forall ((a@@46 T@U) (b@@29 T@U) (o@@27 T@U) (T@@52 T@T) ) (! (= (U_2_bool (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@46 b@@29) o@@27))  (and (U_2_bool (MapType0Select T@@52 boolType a@@46 o@@27)) (not (U_2_bool (MapType0Select T@@52 boolType b@@29 o@@27)))))
 :qid |testbpl.875:18|
 :skolemid |145|
 :pattern ( (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@46 b@@29) o@@27))
)))
(assert (forall ((a@@47 T@U) (b@@30 T@U) (o@@28 T@U) (T@@53 T@T) ) (! (= (U_2_bool (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@47 b@@30) o@@28))  (and (U_2_bool (MapType0Select T@@53 boolType a@@47 o@@28)) (not (U_2_bool (MapType0Select T@@53 boolType b@@30 o@@28)))))
 :qid |testbpl.973:18|
 :skolemid |168|
 :pattern ( (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@47 b@@30) o@@28))
)))
(assert (forall ((v@@18 T@U) (t0@@25 T@U) (h@@11 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@25) h@@11) (forall ((bx@@12 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@18 bx@@12)) ($IsAllocBox BoxType bx@@12 t0@@25 h@@11))
 :qid |testbpl.353:19|
 :skolemid |66|
 :pattern ( (MapType0Select BoxType boolType v@@18 bx@@12))
)))
 :qid |testbpl.350:15|
 :skolemid |67|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@25) h@@11))
)))
(assert (forall ((v@@19 T@U) (t0@@26 T@U) (h@@12 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@26) h@@12) (forall ((bx@@13 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@19 bx@@13)) ($IsAllocBox BoxType bx@@13 t0@@26 h@@12))
 :qid |testbpl.358:19|
 :skolemid |68|
 :pattern ( (MapType0Select BoxType boolType v@@19 bx@@13))
)))
 :qid |testbpl.355:15|
 :skolemid |69|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@26) h@@12))
)))
(assert (forall ((o@@29 T@U) (T@@54 T@T) ) (! (= (U_2_int (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@29)) 0)
 :qid |testbpl.1038:18|
 :skolemid |186|
 :pattern ( (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@29))
)))
(assert (forall ((t0@@27 T@U) (heap@@4 T@U) (f@@17 T@U) ) (!  (=> (and ($IsGoodHeap heap@@4) ($Is HandleTypeType f@@17 (Tclass._System.___hFunc0 t0@@27))) (= (|Set#Equal| BoxType (Reads0 t0@@27 $OneHeap f@@17) (|Set#Empty| BoxType)) (|Set#Equal| BoxType (Reads0 t0@@27 heap@@4 f@@17) (|Set#Empty| BoxType))))
 :qid |testbpl.2459:15|
 :skolemid |432|
 :pattern ( (Reads0 t0@@27 $OneHeap f@@17) ($IsGoodHeap heap@@4))
 :pattern ( (Reads0 t0@@27 heap@@4 f@@17))
)))
(assert (forall ((m@@18 T@U) (item T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@18) item))  (and (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType m@@18) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType m@@18) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item)))))
 :qid |testbpl.1515:15|
 :skolemid |287|
 :pattern ( (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@18) item))
)))
(assert (forall ((m@@19 T@U) (item@@0 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@19) item@@0))  (and (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))))
 :qid |testbpl.1647:15|
 :skolemid |317|
 :pattern ( (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@19) item@@0))
)))
(assert (forall ((m@@20 T@U) (v@@20 T@U) (U@@15 T@T) (V@@15 T@T) ) (! (= (U_2_bool (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@20) v@@20)) (exists ((u@@5 T@U) ) (!  (and (U_2_bool (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@20) u@@5)) (= v@@20 (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@20) u@@5)))
 :qid |testbpl.1503:17|
 :skolemid |285|
 :pattern ( (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@20) u@@5))
 :pattern ( (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@20) u@@5))
)))
 :qid |testbpl.1500:20|
 :skolemid |286|
 :pattern ( (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@20) v@@20))
)))
(assert (forall ((m@@21 T@U) (v@@21 T@U) (U@@16 T@T) (V@@16 T@T) ) (! (= (U_2_bool (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@21) v@@21)) (exists ((u@@6 T@U) ) (!  (and (U_2_bool (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@21) u@@6)) (= v@@21 (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@21) u@@6)))
 :qid |testbpl.1641:17|
 :skolemid |315|
 :pattern ( (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@21) u@@6))
 :pattern ( (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@21) u@@6))
)))
 :qid |testbpl.1638:20|
 :skolemid |316|
 :pattern ( (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@21) v@@21))
)))
(assert (forall ((t0@@28 T@U) (t1@@13 T@U) (heap@@5 T@U) (h@@13 T@U) (r@@4 T@U) (rd@@1 T@U) (bx0@@9 T@U) (bx@@14 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (Reads1 t0@@28 t1@@13 heap@@5 (Handle1 h@@13 r@@4 rd@@1) bx0@@9) bx@@14)) (U_2_bool (MapType0Select BoxType boolType (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType (MapType0Type BoxType boolType) rd@@1 heap@@5 bx0@@9) bx@@14)))
 :qid |testbpl.2062:15|
 :skolemid |375|
 :pattern ( (MapType0Select BoxType boolType (Reads1 t0@@28 t1@@13 heap@@5 (Handle1 h@@13 r@@4 rd@@1) bx0@@9) bx@@14))
)))
(assert  (and (and (forall ((arg0@@9 T@T) (arg1@@2 T@T) ) (! (= (Ctor (MapType arg0@@9 arg1@@2)) 11)
 :qid |ctor:MapType|
)) (forall ((arg0@@10 T@T) (arg1@@3 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@10 arg1@@3)) arg0@@10)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@10 arg1@@3))
))) (forall ((arg0@@11 T@T) (arg1@@4 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@11 arg1@@4)) arg1@@4)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@11 arg1@@4))
))))
(assert (forall ((v@@22 T@U) (t0@@29 T@U) (t1@@14 T@U) (h@@14 T@U) ) (! (= ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@29 t1@@14) h@@14) (forall ((bx@@15 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@15)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@15) t1@@14 h@@14) ($IsAllocBox BoxType bx@@15 t0@@29 h@@14)))
 :qid |testbpl.375:19|
 :skolemid |74|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@15))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@15))
)))
 :qid |testbpl.372:15|
 :skolemid |75|
 :pattern ( ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@29 t1@@14) h@@14))
)))
(assert  (and (and (forall ((arg0@@12 T@T) (arg1@@5 T@T) ) (! (= (Ctor (IMapType arg0@@12 arg1@@5)) 12)
 :qid |ctor:IMapType|
)) (forall ((arg0@@13 T@T) (arg1@@6 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@13 arg1@@6)) arg0@@13)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@13 arg1@@6))
))) (forall ((arg0@@14 T@T) (arg1@@7 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@14 arg1@@7)) arg1@@7)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@14 arg1@@7))
))))
(assert (forall ((v@@23 T@U) (t0@@30 T@U) (t1@@15 T@U) (h@@15 T@U) ) (! (= ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@30 t1@@15) h@@15) (forall ((bx@@16 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@16)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@16) t1@@15 h@@15) ($IsAllocBox BoxType bx@@16 t0@@30 h@@15)))
 :qid |testbpl.383:19|
 :skolemid |76|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@16))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@16))
)))
 :qid |testbpl.380:15|
 :skolemid |77|
 :pattern ( ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@30 t1@@15) h@@15))
)))
(assert (forall ((o@@30 T@U) (p@@3 T@U) ) (!  (and (=> (= o@@30 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@30 p@@3) p@@3)) (=> (= p@@3 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@30 p@@3) o@@30)))
 :qid |testbpl.524:15|
 :skolemid |93|
 :pattern ( (|ORD#Plus| o@@30 p@@3))
)))
(assert (forall ((x@@17 Int) (y@@1 Int) ) (! (= (INTERNAL_div_boogie x@@17 y@@1) (div x@@17 y@@1))
 :qid |testbpl.1748:15|
 :skolemid |335|
 :pattern ( (INTERNAL_div_boogie x@@17 y@@1))
)))
(assert (forall ((x@@18 Int) (y@@2 Int) ) (! (= (Div x@@18 y@@2) (div x@@18 y@@2))
 :qid |testbpl.1795:15|
 :skolemid |342|
 :pattern ( (Div x@@18 y@@2))
)))
(assert (forall ((o@@31 T@U) (p@@4 T@U) ) (! (= (|ORD#LessThanLimit| o@@31 p@@4) (|ORD#Less| o@@31 p@@4))
 :qid |testbpl.506:15|
 :skolemid |90|
 :pattern ( (|ORD#LessThanLimit| o@@31 p@@4))
)))
(assert (forall (($ly@@2 T@U) (|q#0@@2| Int) ) (! (= (_module.__default.secretPredicate $ly@@2 |q#0@@2|) (_module.__default.secretPredicate $LZ |q#0@@2|))
 :qid |testbpl.2860:15|
 :skolemid |486|
 :pattern ( (_module.__default.secretPredicate (AsFuelBottom $ly@@2) |q#0@@2|))
)))
(assert (forall ((a@@48 T@U) (b@@31 T@U) (T@@55 T@T) ) (!  (=> (|Set#Equal| T@@55 a@@48 b@@31) (= a@@48 b@@31))
 :qid |testbpl.903:18|
 :skolemid |152|
 :pattern ( (|Set#Equal| T@@55 a@@48 b@@31))
)))
(assert (forall ((a@@49 T@U) (b@@32 T@U) (T@@56 T@T) ) (!  (=> (|ISet#Equal| T@@56 a@@49 b@@32) (= a@@49 b@@32))
 :qid |testbpl.993:18|
 :skolemid |174|
 :pattern ( (|ISet#Equal| T@@56 a@@49 b@@32))
)))
(assert (forall ((a@@50 T@U) (b@@33 T@U) (T@@57 T@T) ) (!  (=> (|MultiSet#Equal| T@@57 a@@50 b@@33) (= a@@50 b@@33))
 :qid |testbpl.1135:18|
 :skolemid |208|
 :pattern ( (|MultiSet#Equal| T@@57 a@@50 b@@33))
)))
(assert (forall ((a@@51 T@U) (b@@34 T@U) (T@@58 T@T) ) (!  (=> (|Seq#Equal| T@@58 a@@51 b@@34) (= a@@51 b@@34))
 :qid |testbpl.1328:18|
 :skolemid |247|
 :pattern ( (|Seq#Equal| T@@58 a@@51 b@@34))
)))
(assert (forall ((m@@22 T@U) (|m'@@0| T@U) (U@@17 T@T) (V@@17 T@T) ) (!  (=> (|Map#Equal| U@@17 V@@17 m@@22 |m'@@0|) (= m@@22 |m'@@0|))
 :qid |testbpl.1592:20|
 :skolemid |303|
 :pattern ( (|Map#Equal| U@@17 V@@17 m@@22 |m'@@0|))
)))
(assert (forall ((m@@23 T@U) (|m'@@1| T@U) (U@@18 T@T) (V@@18 T@T) ) (!  (=> (|IMap#Equal| U@@18 V@@18 m@@23 |m'@@1|) (= m@@23 |m'@@1|))
 :qid |testbpl.1696:20|
 :skolemid |327|
 :pattern ( (|IMap#Equal| U@@18 V@@18 m@@23 |m'@@1|))
)))
(assert (forall ((a@@52 T@U) (x@@19 T@U) (y@@3 T@U) (T@@59 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@59 boolType a@@52 y@@3)) (U_2_bool (MapType0Select T@@59 boolType (|Set#UnionOne| T@@59 a@@52 x@@19) y@@3)))
 :qid |testbpl.814:18|
 :skolemid |132|
 :pattern ( (|Set#UnionOne| T@@59 a@@52 x@@19) (MapType0Select T@@59 boolType a@@52 y@@3))
)))
(assert (forall ((a@@53 T@U) (b@@35 T@U) (y@@4 T@U) (T@@60 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@60 boolType a@@53 y@@4)) (U_2_bool (MapType0Select T@@60 boolType (|Set#Union| T@@60 a@@53 b@@35) y@@4)))
 :qid |testbpl.832:18|
 :skolemid |136|
 :pattern ( (|Set#Union| T@@60 a@@53 b@@35) (MapType0Select T@@60 boolType a@@53 y@@4))
)))
(assert (forall ((a@@54 T@U) (b@@36 T@U) (y@@5 T@U) (T@@61 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@61 boolType b@@36 y@@5)) (U_2_bool (MapType0Select T@@61 boolType (|Set#Union| T@@61 a@@54 b@@36) y@@5)))
 :qid |testbpl.836:18|
 :skolemid |137|
 :pattern ( (|Set#Union| T@@61 a@@54 b@@36) (MapType0Select T@@61 boolType b@@36 y@@5))
)))
(assert (forall ((a@@55 T@U) (x@@20 T@U) (y@@6 T@U) (T@@62 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@62 boolType a@@55 y@@6)) (U_2_bool (MapType0Select T@@62 boolType (|ISet#UnionOne| T@@62 a@@55 x@@20) y@@6)))
 :qid |testbpl.925:18|
 :skolemid |158|
 :pattern ( (|ISet#UnionOne| T@@62 a@@55 x@@20) (MapType0Select T@@62 boolType a@@55 y@@6))
)))
(assert (forall ((a@@56 T@U) (b@@37 T@U) (y@@7 T@U) (T@@63 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@63 boolType a@@56 y@@7)) (U_2_bool (MapType0Select T@@63 boolType (|ISet#Union| T@@63 a@@56 b@@37) y@@7)))
 :qid |testbpl.935:18|
 :skolemid |160|
 :pattern ( (|ISet#Union| T@@63 a@@56 b@@37) (MapType0Select T@@63 boolType a@@56 y@@7))
)))
(assert (forall ((a@@57 T@U) (b@@38 T@U) (y@@8 T@U) (T@@64 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@64 boolType b@@38 y@@8)) (U_2_bool (MapType0Select T@@64 boolType (|ISet#Union| T@@64 a@@57 b@@38) y@@8)))
 :qid |testbpl.939:18|
 :skolemid |161|
 :pattern ( (|ISet#Union| T@@64 a@@57 b@@38) (MapType0Select T@@64 boolType b@@38 y@@8))
)))
(assert (forall ((x@@21 Int) ) (! (= (q@Real x@@21) (to_real x@@21))
 :qid |testbpl.679:15|
 :skolemid |113|
 :pattern ( (q@Real x@@21))
)))
(assert (forall ((a@@58 T@U) (x@@22 T@U) (o@@32 T@U) (T@@65 T@T) ) (! (= (U_2_bool (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@58 x@@22) o@@32))  (or (= o@@32 x@@22) (U_2_bool (MapType0Select T@@65 boolType a@@58 o@@32))))
 :qid |testbpl.808:18|
 :skolemid |130|
 :pattern ( (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@58 x@@22) o@@32))
)))
(assert (forall ((a@@59 T@U) (x@@23 T@U) (o@@33 T@U) (T@@66 T@T) ) (! (= (U_2_bool (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@59 x@@23) o@@33))  (or (= o@@33 x@@23) (U_2_bool (MapType0Select T@@66 boolType a@@59 o@@33))))
 :qid |testbpl.919:18|
 :skolemid |156|
 :pattern ( (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@59 x@@23) o@@33))
)))
(assert (forall ((s@@22 T@U) (n@@11 Int) (T@@67 T@T) ) (!  (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| T@@67 s@@22))) (= (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)) n@@11))
 :qid |testbpl.1341:18|
 :skolemid |250|
 :pattern ( (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)))
)))
(assert (forall ((a@@60 T@U) (b@@39 T@U) (c T@U) ) (!  (=> (or (not (= a@@60 c)) (not true)) (=> (and ($HeapSucc a@@60 b@@39) ($HeapSucc b@@39 c)) ($HeapSucc a@@60 c)))
 :qid |testbpl.718:15|
 :skolemid |116|
 :pattern ( ($HeapSucc a@@60 b@@39) ($HeapSucc b@@39 c))
)))
(assert (forall ((a@@61 T@U) (b@@40 T@U) (y@@9 T@U) (T@@68 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@68 boolType b@@40 y@@9)) (not (U_2_bool (MapType0Select T@@68 boolType (|Set#Difference| T@@68 a@@61 b@@40) y@@9))))
 :qid |testbpl.879:18|
 :skolemid |146|
 :pattern ( (|Set#Difference| T@@68 a@@61 b@@40) (MapType0Select T@@68 boolType b@@40 y@@9))
)))
(assert (forall ((a@@62 T@U) (b@@41 T@U) (y@@10 T@U) (T@@69 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@69 boolType b@@41 y@@10)) (not (U_2_bool (MapType0Select T@@69 boolType (|ISet#Difference| T@@69 a@@62 b@@41) y@@10))))
 :qid |testbpl.977:18|
 :skolemid |169|
 :pattern ( (|ISet#Difference| T@@69 a@@62 b@@41) (MapType0Select T@@69 boolType b@@41 y@@10))
)))
(assert (forall ((f@@18 T@U) (t0@@31 T@U) (t1@@16 T@U) ) (! (= ($Is HandleTypeType f@@18 (Tclass._System.___hFunc1 t0@@31 t1@@16)) (forall ((h@@16 T@U) (bx0@@10 T@U) ) (!  (=> (and (and ($IsGoodHeap h@@16) ($IsBox BoxType bx0@@10 t0@@31)) (Requires1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10)) ($IsBox BoxType (Apply1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10) t1@@16))
 :qid |testbpl.2195:19|
 :skolemid |390|
 :pattern ( (Apply1 t0@@31 t1@@16 h@@16 f@@18 bx0@@10))
)))
 :qid |testbpl.2192:15|
 :skolemid |391|
 :pattern ( ($Is HandleTypeType f@@18 (Tclass._System.___hFunc1 t0@@31 t1@@16)))
)))
(assert (forall ((m@@24 T@U) (U@@19 T@T) (V@@19 T@T) ) (! (= (= m@@24 (|IMap#Empty| U@@19 V@@19)) (= (|IMap#Domain| U@@19 V@@19 m@@24) (|ISet#Empty| U@@19)))
 :qid |testbpl.1624:20|
 :skolemid |312|
 :pattern ( (|IMap#Domain| U@@19 V@@19 m@@24))
)))
(assert (forall ((m@@25 T@U) (U@@20 T@T) (V@@20 T@T) ) (! (= (= m@@25 (|IMap#Empty| U@@20 V@@20)) (= (|IMap#Values| U@@20 V@@20 m@@25) (|ISet#Empty| V@@20)))
 :qid |testbpl.1628:20|
 :skolemid |313|
 :pattern ( (|IMap#Values| U@@20 V@@20 m@@25))
)))
(assert (forall ((m@@26 T@U) (U@@21 T@T) (V@@21 T@T) ) (! (= (= m@@26 (|IMap#Empty| U@@21 V@@21)) (= (|IMap#Items| U@@21 V@@21 m@@26) (|ISet#Empty| BoxType)))
 :qid |testbpl.1632:20|
 :skolemid |314|
 :pattern ( (|IMap#Items| U@@21 V@@21 m@@26))
)))
(assert (forall ((m@@27 T@U) (U@@22 T@T) (V@@22 T@T) ) (!  (or (= m@@27 (|Map#Empty| U@@22 V@@22)) (exists ((k@@5 T@U) (v@@24 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|Map#Items| U@@22 V@@22 m@@27) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@5 v@@24))))
 :qid |testbpl.1484:17|
 :skolemid |280|
)))
 :qid |testbpl.1481:20|
 :skolemid |281|
 :pattern ( (|Map#Items| U@@22 V@@22 m@@27))
)))
(assert (forall ((m@@28 T@U) (U@@23 T@T) (V@@23 T@T) ) (!  (or (= m@@28 (|IMap#Empty| U@@23 V@@23)) (exists ((k@@6 T@U) (v@@25 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| U@@23 V@@23 m@@28) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@6 v@@25))))
 :qid |testbpl.1622:17|
 :skolemid |310|
)))
 :qid |testbpl.1619:20|
 :skolemid |311|
 :pattern ( (|IMap#Items| U@@23 V@@23 m@@28))
)))
(assert (forall ((cl T@U) (nm T@U) (T@@70 T@T) ) (!  (and (= (DeclType T@@70 (FieldOfDecl T@@70 cl nm)) cl) (= (DeclName T@@70 (FieldOfDecl T@@70 cl nm)) nm))
 :qid |testbpl.638:18|
 :skolemid |106|
 :pattern ( (FieldOfDecl T@@70 cl nm))
)))
(assert (forall ((bx@@17 T@U) ) (!  (=> ($IsBox BoxType bx@@17 TInt) (and (= ($Box intType ($Unbox intType bx@@17)) bx@@17) ($Is intType ($Unbox intType bx@@17) TInt)))
 :qid |testbpl.202:15|
 :skolemid |26|
 :pattern ( ($IsBox BoxType bx@@17 TInt))
)))
(assert (forall ((bx@@18 T@U) ) (!  (=> ($IsBox BoxType bx@@18 TReal) (and (= ($Box realType ($Unbox realType bx@@18)) bx@@18) ($Is realType ($Unbox realType bx@@18) TReal)))
 :qid |testbpl.206:15|
 :skolemid |27|
 :pattern ( ($IsBox BoxType bx@@18 TReal))
)))
(assert (forall ((bx@@19 T@U) ) (!  (=> ($IsBox BoxType bx@@19 TBool) (and (= ($Box boolType ($Unbox boolType bx@@19)) bx@@19) ($Is boolType ($Unbox boolType bx@@19) TBool)))
 :qid |testbpl.211:15|
 :skolemid |28|
 :pattern ( ($IsBox BoxType bx@@19 TBool))
)))
(assert (= (Ctor charType) 13))
(assert (forall ((bx@@20 T@U) ) (!  (=> ($IsBox BoxType bx@@20 TChar) (and (= ($Box charType ($Unbox charType bx@@20)) bx@@20) ($Is charType ($Unbox charType bx@@20) TChar)))
 :qid |testbpl.216:15|
 :skolemid |29|
 :pattern ( ($IsBox BoxType bx@@20 TChar))
)))
(assert (forall ((a@@63 T@U) (b@@42 T@U) (T@@71 T@T) ) (!  (and (= (+ (+ (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)) (|Set#Card| T@@71 (|Set#Difference| T@@71 b@@42 a@@63))) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@63 b@@42))) (|Set#Card| T@@71 (|Set#Union| T@@71 a@@63 b@@42))) (= (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)) (- (|Set#Card| T@@71 a@@63) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@63 b@@42)))))
 :qid |testbpl.883:18|
 :skolemid |147|
 :pattern ( (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@63 b@@42)))
)))
(assert (forall (($ly@@3 T@U) (|q#0@@3| Int) ) (! (= (_module.__default.secretPredicate ($LS $ly@@3) |q#0@@3|) (_module.__default.secretPredicate $ly@@3 |q#0@@3|))
 :qid |testbpl.2854:15|
 :skolemid |485|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@3) |q#0@@3|))
)))
(assert (forall ((v@@26 T@U) (t@@8 T@U) (T@@72 T@T) ) (! (= ($IsBox BoxType ($Box T@@72 v@@26) t@@8) ($Is T@@72 v@@26 t@@8))
 :qid |testbpl.258:18|
 :skolemid |37|
 :pattern ( ($IsBox BoxType ($Box T@@72 v@@26) t@@8))
)))
(assert (forall ((t0@@32 T@U) (t1@@17 T@U) (heap@@6 T@U) (h@@17 T@U) (r@@5 T@U) (rd@@2 T@U) (bx0@@11 T@U) ) (!  (=> (U_2_bool (MapType2Select (MapType0Type refType (MapType1Type BoxType)) BoxType boolType r@@5 heap@@6 bx0@@11)) (Requires1 t0@@32 t1@@17 heap@@6 (Handle1 h@@17 r@@5 rd@@2) bx0@@11))
 :qid |testbpl.2052:15|
 :skolemid |374|
 :pattern ( (Requires1 t0@@32 t1@@17 heap@@6 (Handle1 h@@17 r@@5 rd@@2) bx0@@11))
)))
(assert (forall ((s@@23 T@U) (a@@64 T@U) (T@@73 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64)) 0)  (not (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@64)))) (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64)) 1) (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@64))))
 :qid |testbpl.1148:18|
 :skolemid |211|
 :pattern ( (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@64))
)))
(assert (forall ((t@@9 T@U) (T@@74 T@T) ) (! (= (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0) t@@9)
 :qid |testbpl.1260:18|
 :skolemid |232|
 :pattern ( (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0))
)))
(assert (forall ((s@@24 T@U) (i@@11 Int) (v@@27 T@U) (n@@12 Int) (T@@75 T@T) ) (!  (=> (and (<= n@@12 i@@11) (< i@@11 (|Seq#Length| T@@75 s@@24))) (= (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12) (|Seq#Take| T@@75 s@@24 n@@12)))
 :qid |testbpl.1400:18|
 :skolemid |262|
 :pattern ( (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12))
)))
(assert (forall ((r@@6 T@U) (o@@34 T@U) (T@@76 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34)) 1) (= r@@6 o@@34)) (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34)) 0)  (or (not (= r@@6 o@@34)) (not true))))
 :qid |testbpl.1047:18|
 :skolemid |189|
 :pattern ( (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@6) o@@34))
)))
(assert (forall ((o@@35 T@U) ) (! (<= 0 (|ORD#Offset| o@@35))
 :qid |testbpl.464:15|
 :skolemid |84|
 :pattern ( (|ORD#Offset| o@@35))
)))
(assert (forall ((o@@36 T@U) ) (! (<= 0 (_System.array.Length o@@36))
 :qid |testbpl.670:15|
 :skolemid |111|
 :pattern ( (_System.array.Length o@@36))
)))
(assert (forall ((s@@25 T@U) (T@@77 T@T) ) (! (<= 0 (|Set#Card| T@@77 s@@25))
 :qid |testbpl.783:18|
 :skolemid |123|
 :pattern ( (|Set#Card| T@@77 s@@25))
)))
(assert (forall ((s@@26 T@U) (T@@78 T@T) ) (! (<= 0 (|MultiSet#Card| T@@78 s@@26))
 :qid |testbpl.1030:18|
 :skolemid |184|
 :pattern ( (|MultiSet#Card| T@@78 s@@26))
)))
(assert (forall ((s@@27 T@U) (T@@79 T@T) ) (! (<= 0 (|Seq#Length| T@@79 s@@27))
 :qid |testbpl.1198:18|
 :skolemid |221|
 :pattern ( (|Seq#Length| T@@79 s@@27))
)))
(assert (forall ((m@@29 T@U) (U@@24 T@T) (V@@24 T@T) ) (! (<= 0 (|Map#Card| U@@24 V@@24 m@@29))
 :qid |testbpl.1467:20|
 :skolemid |274|
 :pattern ( (|Map#Card| U@@24 V@@24 m@@29))
)))
(assert (forall ((ty@@0 T@U) ) (!  (=> ($AlwaysAllocated ty@@0) (forall ((h@@18 T@U) (v@@28 T@U) ) (!  (=> ($IsBox BoxType v@@28 ty@@0) ($IsAllocBox BoxType v@@28 ty@@0 h@@18))
 :qid |testbpl.393:18|
 :skolemid |78|
 :pattern ( ($IsAllocBox BoxType v@@28 ty@@0 h@@18))
)))
 :qid |testbpl.390:15|
 :skolemid |79|
 :pattern ( ($AlwaysAllocated ty@@0))
)))
(assert (forall ((s@@28 T@U) (i@@12 Int) (j@@2 Int) (T@@80 T@T) ) (!  (=> (and (and (<= 0 i@@12) (< i@@12 j@@2)) (<= j@@2 (|Seq#Length| T@@80 s@@28))) (< (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))) (|Seq#Rank| T@@80 s@@28)))
 :qid |testbpl.1441:18|
 :skolemid |270|
 :pattern ( (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))))
)))
(assert (forall ((a@@65 T@U) (b@@43 T@U) (o@@37 T@U) (T@@81 T@T) ) (! (= (U_2_int (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@65 b@@43) o@@37)) (|Math#min| (U_2_int (MapType0Select T@@81 intType a@@65 o@@37)) (U_2_int (MapType0Select T@@81 intType b@@43 o@@37))))
 :qid |testbpl.1090:18|
 :skolemid |198|
 :pattern ( (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@65 b@@43) o@@37))
)))
(assert (forall ((t@@10 T@U) (u@@7 T@U) ) (! (= (Inv0_TMap (TMap t@@10 u@@7)) t@@10)
 :qid |testbpl.68:15|
 :skolemid |9|
 :pattern ( (TMap t@@10 u@@7))
)))
(assert (forall ((t@@11 T@U) (u@@8 T@U) ) (! (= (Inv1_TMap (TMap t@@11 u@@8)) u@@8)
 :qid |testbpl.70:15|
 :skolemid |10|
 :pattern ( (TMap t@@11 u@@8))
)))
(assert (forall ((t@@12 T@U) (u@@9 T@U) ) (! (= (Tag (TMap t@@12 u@@9)) TagMap)
 :qid |testbpl.72:15|
 :skolemid |11|
 :pattern ( (TMap t@@12 u@@9))
)))
(assert (forall ((t@@13 T@U) (u@@10 T@U) ) (! (= (Inv0_TIMap (TIMap t@@13 u@@10)) t@@13)
 :qid |testbpl.76:15|
 :skolemid |12|
 :pattern ( (TIMap t@@13 u@@10))
)))
(assert (forall ((t@@14 T@U) (u@@11 T@U) ) (! (= (Inv1_TIMap (TIMap t@@14 u@@11)) u@@11)
 :qid |testbpl.78:15|
 :skolemid |13|
 :pattern ( (TIMap t@@14 u@@11))
)))
(assert (forall ((t@@15 T@U) (u@@12 T@U) ) (! (= (Tag (TIMap t@@15 u@@12)) TagIMap)
 :qid |testbpl.80:15|
 :skolemid |14|
 :pattern ( (TIMap t@@15 u@@12))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$R@@6| T@U) ) (! (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@6|)) |#$T0@@1|)
 :qid |testbpl.2018:15|
 :skolemid |370|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@6|))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$R@@7| T@U) ) (! (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@7|)) |#$R@@7|)
 :qid |testbpl.2025:15|
 :skolemid |371|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@7|))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$R@@8| T@U) ) (! (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@8|)) |#$T0@@3|)
 :qid |testbpl.2245:15|
 :skolemid |401|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@8|))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$R@@9| T@U) ) (! (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@9|)) |#$R@@9|)
 :qid |testbpl.2253:15|
 :skolemid |402|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@9|))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$R@@10| T@U) ) (! (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@5| |#$R@@10|)) |#$T0@@5|)
 :qid |testbpl.2293:15|
 :skolemid |408|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@5| |#$R@@10|))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$R@@11| T@U) ) (! (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@6| |#$R@@11|)) |#$R@@11|)
 :qid |testbpl.2301:15|
 :skolemid |409|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@6| |#$R@@11|))
)))
(assert (forall ((|a#0#0#0| T@U) (|a#0#1#0| T@U) ) (! (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|)) |##_System._tuple#2._#Make2|)
 :qid |testbpl.2580:15|
 :skolemid |451|
 :pattern ( (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|))
)))
(assert (forall ((|_System._tuple#2$T0@@4| T@U) (|_System._tuple#2$T1@@4| T@U) ) (! (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|)) |_System._tuple#2$T0@@4|)
 :qid |testbpl.2614:15|
 :skolemid |456|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|))
)))
(assert (forall ((|_System._tuple#2$T0@@5| T@U) (|_System._tuple#2$T1@@5| T@U) ) (! (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|)) |_System._tuple#2$T1@@5|)
 :qid |testbpl.2622:15|
 :skolemid |457|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|))
)))
(assert (forall ((|a#4#0#0| T@U) (|a#4#1#0| T@U) ) (! (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|)) |a#4#0#0|)
 :qid |testbpl.2688:15|
 :skolemid |466|
 :pattern ( (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|))
)))
(assert (forall ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (! (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|)) |a#6#1#0|)
 :qid |testbpl.2698:15|
 :skolemid |468|
 :pattern ( (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))
)))
(assert (forall (($o@@3 T@U) ) (! ($Is refType $o@@3 Tclass._System.object?)
 :qid |testbpl.1849:15|
 :skolemid |350|
 :pattern ( ($Is refType $o@@3 Tclass._System.object?))
)))
(assert (forall ((v@@29 T@U) (t0@@33 T@U) (h@@19 T@U) ) (! (= ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@33) h@@19) (forall ((i@@13 Int) ) (!  (=> (and (<= 0 i@@13) (< i@@13 (|Seq#Length| BoxType v@@29))) ($IsAllocBox BoxType (|Seq#Index| BoxType v@@29 i@@13) t0@@33 h@@19))
 :qid |testbpl.368:19|
 :skolemid |72|
 :pattern ( (|Seq#Index| BoxType v@@29 i@@13))
)))
 :qid |testbpl.365:15|
 :skolemid |73|
 :pattern ( ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@33) h@@19))
)))
(assert (forall ((a@@66 T@U) (x@@24 T@U) (T@@82 T@T) ) (! (U_2_bool (MapType0Select T@@82 boolType (|Set#UnionOne| T@@82 a@@66 x@@24) x@@24))
 :qid |testbpl.812:18|
 :skolemid |131|
 :pattern ( (|Set#UnionOne| T@@82 a@@66 x@@24))
)))
(assert (forall ((a@@67 T@U) (x@@25 T@U) (T@@83 T@T) ) (! (U_2_bool (MapType0Select T@@83 boolType (|ISet#UnionOne| T@@83 a@@67 x@@25) x@@25))
 :qid |testbpl.923:18|
 :skolemid |157|
 :pattern ( (|ISet#UnionOne| T@@83 a@@67 x@@25))
)))
(assert  (and (forall ((t0@@34 T@T) (t1@@18 T@T) (t2@@0 T@T) (val@@7 T@U) (m@@30 T@U) (x0@@7 T@U) (x1@@2 T@U) ) (! (= (MapType3Select t0@@34 t1@@18 t2@@0 (MapType3Store t0@@34 t1@@18 t2@@0 m@@30 x0@@7 x1@@2 val@@7) x0@@7 x1@@2) val@@7)
 :qid |mapAx0:MapType3Select|
 :weight 0
)) (and (and (forall ((u0@@5 T@T) (u1@@3 T@T) (s0@@4 T@T) (t0@@35 T@T) (val@@8 T@U) (m@@31 T@U) (x0@@8 T@U) (x1@@3 T@U) (y0@@4 T@U) (y1@@1 T@U) ) (!  (or (= s0@@4 t0@@35) (= (MapType3Select t0@@35 u0@@5 u1@@3 (MapType3Store s0@@4 u0@@5 u1@@3 m@@31 x0@@8 x1@@3 val@@8) y0@@4 y1@@1) (MapType3Select t0@@35 u0@@5 u1@@3 m@@31 y0@@4 y1@@1)))
 :qid |mapAx1:MapType3Select:0|
 :weight 0
)) (forall ((u0@@6 T@T) (u1@@4 T@T) (s0@@5 T@T) (t0@@36 T@T) (val@@9 T@U) (m@@32 T@U) (x0@@9 T@U) (x1@@4 T@U) (y0@@5 T@U) (y1@@2 T@U) ) (!  (or (= x0@@9 y0@@5) (= (MapType3Select t0@@36 u0@@6 u1@@4 (MapType3Store s0@@5 u0@@6 u1@@4 m@@32 x0@@9 x1@@4 val@@9) y0@@5 y1@@2) (MapType3Select t0@@36 u0@@6 u1@@4 m@@32 y0@@5 y1@@2)))
 :qid |mapAx1:MapType3Select:1|
 :weight 0
))) (forall ((u0@@7 T@T) (u1@@5 T@T) (s0@@6 T@T) (t0@@37 T@T) (val@@10 T@U) (m@@33 T@U) (x0@@10 T@U) (x1@@5 T@U) (y0@@6 T@U) (y1@@3 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType3Select t0@@37 u0@@7 u1@@5 (MapType3Store s0@@6 u0@@7 u1@@5 m@@33 x0@@10 x1@@5 val@@10) y0@@6 y1@@3) (MapType3Select t0@@37 u0@@7 u1@@5 m@@33 y0@@6 y1@@3)))
 :qid |mapAx1:MapType3Select:2|
 :weight 0
)))))
(assert (forall ((|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ($o@@4 T@U) ($f T@U) (alpha@@0 T@T) ) (! (= (U_2_bool (MapType3Select alpha@@0 refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@4 $f))  (=> (and (or (not (= $o@@4 |l#0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) |l#1| $o@@4) |l#2|)))) |l#3|))
 :qid |testbpl.186:1|
 :skolemid |488|
 :pattern ( (MapType3Select alpha@@0 refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@4 $f))
)))
(assert (forall ((|l#0@@0| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ($o@@5 T@U) ($f@@0 T@U) (alpha@@1 T@T) ) (! (= (U_2_bool (MapType3Select alpha@@1 refType boolType (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@5 $f@@0))  (=> (and (or (not (= $o@@5 |l#0@@0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) |l#1@@0| $o@@5) |l#2@@0|)))) |l#3@@0|))
 :qid |testbpl.186:1|
 :skolemid |489|
 :pattern ( (MapType3Select alpha@@1 refType boolType (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@5 $f@@0))
)))
(assert (forall ((a@@68 T@U) (x@@26 T@U) (T@@84 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@84 boolType a@@68 x@@26)) (= (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@68 x@@26)) (|Set#Card| T@@84 a@@68)))
 :qid |testbpl.818:18|
 :skolemid |133|
 :pattern ( (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@68 x@@26)))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |testbpl.40:15|
 :skolemid |0|
 :pattern ( (TBitvector w))
)))
(assert (forall ((t@@16 T@U) ) (! (= (Inv0_TSet (TSet t@@16)) t@@16)
 :qid |testbpl.44:15|
 :skolemid |1|
 :pattern ( (TSet t@@16))
)))
(assert (forall ((t@@17 T@U) ) (! (= (Tag (TSet t@@17)) TagSet)
 :qid |testbpl.46:15|
 :skolemid |2|
 :pattern ( (TSet t@@17))
)))
(assert (forall ((t@@18 T@U) ) (! (= (Inv0_TISet (TISet t@@18)) t@@18)
 :qid |testbpl.50:15|
 :skolemid |3|
 :pattern ( (TISet t@@18))
)))
(assert (forall ((t@@19 T@U) ) (! (= (Tag (TISet t@@19)) TagISet)
 :qid |testbpl.52:15|
 :skolemid |4|
 :pattern ( (TISet t@@19))
)))
(assert (forall ((t@@20 T@U) ) (! (= (Inv0_TMultiSet (TMultiSet t@@20)) t@@20)
 :qid |testbpl.56:15|
 :skolemid |5|
 :pattern ( (TMultiSet t@@20))
)))
(assert (forall ((t@@21 T@U) ) (! (= (Tag (TMultiSet t@@21)) TagMultiSet)
 :qid |testbpl.58:15|
 :skolemid |6|
 :pattern ( (TMultiSet t@@21))
)))
(assert (forall ((t@@22 T@U) ) (! (= (Inv0_TSeq (TSeq t@@22)) t@@22)
 :qid |testbpl.62:15|
 :skolemid |7|
 :pattern ( (TSeq t@@22))
)))
(assert (forall ((t@@23 T@U) ) (! (= (Tag (TSeq t@@23)) TagSeq)
 :qid |testbpl.64:15|
 :skolemid |8|
 :pattern ( (TSeq t@@23))
)))
(assert (forall ((i@@14 Int) ) (! (= (FDim BoxType (IndexField i@@14)) 1)
 :qid |testbpl.606:15|
 :skolemid |102|
 :pattern ( (IndexField i@@14))
)))
(assert (forall ((i@@15 Int) ) (! (= (IndexField_Inverse BoxType (IndexField i@@15)) i@@15)
 :qid |testbpl.610:15|
 :skolemid |103|
 :pattern ( (IndexField i@@15))
)))
(assert (forall ((i@@16 Int) ) (! (= (q@Int (q@Real i@@16)) i@@16)
 :qid |testbpl.682:15|
 :skolemid |114|
 :pattern ( (q@Int (q@Real i@@16)))
)))
(assert (forall ((_System.array$arg@@6 T@U) ) (! (= (Tclass._System.array?_0 (Tclass._System.array? _System.array$arg@@6)) _System.array$arg@@6)
 :qid |testbpl.1903:15|
 :skolemid |356|
 :pattern ( (Tclass._System.array? _System.array$arg@@6))
)))
(assert (forall ((_System.array$arg@@7 T@U) ) (! (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@7)) _System.array$arg@@7)
 :qid |testbpl.1981:15|
 :skolemid |365|
 :pattern ( (Tclass._System.array _System.array$arg@@7))
)))
(assert (forall ((|#$R@@12| T@U) ) (! (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@12|)) |#$R@@12|)
 :qid |testbpl.2339:15|
 :skolemid |415|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@12|))
)))
(assert (forall ((|#$R@@13| T@U) ) (! (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@13|)) |#$R@@13|)
 :qid |testbpl.2517:15|
 :skolemid |442|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@13|))
)))
(assert (forall ((|#$R@@14| T@U) ) (! (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@14|)) |#$R@@14|)
 :qid |testbpl.2554:15|
 :skolemid |447|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@14|))
)))
(assert (forall ((x@@27 T@U) (T@@85 T@T) ) (! (= ($Unbox T@@85 ($Box T@@85 x@@27)) x@@27)
 :qid |testbpl.196:18|
 :skolemid |25|
 :pattern ( ($Box T@@85 x@@27))
)))
(assert (forall ((r@@7 T@U) (T@@86 T@T) ) (! (= (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@7)) 1)
 :qid |testbpl.802:18|
 :skolemid |129|
 :pattern ( (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@7)))
)))
(assert (forall ((t@@24 T@U) (T@@87 T@T) ) (! (= (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)) 1)
 :qid |testbpl.1211:18|
 :skolemid |224|
 :pattern ( (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)))
)))
(assert (forall ((v@@30 T@U) (t0@@38 T@U) (t1@@19 T@U) ) (! (= ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@38 t1@@19)) (forall ((bx@@21 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@21)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@21) t1@@19) ($IsBox BoxType bx@@21 t0@@38)))
 :qid |testbpl.307:19|
 :skolemid |54|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@21))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@21))
)))
 :qid |testbpl.304:15|
 :skolemid |55|
 :pattern ( ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@38 t1@@19)))
)))
(assert (forall ((v@@31 T@U) (t0@@39 T@U) (t1@@20 T@U) ) (! (= ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@39 t1@@20)) (forall ((bx@@22 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@22)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@22) t1@@20) ($IsBox BoxType bx@@22 t0@@39)))
 :qid |testbpl.321:19|
 :skolemid |57|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@22))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@22))
)))
 :qid |testbpl.318:15|
 :skolemid |58|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@39 t1@@20)))
)))
(assert (forall ((o@@38 T@U) (p@@5 T@U) ) (!  (and (and (and (=> (|ORD#Less| o@@38 p@@5) (or (not (= o@@38 p@@5)) (not true))) (=> (and (|ORD#IsNat| o@@38) (not (|ORD#IsNat| p@@5))) (|ORD#Less| o@@38 p@@5))) (=> (and (|ORD#IsNat| o@@38) (|ORD#IsNat| p@@5)) (= (|ORD#Less| o@@38 p@@5) (< (|ORD#Offset| o@@38) (|ORD#Offset| p@@5))))) (=> (and (|ORD#Less| o@@38 p@@5) (|ORD#IsNat| p@@5)) (|ORD#IsNat| o@@38)))
 :qid |testbpl.488:15|
 :skolemid |87|
 :pattern ( (|ORD#Less| o@@38 p@@5))
)))
(assert (forall ((h@@20 T@U) (i@@17 Int) (v@@32 T@U) (a@@69 T@U) ) (!  (=> (and (<= 0 i@@17) (< i@@17 (_System.array.Length a@@69))) (= (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@20 a@@69 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@20 a@@69) (IndexField i@@17) ($Box BoxType v@@32))) a@@69) (|Seq#Update| BoxType (|Seq#FromArray| h@@20 a@@69) i@@17 v@@32)))
 :qid |testbpl.1389:15|
 :skolemid |260|
 :pattern ( (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@20 a@@69 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@20 a@@69) (IndexField i@@17) ($Box BoxType v@@32))) a@@69))
)))
(assert (forall ((r@@8 T@U) (T@@88 T@T) ) (! (U_2_bool (MapType0Select T@@88 boolType (|Set#Singleton| T@@88 r@@8) r@@8))
 :qid |testbpl.796:18|
 :skolemid |127|
 :pattern ( (|Set#Singleton| T@@88 r@@8))
)))
(assert (forall ((x@@28 Int) (y@@11 Int) ) (! (= (INTERNAL_lt_boogie x@@28 y@@11) (< x@@28 y@@11))
 :qid |testbpl.1762:15|
 :skolemid |337|
 :pattern ( (INTERNAL_lt_boogie x@@28 y@@11))
)))
(assert (forall ((x@@29 Int) (y@@12 Int) ) (! (= (INTERNAL_gt_boogie x@@29 y@@12) (> x@@29 y@@12))
 :qid |testbpl.1776:15|
 :skolemid |339|
 :pattern ( (INTERNAL_gt_boogie x@@29 y@@12))
)))
(assert (forall ((m@@34 T@U) (n@@13 T@U) (u@@13 T@U) (U@@25 T@T) (V@@25 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13)) (and (=> (not (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13))) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 m@@34) u@@13))) (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13)) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 n@@13) u@@13)))))
 :qid |testbpl.1567:20|
 :skolemid |297|
 :pattern ( (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@34 n@@13)) u@@13))
)))
(assert (forall ((m@@35 T@U) (n@@14 T@U) (u@@14 T@U) (U@@26 T@T) (V@@26 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14)) (and (=> (not (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14))) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 m@@35) u@@14))) (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14)) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 n@@14) u@@14)))))
 :qid |testbpl.1706:20|
 :skolemid |329|
 :pattern ( (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@35 n@@14)) u@@14))
)))
(assert (forall ((s@@29 T@U) (i@@18 Int) (v@@33 T@U) (x@@30 T@U) (T@@89 T@T) ) (!  (=> (and (<= 0 i@@18) (< i@@18 (|Seq#Length| T@@89 s@@29))) (= (U_2_int (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30)) (U_2_int (MapType0Select T@@89 intType (|MultiSet#Union| T@@89 (|MultiSet#Difference| T@@89 (|MultiSet#FromSeq| T@@89 s@@29) (|MultiSet#Singleton| T@@89 (|Seq#Index| T@@89 s@@29 i@@18))) (|MultiSet#Singleton| T@@89 v@@33)) x@@30))))
 :qid |testbpl.1180:18|
 :skolemid |218|
 :pattern ( (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30))
)))
(assert (forall ((_System.array$arg@@8 T@U) ($h@@11 T@U) ($o@@6 T@U) ($i0 Int) ) (!  (=> (and (and (and (and (and ($IsGoodHeap $h@@11) (or (not (= $o@@6 null)) (not true))) (= (dtype $o@@6) (Tclass._System.array? _System.array$arg@@8))) (<= 0 $i0)) (< $i0 (_System.array.Length $o@@6))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) alloc)))) ($IsAllocBox BoxType ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) (IndexField $i0))) _System.array$arg@@8 $h@@11))
 :qid |testbpl.1928:15|
 :skolemid |359|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@11 $o@@6) (IndexField $i0))) (Tclass._System.array? _System.array$arg@@8))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (! (< (BoxRank |a#5#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)))
 :qid |testbpl.2693:15|
 :skolemid |467|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (! (< (BoxRank |a#7#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|)))
 :qid |testbpl.2703:15|
 :skolemid |469|
 :pattern ( (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|))
)))
(assert (forall ((a@@70 T@U) (b@@44 T@U) (T@@90 T@T) ) (! (= (|Set#Union| T@@90 a@@70 (|Set#Union| T@@90 a@@70 b@@44)) (|Set#Union| T@@90 a@@70 b@@44))
 :qid |testbpl.856:18|
 :skolemid |141|
 :pattern ( (|Set#Union| T@@90 a@@70 (|Set#Union| T@@90 a@@70 b@@44)))
)))
(assert (forall ((a@@71 T@U) (b@@45 T@U) (T@@91 T@T) ) (! (= (|Set#Intersection| T@@91 a@@71 (|Set#Intersection| T@@91 a@@71 b@@45)) (|Set#Intersection| T@@91 a@@71 b@@45))
 :qid |testbpl.864:18|
 :skolemid |143|
 :pattern ( (|Set#Intersection| T@@91 a@@71 (|Set#Intersection| T@@91 a@@71 b@@45)))
)))
(assert (forall ((a@@72 T@U) (b@@46 T@U) (T@@92 T@T) ) (! (= (|ISet#Union| T@@92 a@@72 (|ISet#Union| T@@92 a@@72 b@@46)) (|ISet#Union| T@@92 a@@72 b@@46))
 :qid |testbpl.959:18|
 :skolemid |165|
 :pattern ( (|ISet#Union| T@@92 a@@72 (|ISet#Union| T@@92 a@@72 b@@46)))
)))
(assert (forall ((a@@73 T@U) (b@@47 T@U) (T@@93 T@T) ) (! (= (|ISet#Intersection| T@@93 a@@73 (|ISet#Intersection| T@@93 a@@73 b@@47)) (|ISet#Intersection| T@@93 a@@73 b@@47))
 :qid |testbpl.967:18|
 :skolemid |167|
 :pattern ( (|ISet#Intersection| T@@93 a@@73 (|ISet#Intersection| T@@93 a@@73 b@@47)))
)))
(assert (forall ((a@@74 T@U) (b@@48 T@U) (T@@94 T@T) ) (! (= (|MultiSet#Intersection| T@@94 a@@74 (|MultiSet#Intersection| T@@94 a@@74 b@@48)) (|MultiSet#Intersection| T@@94 a@@74 b@@48))
 :qid |testbpl.1099:18|
 :skolemid |200|
 :pattern ( (|MultiSet#Intersection| T@@94 a@@74 (|MultiSet#Intersection| T@@94 a@@74 b@@48)))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$R@@15| T@U) (|f#0@@3| T@U) ) (! (= ($Is HandleTypeType |f#0@@3| (Tclass._System.___hTotalFunc1 |#$T0@@7| |#$R@@15|))  (and ($Is HandleTypeType |f#0@@3| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@15|)) (forall ((|x0#0| T@U) ) (!  (=> ($IsBox BoxType |x0#0| |#$T0@@7|) (Requires1 |#$T0@@7| |#$R@@15| $OneHeap |f#0@@3| |x0#0|))
 :qid |testbpl.2317:19|
 :skolemid |411|
))))
 :qid |testbpl.2313:15|
 :skolemid |412|
 :pattern ( ($Is HandleTypeType |f#0@@3| (Tclass._System.___hTotalFunc1 |#$T0@@7| |#$R@@15|)))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$R@@16| T@U) (|f#0@@4| T@U) ) (! (= ($Is HandleTypeType |f#0@@4| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@16|))  (and ($Is HandleTypeType |f#0@@4| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@16|)) (forall ((|x0#0@@0| T@U) ) (!  (=> ($IsBox BoxType |x0#0@@0| |#$T0@@8|) (|Set#Equal| BoxType (Reads1 |#$T0@@8| |#$R@@16| $OneHeap |f#0@@4| |x0#0@@0|) (|Set#Empty| BoxType)))
 :qid |testbpl.2270:19|
 :skolemid |404|
))))
 :qid |testbpl.2266:15|
 :skolemid |405|
 :pattern ( ($Is HandleTypeType |f#0@@4| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@16|)))
)))
(assert (forall ((m@@36 T@U) (u@@15 T@U) (|u'| T@U) (v@@34 T@U) (U@@27 T@T) (V@@27 T@T) ) (!  (and (=> (= |u'| u@@15) (and (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|)) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|) v@@34))) (=> (or (not (= |u'| u@@15)) (not true)) (and (= (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|)) (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 m@@36) |u'|))) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|) (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 m@@36) |u'|)))))
 :qid |testbpl.1545:20|
 :skolemid |293|
 :pattern ( (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|))
 :pattern ( (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@36 u@@15 v@@34)) |u'|))
)))
(assert (forall ((m@@37 T@U) (u@@16 T@U) (|u'@@0| T@U) (v@@35 T@U) (U@@28 T@T) (V@@28 T@T) ) (!  (and (=> (= |u'@@0| u@@16) (and (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|)) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|) v@@35))) (=> (or (not (= |u'@@0| u@@16)) (not true)) (and (= (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|)) (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 m@@37) |u'@@0|))) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|) (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 m@@37) |u'@@0|)))))
 :qid |testbpl.1677:20|
 :skolemid |323|
 :pattern ( (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|))
 :pattern ( (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@37 u@@16 v@@35)) |u'@@0|))
)))
(assert (forall ((f@@19 T@U) (ly@@0 T@U) (A@@0 T@T) ) (! (= (AtLayer A@@0 f@@19 ($LS ly@@0)) (AtLayer A@@0 f@@19 ly@@0))
 :qid |testbpl.593:18|
 :skolemid |101|
 :pattern ( (AtLayer A@@0 f@@19 ($LS ly@@0)))
)))
(assert (forall ((n@@15 Int) ) (!  (=> (or (and (<= 0 n@@15) (< n@@15 55296)) (and (<= 57344 n@@15) (< n@@15 1114112))) (= (|char#ToInt| (|char#FromInt| n@@15)) n@@15))
 :qid |testbpl.162:15|
 :skolemid |21|
 :pattern ( (|char#FromInt| n@@15))
)))
(assert (forall ((bx@@23 T@U) (s@@30 T@U) (t@@25 T@U) ) (!  (=> ($IsBox BoxType bx@@23 (TMap s@@30 t@@25)) (and (= ($Box (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@23)) bx@@23) ($Is (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@23) (TMap s@@30 t@@25))))
 :qid |testbpl.247:15|
 :skolemid |35|
 :pattern ( ($IsBox BoxType bx@@23 (TMap s@@30 t@@25)))
)))
(assert (forall ((bx@@24 T@U) (s@@31 T@U) (t@@26 T@U) ) (!  (=> ($IsBox BoxType bx@@24 (TIMap s@@31 t@@26)) (and (= ($Box (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@24)) bx@@24) ($Is (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@24) (TIMap s@@31 t@@26))))
 :qid |testbpl.252:15|
 :skolemid |36|
 :pattern ( ($IsBox BoxType bx@@24 (TIMap s@@31 t@@26)))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$R@@17| T@U) (bx@@25 T@U) ) (!  (=> ($IsBox BoxType bx@@25 (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@25)) bx@@25) ($Is HandleTypeType ($Unbox HandleTypeType bx@@25) (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|))))
 :qid |testbpl.2030:15|
 :skolemid |372|
 :pattern ( ($IsBox BoxType bx@@25 (Tclass._System.___hFunc1 |#$T0@@9| |#$R@@17|)))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$R@@18| T@U) (bx@@26 T@U) ) (!  (=> ($IsBox BoxType bx@@26 (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@26)) bx@@26) ($Is HandleTypeType ($Unbox HandleTypeType bx@@26) (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|))))
 :qid |testbpl.2259:15|
 :skolemid |403|
 :pattern ( ($IsBox BoxType bx@@26 (Tclass._System.___hPartialFunc1 |#$T0@@10| |#$R@@18|)))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$R@@19| T@U) (bx@@27 T@U) ) (!  (=> ($IsBox BoxType bx@@27 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@27)) bx@@27) ($Is HandleTypeType ($Unbox HandleTypeType bx@@27) (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|))))
 :qid |testbpl.2306:15|
 :skolemid |410|
 :pattern ( ($IsBox BoxType bx@@27 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@19|)))
)))
(assert (forall ((|_System._tuple#2$T0@@6| T@U) (|_System._tuple#2$T1@@6| T@U) (bx@@28 T@U) ) (!  (=> ($IsBox BoxType bx@@28 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|)) (and (= ($Box DatatypeTypeType ($Unbox DatatypeTypeType bx@@28)) bx@@28) ($Is DatatypeTypeType ($Unbox DatatypeTypeType bx@@28) (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|))))
 :qid |testbpl.2628:15|
 :skolemid |458|
 :pattern ( ($IsBox BoxType bx@@28 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|)))
)))
(assert (forall ((a@@75 T@U) (b@@49 T@U) (T@@95 T@T) ) (! (= (|MultiSet#Disjoint| T@@95 a@@75 b@@49) (forall ((o@@39 T@U) ) (!  (or (= (U_2_int (MapType0Select T@@95 intType a@@75 o@@39)) 0) (= (U_2_int (MapType0Select T@@95 intType b@@49 o@@39)) 0))
 :qid |testbpl.1144:19|
 :skolemid |209|
 :pattern ( (MapType0Select T@@95 intType a@@75 o@@39))
 :pattern ( (MapType0Select T@@95 intType b@@49 o@@39))
)))
 :qid |testbpl.1141:18|
 :skolemid |210|
 :pattern ( (|MultiSet#Disjoint| T@@95 a@@75 b@@49))
)))
(assert (forall ((o@@40 T@U) (T@@96 T@T) ) (!  (not (U_2_bool (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@40)))
 :qid |testbpl.787:18|
 :skolemid |124|
 :pattern ( (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@40))
)))
(assert (forall ((o@@41 T@U) (T@@97 T@T) ) (!  (not (U_2_bool (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@41)))
 :qid |testbpl.915:18|
 :skolemid |155|
 :pattern ( (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@41))
)))
(assert (forall ((t0@@40 T@U) (t1@@21 T@U) (heap@@7 T@U) (f@@20 T@U) (bx0@@12 T@U) ) (!  (=> (and (and ($IsGoodHeap heap@@7) ($IsBox BoxType bx0@@12 t0@@40)) ($Is HandleTypeType f@@20 (Tclass._System.___hFunc1 t0@@40 t1@@21))) (= (|Set#Equal| BoxType (Reads1 t0@@40 t1@@21 $OneHeap f@@20 bx0@@12) (|Set#Empty| BoxType)) (|Set#Equal| BoxType (Reads1 t0@@40 t1@@21 heap@@7 f@@20 bx0@@12) (|Set#Empty| BoxType))))
 :qid |testbpl.2174:15|
 :skolemid |388|
 :pattern ( (Reads1 t0@@40 t1@@21 $OneHeap f@@20 bx0@@12) ($IsGoodHeap heap@@7))
 :pattern ( (Reads1 t0@@40 t1@@21 heap@@7 f@@20 bx0@@12))
)))
(assert (forall ((h0@@9 T@U) (h1@@9 T@U) (a@@76 T@U) ) (!  (=> (and (and (and ($IsGoodHeap h0@@9) ($IsGoodHeap h1@@9)) ($HeapSucc h0@@9 h1@@9)) (= (MapType0Select refType (MapType1Type BoxType) h0@@9 a@@76) (MapType0Select refType (MapType1Type BoxType) h1@@9 a@@76))) (= (|Seq#FromArray| h0@@9 a@@76) (|Seq#FromArray| h1@@9 a@@76)))
 :qid |testbpl.1384:15|
 :skolemid |259|
 :pattern ( (|Seq#FromArray| h1@@9 a@@76) ($HeapSucc h0@@9 h1@@9))
)))
(assert (forall ((s@@32 T@U) (i@@19 Int) (v@@36 T@U) (T@@98 T@T) ) (!  (=> (and (<= 0 i@@19) (< i@@19 (|Seq#Length| T@@98 s@@32))) (= (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)) (|Seq#Length| T@@98 s@@32)))
 :qid |testbpl.1272:18|
 :skolemid |234|
 :pattern ( (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)))
)))
(assert (forall ((x@@31 Int) (y@@13 Int) ) (! (= (INTERNAL_mod_boogie x@@31 y@@13) (mod x@@31 y@@13))
 :qid |testbpl.1755:15|
 :skolemid |336|
 :pattern ( (INTERNAL_mod_boogie x@@31 y@@13))
)))
(assert (forall ((x@@32 Int) (y@@14 Int) ) (! (= (Mod x@@32 y@@14) (mod x@@32 y@@14))
 :qid |testbpl.1800:15|
 :skolemid |343|
 :pattern ( (Mod x@@32 y@@14))
)))
(assert (forall ((f@@21 T@U) (t0@@41 T@U) (h@@21 T@U) ) (!  (=> ($IsGoodHeap h@@21) (= ($IsAlloc HandleTypeType f@@21 (Tclass._System.___hFunc0 t0@@41) h@@21)  (=> (Requires0 t0@@41 h@@21 f@@21) (forall ((r@@9 T@U) ) (!  (=> (and (or (not (= r@@9 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@41 h@@21 f@@21) ($Box refType r@@9)))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@21 r@@9) alloc))))
 :qid |testbpl.2493:22|
 :skolemid |438|
 :pattern ( (MapType0Select BoxType boolType (Reads0 t0@@41 h@@21 f@@21) ($Box refType r@@9)))
)))))
 :qid |testbpl.2488:15|
 :skolemid |439|
 :pattern ( ($IsAlloc HandleTypeType f@@21 (Tclass._System.___hFunc0 t0@@41) h@@21))
)))
(assert (forall ((a@@77 T@U) (b@@50 T@U) (t0@@42 T@U) (t1@@22 T@U) ) (!  (=> (forall ((bx@@29 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@77 bx@@29)) (and ($IsBox BoxType bx@@29 t0@@42) ($IsBox BoxType (MapType0Select BoxType BoxType b@@50 bx@@29) t1@@22)))
 :qid |testbpl.1540:11|
 :skolemid |291|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@77 b@@50 (TMap t0@@42 t1@@22)) (TMap t0@@42 t1@@22)))
 :qid |testbpl.1538:15|
 :skolemid |292|
 :pattern ( (|Map#Glue| BoxType BoxType a@@77 b@@50 (TMap t0@@42 t1@@22)))
)))
(assert (forall ((a@@78 T@U) (b@@51 T@U) (t0@@43 T@U) (t1@@23 T@U) ) (!  (=> (forall ((bx@@30 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@78 bx@@30)) (and ($IsBox BoxType bx@@30 t0@@43) ($IsBox BoxType (MapType0Select BoxType BoxType b@@51 bx@@30) t1@@23)))
 :qid |testbpl.1672:11|
 :skolemid |321|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@78 b@@51 (TIMap t0@@43 t1@@23)) (TIMap t0@@43 t1@@23)))
 :qid |testbpl.1670:15|
 :skolemid |322|
 :pattern ( (|IMap#Glue| BoxType BoxType a@@78 b@@51 (TIMap t0@@43 t1@@23)))
)))
(assert (forall ((|#$R@@20| T@U) (|f#0@@5| T@U) ) (! (= ($Is HandleTypeType |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@20|))  (and ($Is HandleTypeType |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@20|)) (Requires0 |#$R@@20| $OneHeap |f#0@@5|)))
 :qid |testbpl.2566:15|
 :skolemid |449|
 :pattern ( ($Is HandleTypeType |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@20|)))
)))
(assert (forall ((h@@22 T@U) (a@@79 T@U) ) (! (= (|Seq#Length| BoxType (|Seq#FromArray| h@@22 a@@79)) (_System.array.Length a@@79))
 :qid |testbpl.1373:15|
 :skolemid |256|
 :pattern ( (|Seq#Length| BoxType (|Seq#FromArray| h@@22 a@@79)))
)))
(assert (forall ((a@@80 T@U) (b@@52 T@U) ) (!  (and (= (TypeTupleCar (TypeTuple a@@80 b@@52)) a@@80) (= (TypeTupleCdr (TypeTuple a@@80 b@@52)) b@@52))
 :qid |testbpl.428:15|
 :skolemid |80|
 :pattern ( (TypeTuple a@@80 b@@52))
)))
(assert (forall ((f@@22 T@U) (i@@20 Int) ) (!  (and (= (MultiIndexField_Inverse0 BoxType (MultiIndexField f@@22 i@@20)) f@@22) (= (MultiIndexField_Inverse1 BoxType (MultiIndexField f@@22 i@@20)) i@@20))
 :qid |testbpl.622:15|
 :skolemid |105|
 :pattern ( (MultiIndexField f@@22 i@@20))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$R@@21| T@U) ) (!  (and (= (Tag (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|)) Tagclass._System.___hFunc1) (= (TagFamily (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|)) |tytagFamily$_#Func1|))
 :qid |testbpl.2010:15|
 :skolemid |369|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@12| |#$R@@21|))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$R@@22| T@U) ) (!  (and (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|)) Tagclass._System.___hPartialFunc1) (= (TagFamily (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|)) |tytagFamily$_#PartialFunc1|))
 :qid |testbpl.2235:15|
 :skolemid |400|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@22|))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$R@@23| T@U) ) (!  (and (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|)) Tagclass._System.___hTotalFunc1) (= (TagFamily (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|)) |tytagFamily$_#TotalFunc1|))
 :qid |testbpl.2285:15|
 :skolemid |407|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@23|))
)))
(assert (forall ((|_System._tuple#2$T0@@7| T@U) (|_System._tuple#2$T1@@7| T@U) ) (!  (and (= (Tag (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|)) Tagclass._System.Tuple2) (= (TagFamily (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|)) |tytagFamily$_tuple#2|))
 :qid |testbpl.2604:15|
 :skolemid |455|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|))
)))
(assert (forall ((s@@33 T@U) (val@@11 T@U) (T@@99 T@T) ) (!  (and (= (|Seq#Build_inv0| T@@99 (|Seq#Build| T@@99 s@@33 val@@11)) s@@33) (= (|Seq#Build_inv1| T@@99 (|Seq#Build| T@@99 s@@33 val@@11)) val@@11))
 :qid |testbpl.1221:18|
 :skolemid |225|
 :pattern ( (|Seq#Build| T@@99 s@@33 val@@11))
)))
(assert (forall ((m@@38 T@U) (|m'@@2| T@U) (U@@29 T@T) (V@@29 T@T) ) (! (= (|Map#Equal| U@@29 V@@29 m@@38 |m'@@2|)  (and (forall ((u@@17 T@U) ) (! (= (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@38) u@@17)) (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 |m'@@2|) u@@17)))
 :qid |testbpl.1589:19|
 :skolemid |300|
)) (forall ((u@@18 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@38) u@@18)) (= (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 m@@38) u@@18) (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 |m'@@2|) u@@18)))
 :qid |testbpl.1590:19|
 :skolemid |301|
))))
 :qid |testbpl.1586:20|
 :skolemid |302|
 :pattern ( (|Map#Equal| U@@29 V@@29 m@@38 |m'@@2|))
)))
(assert (forall ((m@@39 T@U) (|m'@@3| T@U) (U@@30 T@T) (V@@30 T@T) ) (! (= (|IMap#Equal| U@@30 V@@30 m@@39 |m'@@3|)  (and (forall ((u@@19 T@U) ) (! (= (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@39) u@@19)) (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 |m'@@3|) u@@19)))
 :qid |testbpl.1692:19|
 :skolemid |324|
)) (forall ((u@@20 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@39) u@@20)) (= (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 m@@39) u@@20) (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 |m'@@3|) u@@20)))
 :qid |testbpl.1693:19|
 :skolemid |325|
))))
 :qid |testbpl.1689:20|
 :skolemid |326|
 :pattern ( (|IMap#Equal| U@@30 V@@30 m@@39 |m'@@3|))
)))
(assert (forall ((o@@42 T@U) (m@@40 Int) (n@@16 Int) ) (!  (=> (and (<= 0 m@@40) (<= 0 n@@16)) (= (|ORD#Plus| (|ORD#Plus| o@@42 (|ORD#FromNat| m@@40)) (|ORD#FromNat| n@@16)) (|ORD#Plus| o@@42 (|ORD#FromNat| (+ m@@40 n@@16)))))
 :qid |testbpl.543:15|
 :skolemid |96|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@42 (|ORD#FromNat| m@@40)) (|ORD#FromNat| n@@16)))
)))
(assert (forall ((x@@33 Int) (y@@15 Int) ) (! (= (INTERNAL_le_boogie x@@33 y@@15) (<= x@@33 y@@15))
 :qid |testbpl.1769:15|
 :skolemid |338|
 :pattern ( (INTERNAL_le_boogie x@@33 y@@15))
)))
(assert (forall ((x@@34 Int) (y@@16 Int) ) (! (= (INTERNAL_ge_boogie x@@34 y@@16) (>= x@@34 y@@16))
 :qid |testbpl.1783:15|
 :skolemid |340|
 :pattern ( (INTERNAL_ge_boogie x@@34 y@@16))
)))
(assert (forall ((x@@35 Int) (y@@17 Int) ) (! (= (INTERNAL_sub_boogie x@@35 y@@17) (- x@@35 y@@17))
 :qid |testbpl.1734:15|
 :skolemid |333|
 :pattern ( (INTERNAL_sub_boogie x@@35 y@@17))
)))
(assert (forall ((x@@36 Int) (y@@18 Int) ) (! (= (Sub x@@36 y@@18) (- x@@36 y@@18))
 :qid |testbpl.1810:15|
 :skolemid |345|
 :pattern ( (Sub x@@36 y@@18))
)))
(assert (forall ((x@@37 Int) (y@@19 Int) ) (! (= (INTERNAL_add_boogie x@@37 y@@19) (+ x@@37 y@@19))
 :qid |testbpl.1727:15|
 :skolemid |332|
 :pattern ( (INTERNAL_add_boogie x@@37 y@@19))
)))
(assert (forall ((x@@38 Int) (y@@20 Int) ) (! (= (Add x@@38 y@@20) (+ x@@38 y@@20))
 :qid |testbpl.1805:15|
 :skolemid |344|
 :pattern ( (Add x@@38 y@@20))
)))
(assert (forall ((x@@39 Int) (y@@21 Int) ) (! (= (INTERNAL_mul_boogie x@@39 y@@21) (* x@@39 y@@21))
 :qid |testbpl.1741:15|
 :skolemid |334|
 :pattern ( (INTERNAL_mul_boogie x@@39 y@@21))
)))
(assert (forall ((x@@40 Int) (y@@22 Int) ) (! (= (Mul x@@40 y@@22) (* x@@40 y@@22))
 :qid |testbpl.1790:15|
 :skolemid |341|
 :pattern ( (Mul x@@40 y@@22))
)))
(assert (forall ((d@@9 T@U) ) (! (= (BoxRank ($Box DatatypeTypeType d@@9)) (DtRank d@@9))
 :qid |testbpl.456:15|
 :skolemid |83|
 :pattern ( (BoxRank ($Box DatatypeTypeType d@@9)))
)))
(assert (forall ((r@@10 T@U) (T@@100 T@T) ) (! (= (|MultiSet#Singleton| T@@100 r@@10) (|MultiSet#UnionOne| T@@100 (|MultiSet#Empty| T@@100) r@@10))
 :qid |testbpl.1052:18|
 :skolemid |190|
 :pattern ( (|MultiSet#Singleton| T@@100 r@@10))
)))
(assert (forall ((s@@34 T@U) (T@@101 T@T) ) (! (= (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)) (|Set#Card| T@@101 s@@34))
 :qid |testbpl.1153:18|
 :skolemid |212|
 :pattern ( (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)))
)))
(assert (forall ((s@@35 T@U) (T@@102 T@T) ) (! (= (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)) (|Seq#Length| T@@102 s@@35))
 :qid |testbpl.1167:18|
 :skolemid |215|
 :pattern ( (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)))
)))
(assert (forall ((m@@41 T@U) (U@@31 T@T) (V@@31 T@T) ) (! (= (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@41)) (|Map#Card| U@@31 V@@31 m@@41))
 :qid |testbpl.1486:20|
 :skolemid |282|
 :pattern ( (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@41)))
 :pattern ( (|Map#Card| U@@31 V@@31 m@@41))
)))
(assert (forall ((m@@42 T@U) (U@@32 T@T) (V@@32 T@T) ) (! (= (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@42)) (|Map#Card| U@@32 V@@32 m@@42))
 :qid |testbpl.1494:20|
 :skolemid |284|
 :pattern ( (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@42)))
 :pattern ( (|Map#Card| U@@32 V@@32 m@@42))
)))
(assert (forall ((m@@43 T@U) (U@@33 T@T) (V@@33 T@T) ) (! (<= (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@43)) (|Map#Card| U@@33 V@@33 m@@43))
 :qid |testbpl.1490:20|
 :skolemid |283|
 :pattern ( (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@43)))
 :pattern ( (|Map#Card| U@@33 V@@33 m@@43))
)))
(assert (forall ((s@@36 T@U) (n@@17 Int) (x@@41 T@U) (T@@103 T@T) ) (! (= (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41) (exists ((i@@21 Int) ) (!  (and (and (and (<= 0 n@@17) (<= n@@17 i@@21)) (< i@@21 (|Seq#Length| T@@103 s@@36))) (= (|Seq#Index| T@@103 s@@36 i@@21) x@@41))
 :qid |testbpl.1314:19|
 :skolemid |243|
 :pattern ( (|Seq#Index| T@@103 s@@36 i@@21))
)))
 :qid |testbpl.1311:18|
 :skolemid |244|
 :pattern ( (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41))
)))
(assert (forall ((a@@81 Int) (b@@53 Int) ) (! (= (<= a@@81 b@@53) (= (|Math#min| a@@81 b@@53) a@@81))
 :qid |testbpl.1005:15|
 :skolemid |177|
 :pattern ( (|Math#min| a@@81 b@@53))
)))
(assert (forall ((a@@82 Int) (b@@54 Int) ) (! (= (<= b@@54 a@@82) (= (|Math#min| a@@82 b@@54) b@@54))
 :qid |testbpl.1007:15|
 :skolemid |178|
 :pattern ( (|Math#min| a@@82 b@@54))
)))
(assert (forall ((f@@23 T@U) (t0@@44 T@U) ) (! (= ($Is HandleTypeType f@@23 (Tclass._System.___hFunc0 t0@@44)) (forall ((h@@23 T@U) ) (!  (=> (and ($IsGoodHeap h@@23) (Requires0 t0@@44 h@@23 f@@23)) ($IsBox BoxType (Apply0 t0@@44 h@@23 f@@23) t0@@44))
 :qid |testbpl.2476:19|
 :skolemid |434|
 :pattern ( (Apply0 t0@@44 h@@23 f@@23))
)))
 :qid |testbpl.2473:15|
 :skolemid |435|
 :pattern ( ($Is HandleTypeType f@@23 (Tclass._System.___hFunc0 t0@@44)))
)))
(assert (forall ((o@@43 T@U) (m@@44 Int) (n@@18 Int) ) (!  (=> (and (and (<= 0 m@@44) (<= 0 n@@18)) (<= n@@18 (+ (|ORD#Offset| o@@43) m@@44))) (and (=> (<= 0 (- m@@44 n@@18)) (= (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)) (|ORD#Plus| o@@43 (|ORD#FromNat| (- m@@44 n@@18))))) (=> (<= (- m@@44 n@@18) 0) (= (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)) (|ORD#Minus| o@@43 (|ORD#FromNat| (- n@@18 m@@44)))))))
 :qid |testbpl.555:15|
 :skolemid |98|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@43 (|ORD#FromNat| m@@44)) (|ORD#FromNat| n@@18)))
)))
(assert (forall ((o@@44 T@U) (m@@45 Int) (n@@19 Int) ) (!  (=> (and (and (<= 0 m@@45) (<= 0 n@@19)) (<= n@@19 (+ (|ORD#Offset| o@@44) m@@45))) (and (=> (<= 0 (- m@@45 n@@19)) (= (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)) (|ORD#Minus| o@@44 (|ORD#FromNat| (- m@@45 n@@19))))) (=> (<= (- m@@45 n@@19) 0) (= (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)) (|ORD#Plus| o@@44 (|ORD#FromNat| (- n@@19 m@@45)))))))
 :qid |testbpl.565:15|
 :skolemid |99|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@44 (|ORD#FromNat| m@@45)) (|ORD#FromNat| n@@19)))
)))
(assert (forall ((bx@@31 T@U) ) (!  (=> ($IsBox BoxType bx@@31 (TBitvector 0)) (and (= ($Box intType ($Unbox intType bx@@31)) bx@@31) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@31) (TBitvector 0))))
 :qid |testbpl.221:15|
 :skolemid |30|
 :pattern ( ($IsBox BoxType bx@@31 (TBitvector 0)))
)))
(assert (forall ((bx@@32 T@U) (t@@27 T@U) ) (!  (=> ($IsBox BoxType bx@@32 (TSet t@@27)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@32)) bx@@32) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@32) (TSet t@@27))))
 :qid |testbpl.226:15|
 :skolemid |31|
 :pattern ( ($IsBox BoxType bx@@32 (TSet t@@27)))
)))
(assert (forall ((bx@@33 T@U) (t@@28 T@U) ) (!  (=> ($IsBox BoxType bx@@33 (TISet t@@28)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@33)) bx@@33) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@33) (TISet t@@28))))
 :qid |testbpl.231:15|
 :skolemid |32|
 :pattern ( ($IsBox BoxType bx@@33 (TISet t@@28)))
)))
(assert (forall ((bx@@34 T@U) (t@@29 T@U) ) (!  (=> ($IsBox BoxType bx@@34 (TMultiSet t@@29)) (and (= ($Box (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@34)) bx@@34) ($Is (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@34) (TMultiSet t@@29))))
 :qid |testbpl.236:15|
 :skolemid |33|
 :pattern ( ($IsBox BoxType bx@@34 (TMultiSet t@@29)))
)))
(assert (forall ((bx@@35 T@U) (t@@30 T@U) ) (!  (=> ($IsBox BoxType bx@@35 (TSeq t@@30)) (and (= ($Box (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@35)) bx@@35) ($Is (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@35) (TSeq t@@30))))
 :qid |testbpl.242:15|
 :skolemid |34|
 :pattern ( ($IsBox BoxType bx@@35 (TSeq t@@30)))
)))
(assert (forall ((_System.array$arg@@9 T@U) (bx@@36 T@U) ) (!  (=> ($IsBox BoxType bx@@36 (Tclass._System.array? _System.array$arg@@9)) (and (= ($Box refType ($Unbox refType bx@@36)) bx@@36) ($Is refType ($Unbox refType bx@@36) (Tclass._System.array? _System.array$arg@@9))))
 :qid |testbpl.1909:15|
 :skolemid |357|
 :pattern ( ($IsBox BoxType bx@@36 (Tclass._System.array? _System.array$arg@@9)))
)))
(assert (forall ((_System.array$arg@@10 T@U) (bx@@37 T@U) ) (!  (=> ($IsBox BoxType bx@@37 (Tclass._System.array _System.array$arg@@10)) (and (= ($Box refType ($Unbox refType bx@@37)) bx@@37) ($Is refType ($Unbox refType bx@@37) (Tclass._System.array _System.array$arg@@10))))
 :qid |testbpl.1987:15|
 :skolemid |366|
 :pattern ( ($IsBox BoxType bx@@37 (Tclass._System.array _System.array$arg@@10)))
)))
(assert (forall ((|#$R@@24| T@U) (bx@@38 T@U) ) (!  (=> ($IsBox BoxType bx@@38 (Tclass._System.___hFunc0 |#$R@@24|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@38)) bx@@38) ($Is HandleTypeType ($Unbox HandleTypeType bx@@38) (Tclass._System.___hFunc0 |#$R@@24|))))
 :qid |testbpl.2344:15|
 :skolemid |416|
 :pattern ( ($IsBox BoxType bx@@38 (Tclass._System.___hFunc0 |#$R@@24|)))
)))
(assert (forall ((|#$R@@25| T@U) (bx@@39 T@U) ) (!  (=> ($IsBox BoxType bx@@39 (Tclass._System.___hPartialFunc0 |#$R@@25|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@39)) bx@@39) ($Is HandleTypeType ($Unbox HandleTypeType bx@@39) (Tclass._System.___hPartialFunc0 |#$R@@25|))))
 :qid |testbpl.2522:15|
 :skolemid |443|
 :pattern ( ($IsBox BoxType bx@@39 (Tclass._System.___hPartialFunc0 |#$R@@25|)))
)))
(assert (forall ((|#$R@@26| T@U) (bx@@40 T@U) ) (!  (=> ($IsBox BoxType bx@@40 (Tclass._System.___hTotalFunc0 |#$R@@26|)) (and (= ($Box HandleTypeType ($Unbox HandleTypeType bx@@40)) bx@@40) ($Is HandleTypeType ($Unbox HandleTypeType bx@@40) (Tclass._System.___hTotalFunc0 |#$R@@26|))))
 :qid |testbpl.2559:15|
 :skolemid |448|
 :pattern ( ($IsBox BoxType bx@@40 (Tclass._System.___hTotalFunc0 |#$R@@26|)))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (T@@104 T@T) ) (! (= (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)) (|MultiSet#UnionOne| T@@104 (|MultiSet#FromSeq| T@@104 s@@37) v@@37))
 :qid |testbpl.1171:18|
 :skolemid |216|
 :pattern ( (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)))
)))
(assert (forall ((m@@46 T@U) (s@@38 T@U) (U@@34 T@T) (V@@34 T@T) ) (! (= (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@46 s@@38)) (|Set#Difference| U@@34 (|Map#Domain| U@@34 V@@34 m@@46) s@@38))
 :qid |testbpl.1575:20|
 :skolemid |298|
 :pattern ( (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@46 s@@38)))
)))
(assert (forall ((m@@47 T@U) (s@@39 T@U) (U@@35 T@T) (V@@35 T@T) ) (! (= (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@47 s@@39)) (|Set#Difference| U@@35 (|IMap#Domain| U@@35 V@@35 m@@47) s@@39))
 :qid |testbpl.1716:20|
 :skolemid |330|
 :pattern ( (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@47 s@@39)))
)))
(assert (forall ((ch T@U) ) (!  (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (or (and (<= 0 (|char#ToInt| ch)) (< (|char#ToInt| ch) 55296)) (and (<= 57344 (|char#ToInt| ch)) (< (|char#ToInt| ch) 1114112))))
 :qid |testbpl.168:15|
 :skolemid |22|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((o@@45 T@U) ) (!  (=> (|ORD#IsNat| o@@45) (= o@@45 (|ORD#FromNat| (|ORD#Offset| o@@45))))
 :qid |testbpl.482:15|
 :skolemid |86|
 :pattern ( (|ORD#Offset| o@@45))
 :pattern ( (|ORD#IsNat| o@@45))
)))
(assert (forall ((s@@40 T@U) (T@@105 T@T) ) (!  (and (= (= (|Set#Card| T@@105 s@@40) 0) (= s@@40 (|Set#Empty| T@@105))) (=> (or (not (= (|Set#Card| T@@105 s@@40) 0)) (not true)) (exists ((x@@42 T@U) ) (! (U_2_bool (MapType0Select T@@105 boolType s@@40 x@@42))
 :qid |testbpl.792:39|
 :skolemid |125|
))))
 :qid |testbpl.789:18|
 :skolemid |126|
 :pattern ( (|Set#Card| T@@105 s@@40))
)))
(assert (forall ((h@@24 T@U) (r@@11 T@U) (f@@24 T@U) (x@@43 T@U) (alpha@@2 T@T) ) (!  (=> ($IsGoodHeap (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43)))) ($HeapSucc h@@24 (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43)))))
 :qid |testbpl.714:22|
 :skolemid |115|
 :pattern ( (MapType0Store refType (MapType1Type BoxType) h@@24 r@@11 (MapType1Store alpha@@2 BoxType (MapType0Select refType (MapType1Type BoxType) h@@24 r@@11) f@@24 ($Box alpha@@2 x@@43))))
)))
(assert (forall ((a@@83 T@U) (b@@55 T@U) (T@@106 T@T) ) (! (= (|Set#Subset| T@@106 a@@83 b@@55) (forall ((o@@46 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@106 boolType a@@83 o@@46)) (U_2_bool (MapType0Select T@@106 boolType b@@55 o@@46)))
 :qid |testbpl.895:33|
 :skolemid |148|
 :pattern ( (MapType0Select T@@106 boolType a@@83 o@@46))
 :pattern ( (MapType0Select T@@106 boolType b@@55 o@@46))
)))
 :qid |testbpl.893:18|
 :skolemid |149|
 :pattern ( (|Set#Subset| T@@106 a@@83 b@@55))
)))
(assert (forall ((a@@84 T@U) (b@@56 T@U) (T@@107 T@T) ) (! (= (|ISet#Subset| T@@107 a@@84 b@@56) (forall ((o@@47 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@107 boolType a@@84 o@@47)) (U_2_bool (MapType0Select T@@107 boolType b@@56 o@@47)))
 :qid |testbpl.985:34|
 :skolemid |170|
 :pattern ( (MapType0Select T@@107 boolType a@@84 o@@47))
 :pattern ( (MapType0Select T@@107 boolType b@@56 o@@47))
)))
 :qid |testbpl.983:18|
 :skolemid |171|
 :pattern ( (|ISet#Subset| T@@107 a@@84 b@@56))
)))
(assert (forall ((d@@10 T@U) ($h@@12 T@U) ) (!  (=> (and ($IsGoodHeap $h@@12) ($Is DatatypeTypeType d@@10 Tclass._System.Tuple0)) ($IsAlloc DatatypeTypeType d@@10 Tclass._System.Tuple0 $h@@12))
 :qid |testbpl.2786:15|
 :skolemid |477|
 :pattern ( ($IsAlloc DatatypeTypeType d@@10 Tclass._System.Tuple0 $h@@12))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (= (TagFamily Tclass._System.object?) tytagFamily$object))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (= (TagFamily Tclass._System.nat) tytagFamily$nat))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (= (TagFamily Tclass._System.object) tytagFamily$object))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (= (TagFamily Tclass._System.Tuple0) |tytagFamily$_tuple#0|))
(assert (forall ((_System.array$arg@@11 T@U) ($h@@13 T@U) ($o@@7 T@U) ($i0@@0 Int) ) (!  (=> (and (and (and (and ($IsGoodHeap $h@@13) (or (not (= $o@@7 null)) (not true))) (= (dtype $o@@7) (Tclass._System.array? _System.array$arg@@11))) (<= 0 $i0@@0)) (< $i0@@0 (_System.array.Length $o@@7))) ($IsBox BoxType ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@13 $o@@7) (IndexField $i0@@0))) _System.array$arg@@11))
 :qid |testbpl.1916:15|
 :skolemid |358|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@13 $o@@7) (IndexField $i0@@0))) (Tclass._System.array? _System.array$arg@@11))
)))
(assert (forall ((ty@@1 T@U) (heap@@8 T@U) (len@@0 Int) (init@@0 T@U) ) (!  (=> (and ($IsGoodHeap heap@@8) (<= 0 len@@0)) (= (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@8 len@@0 init@@0)) len@@0))
 :qid |testbpl.1241:15|
 :skolemid |229|
 :pattern ( (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@8 len@@0 init@@0)))
)))
(assert (forall ((s@@41 T@U) (n@@20 Int) (k@@7 Int) (T@@108 T@T) ) (!  (=> (and (and (<= 0 n@@20) (<= n@@20 k@@7)) (< k@@7 (|Seq#Length| T@@108 s@@41))) (= (|Seq#Index| T@@108 (|Seq#Drop| T@@108 s@@41 n@@20) (- k@@7 n@@20)) (|Seq#Index| T@@108 s@@41 k@@7)))
 :qid |testbpl.1361:18|
 :weight 25
 :skolemid |254|
 :pattern ( (|Seq#Index| T@@108 s@@41 k@@7) (|Seq#Drop| T@@108 s@@41 n@@20))
)))
(assert (forall ((v@@38 T@U) (t0@@45 T@U) (h@@25 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@45) h@@25) (forall ((bx@@41 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@38 bx@@41))) ($IsAllocBox BoxType bx@@41 t0@@45 h@@25))
 :qid |testbpl.363:19|
 :skolemid |70|
 :pattern ( (MapType0Select BoxType intType v@@38 bx@@41))
)))
 :qid |testbpl.360:15|
 :skolemid |71|
 :pattern ( ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@45) h@@25))
)))
(assert (forall ((t0@@46 T@U) (heap@@9 T@U) (h@@26 T@U) (r@@12 T@U) (rd@@3 T@U) (bx@@42 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@46 heap@@9 (Handle0 h@@26 r@@12 rd@@3)) bx@@42)) (U_2_bool (MapType0Select BoxType boolType (MapType0Select (MapType0Type refType (MapType1Type BoxType)) (MapType0Type BoxType boolType) rd@@3 heap@@9) bx@@42)))
 :qid |testbpl.2366:15|
 :skolemid |419|
 :pattern ( (MapType0Select BoxType boolType (Reads0 t0@@46 heap@@9 (Handle0 h@@26 r@@12 rd@@3)) bx@@42))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit DatatypeTypeType |#_System._tuple#0._#Make0|)))
(assert (forall ((o@@48 T@U) (p@@6 T@U) ) (!  (=> (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@48))) (or (and (= p@@6 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@48 p@@6) o@@48)) (and (or (not (= p@@6 (|ORD#FromNat| 0))) (not true)) (|ORD#Less| (|ORD#Minus| o@@48 p@@6) o@@48))))
 :qid |testbpl.537:15|
 :skolemid |95|
 :pattern ( (|ORD#Minus| o@@48 p@@6))
)))
(assert (forall ((a@@85 T@U) (x@@44 T@U) (T@@109 T@T) ) (!  (=> (not (U_2_bool (MapType0Select T@@109 boolType a@@85 x@@44))) (= (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@85 x@@44)) (+ (|Set#Card| T@@109 a@@85) 1)))
 :qid |testbpl.822:18|
 :skolemid |134|
 :pattern ( (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@85 x@@44)))
)))
(assert (forall ((s@@42 T@U) ) (! ($Is (MapType0Type BoxType boolType) (SetRef_to_SetBox s@@42) (TSet Tclass._System.object?))
 :qid |testbpl.440:15|
 :skolemid |82|
 :pattern ( (SetRef_to_SetBox s@@42))
)))
(assert (forall ((f@@25 T@U) (t0@@47 T@U) (h@@27 T@U) ) (!  (=> (and ($IsGoodHeap h@@27) ($IsAlloc HandleTypeType f@@25 (Tclass._System.___hFunc0 t0@@47) h@@27)) (=> (Requires0 t0@@47 h@@27 f@@25) ($IsAllocBox BoxType (Apply0 t0@@47 h@@27 f@@25) t0@@47 h@@27)))
 :qid |testbpl.2497:15|
 :skolemid |440|
 :pattern ( ($IsAlloc HandleTypeType f@@25 (Tclass._System.___hFunc0 t0@@47) h@@27))
)))
(assert (forall ((_System.array$arg@@12 T@U) ($h@@14 T@U) ($o@@8 T@U) ) (!  (=> (and (and (and ($IsGoodHeap $h@@14) (or (not (= $o@@8 null)) (not true))) (= (dtype $o@@8) (Tclass._System.array? _System.array$arg@@12))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@14 $o@@8) alloc)))) ($IsAlloc intType (int_2_U (_System.array.Length $o@@8)) TInt $h@@14))
 :qid |testbpl.1959:15|
 :skolemid |363|
 :pattern ( (_System.array.Length $o@@8) ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) $h@@14 $o@@8) alloc)) (Tclass._System.array? _System.array$arg@@12))
)))
(assert (forall ((s@@43 T@U) (m@@48 Int) (n@@21 Int) (T@@110 T@T) ) (!  (=> (and (and (<= 0 m@@48) (<= 0 n@@21)) (<= (+ m@@48 n@@21) (|Seq#Length| T@@110 s@@43))) (= (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@48) n@@21) (|Seq#Drop| T@@110 s@@43 (+ m@@48 n@@21))))
 :qid |testbpl.1454:18|
 :skolemid |273|
 :pattern ( (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@48) n@@21))
)))
(assert (forall ((s0@@7 T@U) (s1@@2 T@U) (n@@22 Int) (T@@111 T@T) ) (! (= (|Seq#SameUntil| T@@111 s0@@7 s1@@2 n@@22) (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 n@@22)) (= (|Seq#Index| T@@111 s0@@7 j@@3) (|Seq#Index| T@@111 s1@@2 j@@3)))
 :qid |testbpl.1335:19|
 :skolemid |248|
 :pattern ( (|Seq#Index| T@@111 s0@@7 j@@3))
 :pattern ( (|Seq#Index| T@@111 s1@@2 j@@3))
)))
 :qid |testbpl.1332:18|
 :skolemid |249|
 :pattern ( (|Seq#SameUntil| T@@111 s0@@7 s1@@2 n@@22))
)))
(assert (forall ((a@@86 T@U) (b@@57 T@U) (T@@112 T@T) ) (! (= (|Set#Disjoint| T@@112 a@@86 b@@57) (forall ((o@@49 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@112 boolType a@@86 o@@49))) (not (U_2_bool (MapType0Select T@@112 boolType b@@57 o@@49))))
 :qid |testbpl.909:35|
 :skolemid |153|
 :pattern ( (MapType0Select T@@112 boolType a@@86 o@@49))
 :pattern ( (MapType0Select T@@112 boolType b@@57 o@@49))
)))
 :qid |testbpl.907:18|
 :skolemid |154|
 :pattern ( (|Set#Disjoint| T@@112 a@@86 b@@57))
)))
(assert (forall ((a@@87 T@U) (b@@58 T@U) (T@@113 T@T) ) (! (= (|ISet#Disjoint| T@@113 a@@87 b@@58) (forall ((o@@50 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@113 boolType a@@87 o@@50))) (not (U_2_bool (MapType0Select T@@113 boolType b@@58 o@@50))))
 :qid |testbpl.1001:36|
 :skolemid |175|
 :pattern ( (MapType0Select T@@113 boolType a@@87 o@@50))
 :pattern ( (MapType0Select T@@113 boolType b@@58 o@@50))
)))
 :qid |testbpl.999:18|
 :skolemid |176|
 :pattern ( (|ISet#Disjoint| T@@113 a@@87 b@@58))
)))
(assert (forall ((a@@88 T@U) (x@@45 T@U) (y@@23 T@U) (T@@114 T@T) ) (!  (=> (or (not (= x@@45 y@@23)) (not true)) (= (U_2_int (MapType0Select T@@114 intType a@@88 y@@23)) (U_2_int (MapType0Select T@@114 intType (|MultiSet#UnionOne| T@@114 a@@88 x@@45) y@@23))))
 :qid |testbpl.1070:18|
 :skolemid |194|
 :pattern ( (|MultiSet#UnionOne| T@@114 a@@88 x@@45) (MapType0Select T@@114 intType a@@88 y@@23))
)))
(assert (forall ((s0@@8 T@U) (s1@@3 T@U) (n@@23 Int) (T@@115 T@T) ) (!  (and (=> (< n@@23 (|Seq#Length| T@@115 s0@@8)) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23) (|Seq#Index| T@@115 s0@@8 n@@23))) (=> (<= (|Seq#Length| T@@115 s0@@8) n@@23) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23) (|Seq#Index| T@@115 s1@@3 (- n@@23 (|Seq#Length| T@@115 s0@@8))))))
 :qid |testbpl.1264:18|
 :skolemid |233|
 :pattern ( (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@8 s1@@3) n@@23))
)))
(assert (forall ((o@@51 T@U) (p@@7 T@U) ) (!  (and (=> (|ORD#IsNat| (|ORD#Plus| o@@51 p@@7)) (and (|ORD#IsNat| o@@51) (|ORD#IsNat| p@@7))) (=> (|ORD#IsNat| p@@7) (and (= (|ORD#IsNat| (|ORD#Plus| o@@51 p@@7)) (|ORD#IsNat| o@@51)) (= (|ORD#Offset| (|ORD#Plus| o@@51 p@@7)) (+ (|ORD#Offset| o@@51) (|ORD#Offset| p@@7))))))
 :qid |testbpl.512:15|
 :skolemid |91|
 :pattern ( (|ORD#Plus| o@@51 p@@7))
)))
(assert (forall ((f@@26 T@U) (t0@@48 T@U) (u0@@8 T@U) ) (!  (=> (and ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 t0@@48)) (forall ((bx@@43 T@U) ) (!  (=> ($IsBox BoxType bx@@43 t0@@48) ($IsBox BoxType bx@@43 u0@@8))
 :qid |testbpl.2483:19|
 :skolemid |436|
 :pattern ( ($IsBox BoxType bx@@43 t0@@48))
 :pattern ( ($IsBox BoxType bx@@43 u0@@8))
))) ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 u0@@8)))
 :qid |testbpl.2480:15|
 :skolemid |437|
 :pattern ( ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 t0@@48)) ($Is HandleTypeType f@@26 (Tclass._System.___hFunc0 u0@@8)))
)))
(assert (forall ((a@@89 Int) ) (!  (=> (< a@@89 0) (= (|Math#clip| a@@89) 0))
 :qid |testbpl.1017:15|
 :skolemid |181|
 :pattern ( (|Math#clip| a@@89))
)))
(assert (forall ((|a#3#0#0| T@U) (|a#3#1#0| T@U) ) (! (= (|#_System._tuple#2._#Make2| (Lit BoxType |a#3#0#0|) (Lit BoxType |a#3#1#0|)) (Lit DatatypeTypeType (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|)))
 :qid |testbpl.2682:15|
 :skolemid |465|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit BoxType |a#3#0#0|) (Lit BoxType |a#3#1#0|)))
)))
(assert (forall ((x@@46 Int) ) (! (= ($Box intType (int_2_U (LitInt x@@46))) (Lit BoxType ($Box intType (int_2_U x@@46))))
 :qid |testbpl.144:15|
 :skolemid |18|
 :pattern ( ($Box intType (int_2_U (LitInt x@@46))))
)))
(assert (forall ((x@@47 Real) ) (! (= ($Box realType (real_2_U (LitReal x@@47))) (Lit BoxType ($Box realType (real_2_U x@@47))))
 :qid |testbpl.151:15|
 :skolemid |20|
 :pattern ( ($Box realType (real_2_U (LitReal x@@47))))
)))
(assert (forall ((x@@48 T@U) (T@@116 T@T) ) (! (= ($Box T@@116 (Lit T@@116 x@@48)) (Lit BoxType ($Box T@@116 x@@48)))
 :qid |testbpl.137:18|
 :skolemid |16|
 :pattern ( ($Box T@@116 (Lit T@@116 x@@48)))
)))
(assert (forall ((a@@90 T@U) (b@@59 T@U) (T@@117 T@T) ) (! (= (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@90 b@@59)) (|MultiSet#Union| T@@117 (|MultiSet#FromSeq| T@@117 a@@90) (|MultiSet#FromSeq| T@@117 b@@59)))
 :qid |testbpl.1175:18|
 :skolemid |217|
 :pattern ( (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@90 b@@59)))
)))
(assert (forall ((m@@49 T@U) (n@@24 T@U) (U@@36 T@T) (V@@36 T@T) ) (! (= (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@49 n@@24)) (|Set#Union| U@@36 (|Map#Domain| U@@36 V@@36 m@@49) (|Map#Domain| U@@36 V@@36 n@@24)))
 :qid |testbpl.1563:20|
 :skolemid |296|
 :pattern ( (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@49 n@@24)))
)))
(assert (forall ((m@@50 T@U) (n@@25 T@U) (U@@37 T@T) (V@@37 T@T) ) (! (= (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@50 n@@25)) (|Set#Union| U@@37 (|IMap#Domain| U@@37 V@@37 m@@50) (|IMap#Domain| U@@37 V@@37 n@@25)))
 :qid |testbpl.1702:20|
 :skolemid |328|
 :pattern ( (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@50 n@@25)))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@4 T@U) (|q#0@@4| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0@@4|) (< 0 $FunctionContextHeight)) true)
 :qid |testbpl.2832:16|
 :skolemid |482|
 :pattern ( (_module.__default.secretPredicate $ly@@4 |q#0@@4|))
))))
(assert (forall ((s@@44 T@U) (T@@118 T@T) ) (!  (=> (= (|Seq#Length| T@@118 s@@44) 0) (= s@@44 (|Seq#Empty| T@@118)))
 :qid |testbpl.1205:18|
 :skolemid |223|
 :pattern ( (|Seq#Length| T@@118 s@@44))
)))
(assert (forall ((s@@45 T@U) (n@@26 Int) (T@@119 T@T) ) (!  (=> (= n@@26 0) (= (|Seq#Take| T@@119 s@@45 n@@26) (|Seq#Empty| T@@119)))
 :qid |testbpl.1450:18|
 :skolemid |272|
 :pattern ( (|Seq#Take| T@@119 s@@45 n@@26))
)))
(assert (forall ((t0@@49 T@U) (heap@@10 T@U) (h@@28 T@U) (r@@13 T@U) (rd@@4 T@U) ) (!  (=> (U_2_bool (MapType0Select (MapType0Type refType (MapType1Type BoxType)) boolType r@@13 heap@@10)) (Requires0 t0@@49 heap@@10 (Handle0 h@@28 r@@13 rd@@4)))
 :qid |testbpl.2362:15|
 :skolemid |418|
 :pattern ( (Requires0 t0@@49 heap@@10 (Handle0 h@@28 r@@13 rd@@4)))
)))
(assert (forall ((s@@46 T@U) (x@@49 T@U) (n@@27 T@U) (T@@120 T@T) ) (!  (=> (<= 0 (U_2_int n@@27)) (= (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)) (+ (- (|MultiSet#Card| T@@120 s@@46) (U_2_int (MapType0Select T@@120 intType s@@46 x@@49))) (U_2_int n@@27))))
 :qid |testbpl.1032:18|
 :skolemid |185|
 :pattern ( (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)))
)))
(assert (forall ((t0@@50 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@27 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@10 h1@@10) ($IsGoodHeap h0@@10)) ($IsGoodHeap h1@@10)) ($Is HandleTypeType f@@27 (Tclass._System.___hFunc0 t0@@50))) (forall ((o@@52 T@U) (fld@@9 T@U) (a@@91 T@T) ) (!  (=> (and (or (not (= o@@52 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@50 h0@@10 f@@27) ($Box refType o@@52)))) (= ($Unbox a@@91 (MapType1Select a@@91 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@10 o@@52) fld@@9)) ($Unbox a@@91 (MapType1Select a@@91 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@10 o@@52) fld@@9))))
 :qid |testbpl.2414:22|
 :skolemid |424|
))) (= (Requires0 t0@@50 h0@@10 f@@27) (Requires0 t0@@50 h1@@10 f@@27)))
 :qid |testbpl.2407:15|
 :skolemid |425|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Requires0 t0@@50 h1@@10 f@@27))
)))
(assert (forall ((t0@@51 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@28 T@U) ) (!  (=> (and (and (and (and ($HeapSucc h0@@11 h1@@11) ($IsGoodHeap h0@@11)) ($IsGoodHeap h1@@11)) ($Is HandleTypeType f@@28 (Tclass._System.___hFunc0 t0@@51))) (forall ((o@@53 T@U) (fld@@10 T@U) (a@@92 T@T) ) (!  (=> (and (or (not (= o@@53 null)) (not true)) (U_2_bool (MapType0Select BoxType boolType (Reads0 t0@@51 h1@@11 f@@28) ($Box refType o@@53)))) (= ($Unbox a@@92 (MapType1Select a@@92 BoxType (MapType0Select refType (MapType1Type BoxType) h0@@11 o@@53) fld@@10)) ($Unbox a@@92 (MapType1Select a@@92 BoxType (MapType0Select refType (MapType1Type BoxType) h1@@11 o@@53) fld@@10))))
 :qid |testbpl.2427:22|
 :skolemid |426|
))) (= (Requires0 t0@@51 h0@@11 f@@28) (Requires0 t0@@51 h1@@11 f@@28)))
 :qid |testbpl.2420:15|
 :skolemid |427|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Requires0 t0@@51 h1@@11 f@@28))
)))
(assert (= |_module.__default.magicNum#requires| true))
(assert (forall ((a@@93 T@U) (b@@60 T@U) (o@@54 T@U) (T@@121 T@T) ) (! (= (U_2_bool (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@93 b@@60) o@@54))  (or (U_2_bool (MapType0Select T@@121 boolType a@@93 o@@54)) (U_2_bool (MapType0Select T@@121 boolType b@@60 o@@54))))
 :qid |testbpl.828:18|
 :skolemid |135|
 :pattern ( (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@93 b@@60) o@@54))
)))
(assert (forall ((a@@94 T@U) (b@@61 T@U) (o@@55 T@U) (T@@122 T@T) ) (! (= (U_2_bool (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@94 b@@61) o@@55))  (or (U_2_bool (MapType0Select T@@122 boolType a@@94 o@@55)) (U_2_bool (MapType0Select T@@122 boolType b@@61 o@@55))))
 :qid |testbpl.931:18|
 :skolemid |159|
 :pattern ( (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@94 b@@61) o@@55))
)))
(assert (forall ((h@@29 T@U) (v@@39 T@U) ) (! ($IsAlloc intType v@@39 TInt h@@29)
 :qid |testbpl.334:15|
 :skolemid |60|
 :pattern ( ($IsAlloc intType v@@39 TInt h@@29))
)))
(assert (forall ((h@@30 T@U) (v@@40 T@U) ) (! ($IsAlloc realType v@@40 TReal h@@30)
 :qid |testbpl.336:15|
 :skolemid |61|
 :pattern ( ($IsAlloc realType v@@40 TReal h@@30))
)))
(assert (forall ((h@@31 T@U) (v@@41 T@U) ) (! ($IsAlloc boolType v@@41 TBool h@@31)
 :qid |testbpl.338:15|
 :skolemid |62|
 :pattern ( ($IsAlloc boolType v@@41 TBool h@@31))
)))
(assert (forall ((h@@32 T@U) (v@@42 T@U) ) (! ($IsAlloc charType v@@42 TChar h@@32)
 :qid |testbpl.340:15|
 :skolemid |63|
 :pattern ( ($IsAlloc charType v@@42 TChar h@@32))
)))
(assert (forall ((h@@33 T@U) (v@@43 T@U) ) (! ($IsAlloc BoxType v@@43 TORDINAL h@@33)
 :qid |testbpl.342:15|
 :skolemid |64|
 :pattern ( ($IsAlloc BoxType v@@43 TORDINAL h@@33))
)))
(assert (forall ((s@@47 T@U) (i@@22 Int) (v@@44 T@U) (n@@28 Int) (T@@123 T@T) ) (!  (=> (and (and (<= 0 i@@22) (< i@@22 n@@28)) (<= n@@28 (|Seq#Length| T@@123 s@@47))) (= (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28) (|Seq#Update| T@@123 (|Seq#Take| T@@123 s@@47 n@@28) i@@22 v@@44)))
 :qid |testbpl.1395:18|
 :skolemid |261|
 :pattern ( (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28))
)))
(assert (forall ((v@@45 T@U) (t0@@52 T@U) ) (! (= ($Is (SeqType BoxType) v@@45 (TSeq t0@@52)) (forall ((i@@23 Int) ) (!  (=> (and (<= 0 i@@23) (< i@@23 (|Seq#Length| BoxType v@@45))) ($IsBox BoxType (|Seq#Index| BoxType v@@45 i@@23) t0@@52))
 :qid |testbpl.300:19|
 :skolemid |52|
 :pattern ( (|Seq#Index| BoxType v@@45 i@@23))
)))
 :qid |testbpl.297:15|
 :skolemid |53|
 :pattern ( ($Is (SeqType BoxType) v@@45 (TSeq t0@@52)))
)))
(assert (forall ((|#$R@@27| T@U) (|f#0@@6| T@U) ) (! (= ($Is HandleTypeType |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|))  (and ($Is HandleTypeType |f#0@@6| (Tclass._System.___hFunc0 |#$R@@27|)) (|Set#Equal| BoxType (Reads0 |#$R@@27| $OneHeap |f#0@@6|) (|Set#Empty| BoxType))))
 :qid |testbpl.2529:15|
 :skolemid |444|
 :pattern ( ($Is HandleTypeType |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|)))
)))
(assert (forall ((s@@48 T@U) (i@@24 Int) ) (!  (=> (and (<= 0 i@@24) (< i@@24 (|Seq#Length| BoxType s@@48))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))) (|Seq#Rank| BoxType s@@48)))
 :qid |testbpl.1428:15|
 :skolemid |267|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))))
)))
(assert (forall ((v@@46 T@U) (t0@@53 T@U) (t1@@24 T@U) ) (!  (=> ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@53 t1@@24)) (and (and ($Is (MapType0Type BoxType boolType) (|Map#Domain| BoxType BoxType v@@46) (TSet t0@@53)) ($Is (MapType0Type BoxType boolType) (|Map#Values| BoxType BoxType v@@46) (TSet t1@@24))) ($Is (MapType0Type BoxType boolType) (|Map#Items| BoxType BoxType v@@46) (TSet (Tclass._System.Tuple2 t0@@53 t1@@24)))))
 :qid |testbpl.311:15|
 :skolemid |56|
 :pattern ( ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@53 t1@@24)))
)))
(assert (forall ((v@@47 T@U) (t0@@54 T@U) (t1@@25 T@U) ) (!  (=> ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@54 t1@@25)) (and (and ($Is (MapType0Type BoxType boolType) (|IMap#Domain| BoxType BoxType v@@47) (TISet t0@@54)) ($Is (MapType0Type BoxType boolType) (|IMap#Values| BoxType BoxType v@@47) (TISet t1@@25))) ($Is (MapType0Type BoxType boolType) (|IMap#Items| BoxType BoxType v@@47) (TISet (Tclass._System.Tuple2 t0@@54 t1@@25)))))
 :qid |testbpl.325:15|
 :skolemid |59|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@54 t1@@25)))
)))
(assert (forall ((v@@48 T@U) ) (! ($Is intType v@@48 TInt)
 :qid |testbpl.268:15|
 :skolemid |39|
 :pattern ( ($Is intType v@@48 TInt))
)))
(assert (forall ((v@@49 T@U) ) (! ($Is realType v@@49 TReal)
 :qid |testbpl.270:15|
 :skolemid |40|
 :pattern ( ($Is realType v@@49 TReal))
)))
(assert (forall ((v@@50 T@U) ) (! ($Is boolType v@@50 TBool)
 :qid |testbpl.272:15|
 :skolemid |41|
 :pattern ( ($Is boolType v@@50 TBool))
)))
(assert (forall ((v@@51 T@U) ) (! ($Is charType v@@51 TChar)
 :qid |testbpl.274:15|
 :skolemid |42|
 :pattern ( ($Is charType v@@51 TChar))
)))
(assert (forall ((v@@52 T@U) ) (! ($Is BoxType v@@52 TORDINAL)
 :qid |testbpl.276:15|
 :skolemid |43|
 :pattern ( ($Is BoxType v@@52 TORDINAL))
)))
; Valid

(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun |q#0@@5| () Int)
(declare-fun |q##0_0@0| () Int)
(declare-fun $_ModifiesFrame@0 () T@U)
(declare-fun $Heap () T@U)
(declare-fun $IsHeapAnchor (T@U) Bool)
(set-info :boogie-vc-id Impl$$_module.__default.barLemma)
(set-option :timeout 0)
(set-option :rlimit 0)
(assert (not
 (=> (= (ControlFlow 0 0) 5) (let ((anon3_Else_correct true))
(let ((anon3_Then_correct  (=> (> |q#0@@5| 6789) (=> (and (= |q##0_0@0| (- |q#0@@5| 1)) (= (ControlFlow 0 2) (- 0 1))) (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate |q##0_0@0|)))))
(let ((anon0_correct  (=> (= (AsFuelBottom StartFuel__module._default.secretPredicate) StartFuel__module._default.secretPredicate) (=> (and (= (AsFuelBottom StartFuelAssert__module._default.secretPredicate) StartFuelAssert__module._default.secretPredicate) (= $_ModifiesFrame@0 (|lambda#1| null $Heap alloc false))) (and (=> (= (ControlFlow 0 4) 2) anon3_Then_correct) (=> (= (ControlFlow 0 4) 3) anon3_Else_correct))))))
(let ((PreconditionGeneratedEntry_correct  (=> (and (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (= 2 $FunctionContextHeight)) (and (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate |q#0@@5|) (= (ControlFlow 0 5) 4))) anon0_correct)))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)
(pop 1)
; Valid
(get-info :rlimit)
