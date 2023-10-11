(set-option :print-success false)
(set-info :smt-lib-version 2.6)
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
(declare-fun $IsAlloc (T@T T@U T@U T@U) Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun |MultiSet#Card| (T@T T@U) Int)
(declare-fun |MultiSet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@T T@U T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType1Select (T@T T@T T@U T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun refType () T@T)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType1Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun |ORD#Less| (T@U T@U) Bool)
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
(declare-fun $Is (T@T T@U T@U) Bool)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#Offset| (T@U) Int)
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
(declare-fun |Map#Card| (T@T T@T T@U) Int)
(declare-fun |Map#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun |Set#Singleton| (T@T T@U) T@U)
(declare-fun |Set#Card| (T@T T@U) Int)
(declare-fun |Map#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Subtract| (T@T T@T T@U T@U) T@U)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun IndexField (Int) T@U)
(declare-fun TSet (T@U) T@U)
(declare-fun $IsBox (T@T T@U T@U) Bool)
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
(declare-fun |Seq#Equal| (T@T T@U T@U) Bool)
(declare-fun |Seq#Rank| (T@T T@U) Int)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun |MultiSet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun AtLayer (T@T T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun $IsGhostField (T@T T@U) Bool)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $OneHeap () T@U)
(declare-fun |Seq#Create| (T@U T@U Int T@U) T@U)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun $Box (T@T T@U) T@U)
(declare-fun $IsAllocBox (T@T T@U T@U T@U) Bool)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |Set#Equal| (T@T T@U T@U) Bool)
(declare-fun |ISet#Equal| (T@T T@U T@U) Bool)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |Map#Values| (T@T T@T T@U) T@U)
(declare-fun |IMap#Values| (T@T T@T T@U) T@U)
(declare-fun |Set#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |Set#Difference| (T@T T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |ISet#Difference| (T@T T@U T@U) T@U)
(declare-fun |MultiSet#Equal| (T@T T@U T@U) Bool)
(declare-fun |MultiSet#Subset| (T@T T@U T@U) Bool)
(declare-fun |Map#Items| (T@T T@T T@U) T@U)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun DatatypeTypeType () T@T)
(declare-fun _System.Tuple2._1 (T@U) T@U)
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
(declare-fun |Map#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |IMap#Equal| (T@T T@T T@U T@U) Bool)
(declare-fun |Set#UnionOne| (T@T T@U T@U) T@U)
(declare-fun |ISet#UnionOne| (T@T T@U T@U) T@U)
(declare-fun q@Real (Int) Real)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
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
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun IndexField_Inverse (T@T T@U) Int)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun |Map#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Merge| (T@T T@T T@U T@U) T@U)
(declare-fun |IMap#Build| (T@T T@T T@U T@U T@U) T@U)
(declare-fun $LS (T@U) T@U)
(declare-fun |MultiSet#Disjoint| (T@T T@U T@U) Bool)
(declare-fun |Set#Empty| (T@T) T@U)
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
(declare-fun BoxRank (T@U) Int)
(declare-fun DtRank (T@U) Int)
(declare-fun |Set#Subset| (T@T T@U T@U) Bool)
(declare-fun |ISet#Subset| (T@T T@U T@U) Bool)
(declare-fun Tclass._System.object? () T@U)
(declare-fun |Seq#SameUntil| (T@T T@U T@U Int) Bool)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
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
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName)
)
(assert  (and (forall ((t0 T@T) (t1 T@T) (val T@U) (m T@U) (x0 T@U) ) (! (= (MapType0Select t0 t1 (MapType0Store t0 t1 m x0 val) x0) val)
 :qid |mapAx0:MapType0Select|
 :weight 0
)) (forall ((u0 T@T) (u1 T@T) (val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select u0 u1 (MapType0Store u0 u1 m@@0 x0@@0 val@@0) y0) (MapType0Select u0 u1 m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
))))
(assert (forall ((m@@1 T@U) (|m'| T@U) (U T@T) (V T@T) ) (! (= (|Map#Disjoint| U V m@@1 |m'|) (forall ((o T@U) ) (!  (or (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V m@@1) o))) (not (U_2_bool (MapType0Select U boolType (|Map#Domain| U V |m'|) o))))
 :qid |DafnyPreludebpl.1320:38|
 :skolemid |304|
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V m@@1) o))
 :pattern ( (MapType0Select U boolType (|Map#Domain| U V |m'|) o))
)))
 :qid |DafnyPreludebpl.1318:21|
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
(assert (forall ((v T@U) (h T@U) ) (! ($IsAlloc intType v (TBitvector 0) h)
 :qid |DafnyPreludebpl.293:15|
 :skolemid |65|
 :pattern ( ($IsAlloc intType v (TBitvector 0) h))
)))
(assert (forall ((a T@U) (b T@U) (T T@T) ) (!  (and (= (+ (+ (|MultiSet#Card| T (|MultiSet#Difference| T a b)) (|MultiSet#Card| T (|MultiSet#Difference| T b a))) (* 2 (|MultiSet#Card| T (|MultiSet#Intersection| T a b)))) (|MultiSet#Card| T (|MultiSet#Union| T a b))) (= (|MultiSet#Card| T (|MultiSet#Difference| T a b)) (- (|MultiSet#Card| T a) (|MultiSet#Card| T (|MultiSet#Intersection| T a b)))))
 :qid |DafnyPreludebpl.892:18|
 :skolemid |203|
 :pattern ( (|MultiSet#Card| T (|MultiSet#Difference| T a b)))
)))
(assert  (and (and (and (and (and (forall ((t0@@0 T@T) (t1@@0 T@T) (val@@1 T@U) (m@@2 T@U) (x0@@1 T@U) ) (! (= (MapType1Select t0@@0 t1@@0 (MapType1Store t0@@0 t1@@0 m@@2 x0@@1 val@@1) x0@@1) val@@1)
 :qid |mapAx0:MapType1Select|
 :weight 0
)) (and (forall ((u0@@0 T@T) (s0 T@T) (t0@@1 T@T) (val@@2 T@U) (m@@3 T@U) (x0@@2 T@U) (y0@@0 T@U) ) (!  (or (= s0 t0@@1) (= (MapType1Select t0@@1 u0@@0 (MapType1Store s0 u0@@0 m@@3 x0@@2 val@@2) y0@@0) (MapType1Select t0@@1 u0@@0 m@@3 y0@@0)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((u0@@1 T@T) (s0@@0 T@T) (t0@@2 T@T) (val@@3 T@U) (m@@4 T@U) (x0@@3 T@U) (y0@@1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select t0@@2 u0@@1 (MapType1Store s0@@0 u0@@1 m@@4 x0@@3 val@@3) y0@@1) (MapType1Select t0@@2 u0@@1 m@@4 y0@@1)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
)))) (= (Ctor BoxType) 3)) (= (Ctor refType) 4)) (forall ((arg0@@2 T@T) ) (! (= (Ctor (MapType1Type arg0@@2)) 5)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@3 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@3)) arg0@@3)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@3))
))))
(assert (forall ((h@@0 T@U) (k T@U) ) (!  (=> ($HeapSucc h@@0 k) (forall ((o@@0 T@U) ) (!  (=> (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) h@@0 o@@0) alloc))) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@0) alloc))))
 :qid |DafnyPreludebpl.607:30|
 :skolemid |117|
 :pattern ( ($Unbox boolType (MapType1Select boolType BoxType (MapType0Select refType (MapType1Type BoxType) k o@@0) alloc)))
)))
 :qid |DafnyPreludebpl.606:15|
 :skolemid |118|
 :pattern ( ($HeapSucc h@@0 k))
)))
(assert (forall ((o@@1 T@U) (p T@U) (r T@U) ) (!  (=> (and (|ORD#Less| o@@1 p) (|ORD#Less| p r)) (|ORD#Less| o@@1 r))
 :qid |DafnyPreludebpl.425:15|
 :skolemid |89|
 :pattern ( (|ORD#Less| o@@1 p) (|ORD#Less| p r))
 :pattern ( (|ORD#Less| o@@1 p) (|ORD#Less| o@@1 r))
)))
(assert (forall ((T@@0 T@T) ) (! (= (|MultiSet#FromSeq| T@@0 (|Seq#Empty| T@@0)) (|MultiSet#Empty| T@@0))
 :skolemid |213|
)))
(assert (forall ((s T@U) (v@@0 T@U) (x@@2 T@U) (T@@1 T@T) ) (! (= (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2)  (or (= v@@0 x@@2) (|Seq#Contains| T@@1 s x@@2)))
 :qid |DafnyPreludebpl.1042:18|
 :skolemid |240|
 :pattern ( (|Seq#Contains| T@@1 (|Seq#Build| T@@1 s v@@0) x@@2))
)))
(assert (forall ((a@@0 T@U) (b@@0 T@U) (t T@U) (U@@0 T@T) (V@@0 T@T) ) (! (= (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@0 b@@0 t)) a@@0)
 :qid |DafnyPreludebpl.1255:21|
 :skolemid |289|
 :pattern ( (|Map#Domain| U@@0 V@@0 (|Map#Glue| U@@0 V@@0 a@@0 b@@0 t)))
)))
(assert (forall ((a@@1 T@U) (b@@1 T@U) (t@@0 T@U) (U@@1 T@T) (V@@1 T@T) ) (! (= (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@1 b@@1 t@@0)) b@@1)
 :qid |DafnyPreludebpl.1258:21|
 :skolemid |290|
 :pattern ( (|Map#Elements| U@@1 V@@1 (|Map#Glue| U@@1 V@@1 a@@1 b@@1 t@@0)))
)))
(assert (forall ((a@@2 T@U) (b@@2 T@U) (t@@1 T@U) (U@@2 T@T) (V@@2 T@T) ) (! (= (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@2 b@@2 t@@1)) a@@2)
 :qid |DafnyPreludebpl.1390:21|
 :skolemid |319|
 :pattern ( (|IMap#Domain| U@@2 V@@2 (|IMap#Glue| U@@2 V@@2 a@@2 b@@2 t@@1)))
)))
(assert (forall ((a@@3 T@U) (b@@3 T@U) (t@@2 T@U) (U@@3 T@T) (V@@3 T@T) ) (! (= (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@3 b@@3 t@@2)) b@@3)
 :qid |DafnyPreludebpl.1393:21|
 :skolemid |320|
 :pattern ( (|IMap#Elements| U@@3 V@@3 (|IMap#Glue| U@@3 V@@3 a@@3 b@@3 t@@2)))
)))
(assert (forall ((v@@1 T@U) ) (! ($Is intType v@@1 (TBitvector 0))
 :qid |DafnyPreludebpl.234:15|
 :skolemid |44|
 :pattern ( ($Is intType v@@1 (TBitvector 0)))
)))
(assert (forall ((a@@4 Int) (b@@4 Int) ) (!  (or (= (|Math#min| a@@4 b@@4) a@@4) (= (|Math#min| a@@4 b@@4) b@@4))
 :qid |DafnyPreludebpl.822:15|
 :skolemid |179|
 :pattern ( (|Math#min| a@@4 b@@4))
)))
(assert (forall ((o@@2 T@U) (m@@5 Int) (n Int) ) (!  (=> (and (and (<= 0 m@@5) (<= 0 n)) (<= (+ m@@5 n) (|ORD#Offset| o@@2))) (= (|ORD#Minus| (|ORD#Minus| o@@2 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)) (|ORD#Minus| o@@2 (|ORD#FromNat| (+ m@@5 n)))))
 :qid |DafnyPreludebpl.464:15|
 :skolemid |97|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@2 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n)))
)))
(assert (forall ((x@@3 T@U) (T@@2 T@T) ) (!  (not (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
 :qid |DafnyPreludebpl.1033:18|
 :skolemid |238|
 :pattern ( (|Seq#Contains| T@@2 (|Seq#Empty| T@@2) x@@3))
)))
(assert (forall ((s@@0 T@U) (v@@2 T@U) (n@@0 Int) (T@@3 T@T) ) (!  (=> (and (<= 0 n@@0) (<= n@@0 (|Seq#Length| T@@3 s@@0))) (= (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0) (|Seq#Build| T@@3 (|Seq#Drop| T@@3 s@@0 n@@0) v@@2)))
 :qid |DafnyPreludebpl.1147:18|
 :skolemid |266|
 :pattern ( (|Seq#Drop| T@@3 (|Seq#Build| T@@3 s@@0 v@@2) n@@0))
)))
(assert  (and (and (forall ((arg0@@4 T@T) (arg1 T@T) ) (! (= (Ctor (MapType0Type arg0@@4 arg1)) 6)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@5 T@T) (arg1@@0 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@5 arg1@@0)) arg0@@5)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@5 arg1@@0))
))) (forall ((arg0@@6 T@T) (arg1@@1 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@6 arg1@@1)) arg1@@1)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@6 arg1@@1))
))))
(assert (forall ((v@@3 T@U) (t0@@3 T@U) ) (!  (=> ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@3)) ($IsGoodMultiSet BoxType v@@3))
 :qid |DafnyPreludebpl.248:15|
 :skolemid |51|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@3 (TMultiSet t0@@3)))
)))
(assert (forall ((s@@1 T@U) (T@@4 T@T) ) (! ($IsGoodMultiSet T@@4 (|MultiSet#FromSeq| T@@4 s@@1))
 :qid |DafnyPreludebpl.929:18|
 :skolemid |214|
 :pattern ( (|MultiSet#FromSeq| T@@4 s@@1))
)))
(assert (forall ((s@@2 T@U) (i Int) (v@@4 T@U) (n@@1 Int) (T@@5 T@T) ) (!  (=> (and (<= 0 n@@1) (< n@@1 (|Seq#Length| T@@5 s@@2))) (and (=> (= i n@@1) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) v@@4)) (=> (or (not (= i n@@1)) (not true)) (= (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1) (|Seq#Index| T@@5 s@@2 n@@1)))))
 :qid |DafnyPreludebpl.1024:18|
 :skolemid |235|
 :pattern ( (|Seq#Index| T@@5 (|Seq#Update| T@@5 s@@2 i v@@4) n@@1))
)))
(assert (forall ((a@@5 T@U) (b@@5 T@U) (T@@6 T@T) ) (! (= (|Set#Union| T@@6 (|Set#Union| T@@6 a@@5 b@@5) b@@5) (|Set#Union| T@@6 a@@5 b@@5))
 :qid |DafnyPreludebpl.707:18|
 :skolemid |140|
 :pattern ( (|Set#Union| T@@6 (|Set#Union| T@@6 a@@5 b@@5) b@@5))
)))
(assert (forall ((a@@6 T@U) (b@@6 T@U) (T@@7 T@T) ) (! (= (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@6 b@@6) b@@6) (|Set#Intersection| T@@7 a@@6 b@@6))
 :qid |DafnyPreludebpl.711:18|
 :skolemid |142|
 :pattern ( (|Set#Intersection| T@@7 (|Set#Intersection| T@@7 a@@6 b@@6) b@@6))
)))
(assert (forall ((a@@7 T@U) (b@@7 T@U) (T@@8 T@T) ) (! (= (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@7 b@@7) b@@7) (|ISet#Union| T@@8 a@@7 b@@7))
 :qid |DafnyPreludebpl.785:18|
 :skolemid |164|
 :pattern ( (|ISet#Union| T@@8 (|ISet#Union| T@@8 a@@7 b@@7) b@@7))
)))
(assert (forall ((a@@8 T@U) (b@@8 T@U) (T@@9 T@T) ) (! (= (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@8 b@@8) b@@8) (|ISet#Intersection| T@@9 a@@8 b@@8))
 :qid |DafnyPreludebpl.789:18|
 :skolemid |166|
 :pattern ( (|ISet#Intersection| T@@9 (|ISet#Intersection| T@@9 a@@8 b@@8) b@@8))
)))
(assert (forall ((a@@9 T@U) (b@@9 T@U) (T@@10 T@T) ) (! (= (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@9 b@@9) b@@9) (|MultiSet#Intersection| T@@10 a@@9 b@@9))
 :qid |DafnyPreludebpl.881:18|
 :skolemid |199|
 :pattern ( (|MultiSet#Intersection| T@@10 (|MultiSet#Intersection| T@@10 a@@9 b@@9) b@@9))
)))
(assert (forall ((s@@3 T@U) (t@@3 T@U) (n@@2 Int) (T@@11 T@T) ) (!  (=> (= n@@2 (|Seq#Length| T@@11 s@@3)) (and (= (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) s@@3) (= (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2) t@@3)))
 :qid |DafnyPreludebpl.1096:18|
 :skolemid |255|
 :pattern ( (|Seq#Take| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
 :pattern ( (|Seq#Drop| T@@11 (|Seq#Append| T@@11 s@@3 t@@3) n@@2))
)))
(assert (forall ((m@@6 T@U) (u T@U) (v@@5 T@U) (U@@4 T@T) (V@@4 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@4 boolType (|Map#Domain| U@@4 V@@4 m@@6) u)) (= (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)) (|Map#Card| U@@4 V@@4 m@@6)))
 :qid |DafnyPreludebpl.1281:21|
 :skolemid |294|
 :pattern ( (|Map#Card| U@@4 V@@4 (|Map#Build| U@@4 V@@4 m@@6 u v@@5)))
)))
(assert (forall ((r@@0 T@U) (o@@3 T@U) (T@@12 T@T) ) (! (= (U_2_bool (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@3)) (= r@@0 o@@3))
 :qid |DafnyPreludebpl.672:18|
 :skolemid |128|
 :pattern ( (MapType0Select T@@12 boolType (|Set#Singleton| T@@12 r@@0) o@@3))
)))
(assert (forall ((s@@4 T@U) (x@@4 T@U) (T@@13 T@T) ) (! (= (exists ((i@@0 Int) ) (!  (and (and (<= 0 i@@0) (< i@@0 (|Seq#Length| T@@13 s@@4))) (= x@@4 (|Seq#Index| T@@13 s@@4 i@@0)))
 :qid |DafnyPreludebpl.953:11|
 :skolemid |219|
 :pattern ( (|Seq#Index| T@@13 s@@4 i@@0))
)) (< 0 (U_2_int (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))))
 :qid |DafnyPreludebpl.952:18|
 :skolemid |220|
 :pattern ( (MapType0Select T@@13 intType (|MultiSet#FromSeq| T@@13 s@@4) x@@4))
)))
(assert (forall ((a@@10 T@U) (b@@10 T@U) (T@@14 T@T) ) (! (= (+ (|Set#Card| T@@14 (|Set#Union| T@@14 a@@10 b@@10)) (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@10 b@@10))) (+ (|Set#Card| T@@14 a@@10) (|Set#Card| T@@14 b@@10)))
 :qid |DafnyPreludebpl.715:18|
 :skolemid |144|
 :pattern ( (|Set#Card| T@@14 (|Set#Union| T@@14 a@@10 b@@10)))
 :pattern ( (|Set#Card| T@@14 (|Set#Intersection| T@@14 a@@10 b@@10)))
)))
(assert (forall ((m@@7 T@U) (s@@5 T@U) (u@@0 T@U) (U@@5 T@T) (V@@5 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@5 boolType (|Map#Domain| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0)) (= (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0) (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 m@@7) u@@0)))
 :qid |DafnyPreludebpl.1301:21|
 :skolemid |299|
 :pattern ( (MapType0Select U@@5 V@@5 (|Map#Elements| U@@5 V@@5 (|Map#Subtract| U@@5 V@@5 m@@7 s@@5)) u@@0))
)))
(assert (forall ((m@@8 T@U) (s@@6 T@U) (u@@1 T@U) (U@@6 T@T) (V@@6 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@6 boolType (|IMap#Domain| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1)) (= (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1) (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 m@@8) u@@1)))
 :qid |DafnyPreludebpl.1442:21|
 :skolemid |331|
 :pattern ( (MapType0Select U@@6 V@@6 (|IMap#Elements| U@@6 V@@6 (|IMap#Subtract| U@@6 V@@6 m@@8 s@@6)) u@@1))
)))
(assert (forall ((h@@1 T@U) (a@@11 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@11))) (= (|Seq#Take| BoxType (|Seq#FromArray| h@@1 a@@11) n1) (|Seq#Build| BoxType (|Seq#Take| BoxType (|Seq#FromArray| h@@1 a@@11) n0) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@1 a@@11) (IndexField n0))))))
 :qid |DafnyPreludebpl.1143:15|
 :skolemid |265|
 :pattern ( (|Seq#Take| BoxType (|Seq#FromArray| h@@1 a@@11) n0) (|Seq#Take| BoxType (|Seq#FromArray| h@@1 a@@11) n1))
)))
(assert (forall ((s@@7 T@U) (i@@1 Int) (v@@6 T@U) (n@@3 Int) (T@@15 T@T) ) (!  (=> (and (and (<= 0 n@@3) (<= n@@3 i@@1)) (< i@@1 (|Seq#Length| T@@15 s@@7))) (= (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3) (|Seq#Update| T@@15 (|Seq#Drop| T@@15 s@@7 n@@3) (- i@@1 n@@3) v@@6)))
 :qid |DafnyPreludebpl.1136:18|
 :skolemid |263|
 :pattern ( (|Seq#Drop| T@@15 (|Seq#Update| T@@15 s@@7 i@@1 v@@6) n@@3))
)))
(assert (forall ((a@@12 T@U) (b@@11 T@U) (o@@4 T@U) (T@@16 T@T) ) (! (= (U_2_int (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@12 b@@11) o@@4)) (+ (U_2_int (MapType0Select T@@16 intType a@@12 o@@4)) (U_2_int (MapType0Select T@@16 intType b@@11 o@@4))))
 :qid |DafnyPreludebpl.871:18|
 :skolemid |196|
 :pattern ( (MapType0Select T@@16 intType (|MultiSet#Union| T@@16 a@@12 b@@11) o@@4))
)))
(assert (forall ((s@@8 T@U) (n@@4 Int) (T@@17 T@T) ) (!  (=> (= n@@4 0) (= (|Seq#Drop| T@@17 s@@8 n@@4) s@@8))
 :qid |DafnyPreludebpl.1166:18|
 :skolemid |271|
 :pattern ( (|Seq#Drop| T@@17 s@@8 n@@4))
)))
(assert (forall ((v@@7 T@U) (t0@@4 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@4)) (forall ((bx T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@7 bx)) ($IsBox BoxType bx t0@@4))
 :qid |DafnyPreludebpl.238:11|
 :skolemid |45|
 :pattern ( (MapType0Select BoxType boolType v@@7 bx))
)))
 :qid |DafnyPreludebpl.236:15|
 :skolemid |46|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@7 (TSet t0@@4)))
)))
(assert (forall ((v@@8 T@U) (t0@@5 T@U) ) (! (= ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@5)) (forall ((bx@@0 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@8 bx@@0)) ($IsBox BoxType bx@@0 t0@@5))
 :qid |DafnyPreludebpl.242:11|
 :skolemid |47|
 :pattern ( (MapType0Select BoxType boolType v@@8 bx@@0))
)))
 :qid |DafnyPreludebpl.240:15|
 :skolemid |48|
 :pattern ( ($Is (MapType0Type BoxType boolType) v@@8 (TISet t0@@5)))
)))
(assert (forall ((a@@13 Int) ) (!  (=> (<= 0 a@@13) (= (|Math#clip| a@@13) a@@13))
 :qid |DafnyPreludebpl.825:15|
 :skolemid |180|
 :pattern ( (|Math#clip| a@@13))
)))
(assert (forall ((x@@5 Real) ) (! (= (q@Int x@@5) (to_int x@@5))
 :qid |DafnyPreludebpl.576:14|
 :skolemid |112|
 :pattern ( (q@Int x@@5))
)))
(assert (forall ((x@@6 Int) ) (! (= (LitInt x@@6) x@@6)
 :qid |DafnyPreludebpl.108:29|
 :skolemid |17|
 :pattern ( (LitInt x@@6))
)))
(assert (forall ((x@@7 Real) ) (! (= (LitReal x@@7) x@@7)
 :qid |DafnyPreludebpl.111:30|
 :skolemid |19|
 :pattern ( (LitReal x@@7))
)))
(assert (forall ((x@@8 T@U) (T@@18 T@T) ) (! (= (Lit T@@18 x@@8) x@@8)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit T@@18 x@@8))
)))
(assert  (and (forall ((arg0@@7 T@T) ) (! (= (Ctor (SeqType arg0@@7)) 7)
 :qid |ctor:SeqType|
)) (forall ((arg0@@8 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@8)) arg0@@8)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@8))
))))
(assert (forall ((s@@9 T@U) (bx@@1 T@U) (t@@4 T@U) ) (!  (=> (and ($Is (SeqType BoxType) s@@9 (TSeq t@@4)) ($IsBox BoxType bx@@1 t@@4)) ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@1) (TSeq t@@4)))
 :qid |DafnyPreludebpl.998:15|
 :skolemid |228|
 :pattern ( ($Is (SeqType BoxType) (|Seq#Build| BoxType s@@9 bx@@1) (TSeq t@@4)))
)))
(assert $$Language$Dafny)
(assert (forall ((s@@10 T@U) (n@@5 Int) (j Int) (T@@19 T@T) ) (!  (=> (and (and (<= 0 j) (< j n@@5)) (< j (|Seq#Length| T@@19 s@@10))) (= (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j) (|Seq#Index| T@@19 s@@10 j)))
 :qid |DafnyPreludebpl.1075:18|
 :weight 25
 :skolemid |251|
 :pattern ( (|Seq#Index| T@@19 (|Seq#Take| T@@19 s@@10 n@@5) j))
 :pattern ( (|Seq#Index| T@@19 s@@10 j) (|Seq#Take| T@@19 s@@10 n@@5))
)))
(assert (forall ((s@@11 T@U) (n@@6 Int) (T@@20 T@T) ) (!  (=> (and (<= 0 n@@6) (<= n@@6 (|Seq#Length| T@@20 s@@11))) (= (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)) (- (|Seq#Length| T@@20 s@@11) n@@6)))
 :qid |DafnyPreludebpl.1083:18|
 :skolemid |252|
 :pattern ( (|Seq#Length| T@@20 (|Seq#Drop| T@@20 s@@11 n@@6)))
)))
(assert (forall ((m@@9 T@U) (u@@2 T@U) (v@@9 T@U) (U@@7 T@T) (V@@7 T@T) ) (!  (=> (not (U_2_bool (MapType0Select U@@7 boolType (|Map#Domain| U@@7 V@@7 m@@9) u@@2))) (= (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)) (+ (|Map#Card| U@@7 V@@7 m@@9) 1)))
 :qid |DafnyPreludebpl.1283:21|
 :skolemid |295|
 :pattern ( (|Map#Card| U@@7 V@@7 (|Map#Build| U@@7 V@@7 m@@9 u@@2 v@@9)))
)))
(assert (forall ((s0@@1 T@U) (s1 T@U) (T@@21 T@T) ) (! (= (|Seq#Equal| T@@21 s0@@1 s1)  (and (= (|Seq#Length| T@@21 s0@@1) (|Seq#Length| T@@21 s1)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| T@@21 s0@@1))) (= (|Seq#Index| T@@21 s0@@1 j@@0) (|Seq#Index| T@@21 s1 j@@0)))
 :qid |DafnyPreludebpl.1061:13|
 :skolemid |245|
 :pattern ( (|Seq#Index| T@@21 s0@@1 j@@0))
 :pattern ( (|Seq#Index| T@@21 s1 j@@0))
))))
 :qid |DafnyPreludebpl.1058:18|
 :skolemid |246|
 :pattern ( (|Seq#Equal| T@@21 s0@@1 s1))
)))
(assert (forall ((a@@14 T@U) (b@@12 T@U) (o@@5 T@U) (T@@22 T@T) ) (! (= (U_2_int (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@14 b@@12) o@@5)) (|Math#clip| (- (U_2_int (MapType0Select T@@22 intType a@@14 o@@5)) (U_2_int (MapType0Select T@@22 intType b@@12 o@@5)))))
 :qid |DafnyPreludebpl.888:18|
 :skolemid |201|
 :pattern ( (MapType0Select T@@22 intType (|MultiSet#Difference| T@@22 a@@14 b@@12) o@@5))
)))
(assert (forall ((s@@12 T@U) (i@@2 Int) (T@@23 T@T) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| T@@23 s@@12))) (< (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)) (|Seq#Rank| T@@23 s@@12)))
 :qid |DafnyPreludebpl.1158:18|
 :skolemid |269|
 :pattern ( (|Seq#Rank| T@@23 (|Seq#Take| T@@23 s@@12 i@@2)))
)))
(assert (forall ((T@@24 T@T) ) (! (= (|Seq#Length| T@@24 (|Seq#Empty| T@@24)) 0)
 :skolemid |222|
 :pattern ( (|Seq#Empty| T@@24))
)))
(assert (forall ((s@@13 T@U) (bx@@2 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@2)) (U_2_bool (MapType0Select refType boolType s@@13 ($Unbox refType bx@@2))))
 :qid |DafnyPreludebpl.368:15|
 :skolemid |81|
 :pattern ( (MapType0Select BoxType boolType (SetRef_to_SetBox s@@13) bx@@2))
)))
(assert (forall ((f T@U) (i@@3 Int) ) (! (= (FDim BoxType (MultiIndexField f i@@3)) (+ (FDim BoxType f) 1))
 :qid |DafnyPreludebpl.518:15|
 :skolemid |104|
 :pattern ( (MultiIndexField f i@@3))
)))
(assert (forall ((a@@15 T@U) (x@@9 T@U) (T@@25 T@T) ) (! (= (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@15 x@@9)) (+ (|MultiSet#Card| T@@25 a@@15) 1))
 :qid |DafnyPreludebpl.865:18|
 :skolemid |195|
 :pattern ( (|MultiSet#Card| T@@25 (|MultiSet#UnionOne| T@@25 a@@15 x@@9)))
)))
(assert (forall ((s@@14 T@U) (i@@4 Int) (T@@26 T@T) ) (!  (=> (and (< 0 i@@4) (<= i@@4 (|Seq#Length| T@@26 s@@14))) (< (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)) (|Seq#Rank| T@@26 s@@14)))
 :qid |DafnyPreludebpl.1155:18|
 :skolemid |268|
 :pattern ( (|Seq#Rank| T@@26 (|Seq#Drop| T@@26 s@@14 i@@4)))
)))
(assert (= (Ctor LayerTypeType) 8))
(assert (forall ((f@@0 T@U) (ly T@U) (A T@T) ) (! (= (AtLayer A f@@0 ly) (MapType0Select LayerTypeType A f@@0 ly))
 :qid |DafnyPreludebpl.499:18|
 :skolemid |100|
 :pattern ( (AtLayer A f@@0 ly))
)))
(assert ($IsGhostField boolType alloc))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((s@@15 T@U) (v@@10 T@U) (T@@27 T@T) ) (! (= (|Seq#Length| T@@27 (|Seq#Build| T@@27 s@@15 v@@10)) (+ 1 (|Seq#Length| T@@27 s@@15)))
 :qid |DafnyPreludebpl.990:18|
 :skolemid |226|
 :pattern ( (|Seq#Build| T@@27 s@@15 v@@10))
)))
(assert (forall ((ty T@U) (heap T@U) (len Int) (init T@U) (i@@5 Int) ) (!  (=> (and (and ($IsGoodHeap heap) (<= 0 i@@5)) (< i@@5 len)) (= (|Seq#Index| BoxType (|Seq#Create| ty heap len init) i@@5) (Apply1 TInt ty heap init ($Box intType (int_2_U i@@5)))))
 :qid |DafnyPreludebpl.1006:15|
 :skolemid |230|
 :pattern ( (|Seq#Index| BoxType (|Seq#Create| ty heap len init) i@@5))
)))
(assert (forall ((v@@11 T@U) (t@@5 T@U) (h@@2 T@U) (T@@28 T@T) ) (! (= ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@2) ($IsAlloc T@@28 v@@11 t@@5 h@@2))
 :qid |DafnyPreludebpl.215:18|
 :skolemid |38|
 :pattern ( ($IsAllocBox BoxType ($Box T@@28 v@@11) t@@5 h@@2))
)))
(assert (forall ((h@@3 T@U) (k@@0 T@U) (bx@@3 T@U) (t@@6 T@U) ) (!  (=> ($HeapSucc h@@3 k@@0) (=> ($IsAllocBox BoxType bx@@3 t@@6 h@@3) ($IsAllocBox BoxType bx@@3 t@@6 k@@0)))
 :qid |DafnyPreludebpl.555:15|
 :skolemid |110|
 :pattern ( ($HeapSucc h@@3 k@@0) ($IsAllocBox BoxType bx@@3 t@@6 h@@3))
)))
(assert (forall ((h@@4 T@U) (k@@1 T@U) (v@@12 T@U) (t@@7 T@U) (T@@29 T@T) ) (!  (=> ($HeapSucc h@@4 k@@1) (=> ($IsAlloc T@@29 v@@12 t@@7 h@@4) ($IsAlloc T@@29 v@@12 t@@7 k@@1)))
 :qid |DafnyPreludebpl.552:18|
 :skolemid |109|
 :pattern ( ($HeapSucc h@@4 k@@1) ($IsAlloc T@@29 v@@12 t@@7 h@@4))
)))
(assert (forall ((s@@16 T@U) (n@@7 Int) (j@@1 Int) (T@@30 T@T) ) (!  (=> (and (and (<= 0 n@@7) (<= 0 j@@1)) (< j@@1 (- (|Seq#Length| T@@30 s@@16) n@@7))) (= (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1) (|Seq#Index| T@@30 s@@16 (+ j@@1 n@@7))))
 :qid |DafnyPreludebpl.1085:18|
 :weight 25
 :skolemid |253|
 :pattern ( (|Seq#Index| T@@30 (|Seq#Drop| T@@30 s@@16 n@@7) j@@1))
)))
(assert (forall ((s@@17 T@U) (T@@31 T@T) ) (!  (and (= (= (|MultiSet#Card| T@@31 s@@17) 0) (= s@@17 (|MultiSet#Empty| T@@31))) (=> (or (not (= (|MultiSet#Card| T@@31 s@@17) 0)) (not true)) (exists ((x@@10 T@U) ) (! (< 0 (U_2_int (MapType0Select T@@31 intType s@@17 x@@10)))
 :qid |DafnyPreludebpl.845:38|
 :skolemid |187|
))))
 :qid |DafnyPreludebpl.843:18|
 :skolemid |188|
 :pattern ( (|MultiSet#Card| T@@31 s@@17))
)))
(assert (forall ((a@@16 T@U) (b@@13 T@U) (y T@U) (T@@32 T@T) ) (!  (=> (<= (U_2_int (MapType0Select T@@32 intType a@@16 y)) (U_2_int (MapType0Select T@@32 intType b@@13 y))) (= (U_2_int (MapType0Select T@@32 intType (|MultiSet#Difference| T@@32 a@@16 b@@13) y)) 0))
 :qid |DafnyPreludebpl.890:18|
 :skolemid |202|
 :pattern ( (|MultiSet#Difference| T@@32 a@@16 b@@13) (MapType0Select T@@32 intType b@@13 y) (MapType0Select T@@32 intType a@@16 y))
)))
(assert (forall ((u@@3 T@U) (U@@8 T@T) (V@@8 T@T) ) (!  (not (U_2_bool (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3)))
 :qid |DafnyPreludebpl.1250:21|
 :skolemid |288|
 :pattern ( (MapType0Select U@@8 boolType (|Map#Domain| U@@8 V@@8 (|Map#Empty| U@@8 V@@8)) u@@3))
)))
(assert (forall ((u@@4 T@U) (U@@9 T@T) (V@@9 T@T) ) (!  (not (U_2_bool (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4)))
 :qid |DafnyPreludebpl.1385:21|
 :skolemid |318|
 :pattern ( (MapType0Select U@@9 boolType (|IMap#Domain| U@@9 V@@9 (|IMap#Empty| U@@9 V@@9)) u@@4))
)))
(assert (forall ((h@@5 T@U) (k@@2 T@U) ) (!  (=> ($HeapSuccGhost h@@5 k@@2) (and ($HeapSucc h@@5 k@@2) (forall ((o@@6 T@U) (f@@1 T@U) (alpha T@T) ) (!  (=> (not ($IsGhostField alpha f@@1)) (= ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) h@@5 o@@6) f@@1)) ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@6) f@@1))))
 :qid |DafnyPreludebpl.542:20|
 :skolemid |107|
 :pattern ( ($Unbox alpha (MapType1Select alpha BoxType (MapType0Select refType (MapType1Type BoxType) k@@2 o@@6) f@@1)))
))))
 :qid |DafnyPreludebpl.539:15|
 :skolemid |108|
 :pattern ( ($HeapSuccGhost h@@5 k@@2))
)))
(assert (forall ((o@@7 T@U) (p@@0 T@U) ) (!  (=> (and (|ORD#IsNat| p@@0) (<= (|ORD#Offset| p@@0) (|ORD#Offset| o@@7))) (and (= (|ORD#IsNat| (|ORD#Minus| o@@7 p@@0)) (|ORD#IsNat| o@@7)) (= (|ORD#Offset| (|ORD#Minus| o@@7 p@@0)) (- (|ORD#Offset| o@@7) (|ORD#Offset| p@@0)))))
 :qid |DafnyPreludebpl.449:15|
 :skolemid |94|
 :pattern ( (|ORD#Minus| o@@7 p@@0))
)))
(assert (forall ((a@@17 T@U) (b@@14 T@U) (T@@33 T@T) ) (! (= (|Set#Equal| T@@33 a@@17 b@@14) (forall ((o@@8 T@U) ) (! (= (U_2_bool (MapType0Select T@@33 boolType a@@17 o@@8)) (U_2_bool (MapType0Select T@@33 boolType b@@14 o@@8)))
 :qid |DafnyPreludebpl.740:31|
 :skolemid |150|
 :pattern ( (MapType0Select T@@33 boolType a@@17 o@@8))
 :pattern ( (MapType0Select T@@33 boolType b@@14 o@@8))
)))
 :qid |DafnyPreludebpl.739:18|
 :skolemid |151|
 :pattern ( (|Set#Equal| T@@33 a@@17 b@@14))
)))
(assert (forall ((a@@18 T@U) (b@@15 T@U) (T@@34 T@T) ) (! (= (|ISet#Equal| T@@34 a@@18 b@@15) (forall ((o@@9 T@U) ) (! (= (U_2_bool (MapType0Select T@@34 boolType a@@18 o@@9)) (U_2_bool (MapType0Select T@@34 boolType b@@15 o@@9)))
 :qid |DafnyPreludebpl.807:32|
 :skolemid |172|
 :pattern ( (MapType0Select T@@34 boolType a@@18 o@@9))
 :pattern ( (MapType0Select T@@34 boolType b@@15 o@@9))
)))
 :qid |DafnyPreludebpl.806:18|
 :skolemid |173|
 :pattern ( (|ISet#Equal| T@@34 a@@18 b@@15))
)))
(assert (forall ((a@@19 T@U) (b@@16 T@U) (T@@35 T@T) ) (! (= (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@19 b@@16)) (+ (|MultiSet#Card| T@@35 a@@19) (|MultiSet#Card| T@@35 b@@16)))
 :qid |DafnyPreludebpl.873:18|
 :skolemid |197|
 :pattern ( (|MultiSet#Card| T@@35 (|MultiSet#Union| T@@35 a@@19 b@@16)))
)))
(assert (forall ((s0@@2 T@U) (s1@@0 T@U) (T@@36 T@T) ) (! (= (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)) (+ (|Seq#Length| T@@36 s0@@2) (|Seq#Length| T@@36 s1@@0)))
 :qid |DafnyPreludebpl.1012:18|
 :skolemid |231|
 :pattern ( (|Seq#Length| T@@36 (|Seq#Append| T@@36 s0@@2 s1@@0)))
)))
(assert (forall ((n@@8 Int) ) (!  (=> (<= 0 n@@8) (and (|ORD#IsNat| (|ORD#FromNat| n@@8)) (= (|ORD#Offset| (|ORD#FromNat| n@@8)) n@@8)))
 :qid |DafnyPreludebpl.410:15|
 :skolemid |85|
 :pattern ( (|ORD#FromNat| n@@8))
)))
(assert (forall ((ms T@U) (T@@37 T@T) ) (! (= ($IsGoodMultiSet T@@37 ms) (forall ((bx@@4 T@U) ) (!  (and (<= 0 (U_2_int (MapType0Select T@@37 intType ms bx@@4))) (<= (U_2_int (MapType0Select T@@37 intType ms bx@@4)) (|MultiSet#Card| T@@37 ms)))
 :qid |DafnyPreludebpl.834:11|
 :skolemid |182|
 :pattern ( (MapType0Select T@@37 intType ms bx@@4))
)))
 :qid |DafnyPreludebpl.832:18|
 :skolemid |183|
 :pattern ( ($IsGoodMultiSet T@@37 ms))
)))
(assert (forall ((o@@10 T@U) (p@@1 T@U) ) (!  (and (or (= o@@10 (|ORD#Plus| o@@10 p@@1)) (|ORD#Less| o@@10 (|ORD#Plus| o@@10 p@@1))) (or (= p@@1 (|ORD#Plus| o@@10 p@@1)) (|ORD#Less| p@@1 (|ORD#Plus| o@@10 p@@1))))
 :qid |DafnyPreludebpl.441:15|
 :skolemid |92|
 :pattern ( (|ORD#Plus| o@@10 p@@1))
)))
(assert (forall ((a@@20 T@U) (x@@11 T@U) (T@@38 T@T) ) (! (= (U_2_int (MapType0Select T@@38 intType (|MultiSet#UnionOne| T@@38 a@@20 x@@11) x@@11)) (+ (U_2_int (MapType0Select T@@38 intType a@@20 x@@11)) 1))
 :qid |DafnyPreludebpl.857:18|
 :skolemid |192|
 :pattern ( (|MultiSet#UnionOne| T@@38 a@@20 x@@11))
)))
(assert (forall ((s@@18 T@U) (i@@6 Int) (v@@13 T@U) (T@@39 T@T) ) (!  (and (=> (= i@@6 (|Seq#Length| T@@39 s@@18)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) v@@13)) (=> (or (not (= i@@6 (|Seq#Length| T@@39 s@@18))) (not true)) (= (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6) (|Seq#Index| T@@39 s@@18 i@@6))))
 :qid |DafnyPreludebpl.993:18|
 :skolemid |227|
 :pattern ( (|Seq#Index| T@@39 (|Seq#Build| T@@39 s@@18 v@@13) i@@6))
)))
(assert (forall ((a@@21 T@U) (b@@17 T@U) ) (! (= (|char#Minus| a@@21 b@@17) (|char#FromInt| (- (|char#ToInt| a@@21) (|char#ToInt| b@@17))))
 :qid |DafnyPreludebpl.147:15|
 :skolemid |24|
 :pattern ( (|char#Minus| a@@21 b@@17))
)))
(assert (forall ((a@@22 T@U) (b@@18 T@U) ) (! (= (|char#Plus| a@@22 b@@18) (|char#FromInt| (+ (|char#ToInt| a@@22) (|char#ToInt| b@@18))))
 :qid |DafnyPreludebpl.142:15|
 :skolemid |23|
 :pattern ( (|char#Plus| a@@22 b@@18))
)))
(assert (forall ((a@@23 T@U) (x@@12 T@U) (y@@0 T@U) (T@@40 T@T) ) (!  (=> (< 0 (U_2_int (MapType0Select T@@40 intType a@@23 y@@0))) (< 0 (U_2_int (MapType0Select T@@40 intType (|MultiSet#UnionOne| T@@40 a@@23 x@@12) y@@0))))
 :qid |DafnyPreludebpl.860:18|
 :skolemid |193|
 :pattern ( (|MultiSet#UnionOne| T@@40 a@@23 x@@12) (MapType0Select T@@40 intType a@@23 y@@0))
)))
(assert (forall ((m@@10 T@U) (U@@10 T@T) (V@@10 T@T) ) (!  (or (= m@@10 (|Map#Empty| U@@10 V@@10)) (exists ((k@@3 T@U) ) (! (U_2_bool (MapType0Select U@@10 boolType (|Map#Domain| U@@10 V@@10 m@@10) k@@3))
 :qid |DafnyPreludebpl.1196:31|
 :skolemid |276|
)))
 :qid |DafnyPreludebpl.1194:21|
 :skolemid |277|
 :pattern ( (|Map#Domain| U@@10 V@@10 m@@10))
)))
(assert (forall ((m@@11 T@U) (U@@11 T@T) (V@@11 T@T) ) (!  (or (= m@@11 (|Map#Empty| U@@11 V@@11)) (exists ((v@@14 T@U) ) (! (U_2_bool (MapType0Select V@@11 boolType (|Map#Values| U@@11 V@@11 m@@11) v@@14))
 :qid |DafnyPreludebpl.1199:31|
 :skolemid |278|
)))
 :qid |DafnyPreludebpl.1197:21|
 :skolemid |279|
 :pattern ( (|Map#Values| U@@11 V@@11 m@@11))
)))
(assert (forall ((m@@12 T@U) (U@@12 T@T) (V@@12 T@T) ) (!  (or (= m@@12 (|IMap#Empty| U@@12 V@@12)) (exists ((k@@4 T@U) ) (! (U_2_bool (MapType0Select U@@12 boolType (|IMap#Domain| U@@12 V@@12 m@@12) k@@4))
 :qid |DafnyPreludebpl.1336:32|
 :skolemid |306|
)))
 :qid |DafnyPreludebpl.1334:21|
 :skolemid |307|
 :pattern ( (|IMap#Domain| U@@12 V@@12 m@@12))
)))
(assert (forall ((m@@13 T@U) (U@@13 T@T) (V@@13 T@T) ) (!  (or (= m@@13 (|IMap#Empty| U@@13 V@@13)) (exists ((v@@15 T@U) ) (! (U_2_bool (MapType0Select V@@13 boolType (|IMap#Values| U@@13 V@@13 m@@13) v@@15))
 :qid |DafnyPreludebpl.1339:32|
 :skolemid |308|
)))
 :qid |DafnyPreludebpl.1337:21|
 :skolemid |309|
 :pattern ( (|IMap#Values| U@@13 V@@13 m@@13))
)))
(assert (forall ((a@@24 T@U) (x@@13 T@U) (o@@11 T@U) (T@@41 T@T) ) (! (= (< 0 (U_2_int (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@24 x@@13) o@@11)))  (or (= o@@11 x@@13) (< 0 (U_2_int (MapType0Select T@@41 intType a@@24 o@@11)))))
 :qid |DafnyPreludebpl.854:18|
 :skolemid |191|
 :pattern ( (MapType0Select T@@41 intType (|MultiSet#UnionOne| T@@41 a@@24 x@@13) o@@11))
)))
(assert (forall ((h@@6 T@U) (a@@25 T@U) ) (! (forall ((i@@7 Int) ) (!  (=> (and (<= 0 i@@7) (< i@@7 (|Seq#Length| BoxType (|Seq#FromArray| h@@6 a@@25)))) (= (|Seq#Index| BoxType (|Seq#FromArray| h@@6 a@@25) i@@7) ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@6 a@@25) (IndexField i@@7)))))
 :qid |DafnyPreludebpl.1110:11|
 :skolemid |257|
 :pattern ( ($Unbox BoxType (MapType1Select BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@6 a@@25) (IndexField i@@7))))
 :pattern ( (|Seq#Index| BoxType (|Seq#FromArray| h@@6 a@@25) i@@7))
))
 :qid |DafnyPreludebpl.1108:15|
 :skolemid |258|
 :pattern ( (|Seq#FromArray| h@@6 a@@25))
)))
(assert (forall ((v@@16 T@U) (t0@@6 T@U) ) (! (= ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@6)) (forall ((bx@@5 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@16 bx@@5))) ($IsBox BoxType bx@@5 t0@@6))
 :qid |DafnyPreludebpl.246:11|
 :skolemid |49|
 :pattern ( (MapType0Select BoxType intType v@@16 bx@@5))
)))
 :qid |DafnyPreludebpl.244:15|
 :skolemid |50|
 :pattern ( ($Is (MapType0Type BoxType intType) v@@16 (TMultiSet t0@@6)))
)))
(assert (forall ((s0@@3 T@U) (s1@@1 T@U) (x@@14 T@U) (T@@42 T@T) ) (! (= (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14)  (or (|Seq#Contains| T@@42 s0@@3 x@@14) (|Seq#Contains| T@@42 s1@@1 x@@14)))
 :qid |DafnyPreludebpl.1037:18|
 :skolemid |239|
 :pattern ( (|Seq#Contains| T@@42 (|Seq#Append| T@@42 s0@@3 s1@@1) x@@14))
)))
(assert (forall ((s@@19 T@U) (n@@9 Int) (x@@15 T@U) (T@@43 T@T) ) (! (= (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15) (exists ((i@@8 Int) ) (!  (and (and (and (<= 0 i@@8) (< i@@8 n@@9)) (< i@@8 (|Seq#Length| T@@43 s@@19))) (= (|Seq#Index| T@@43 s@@19 i@@8) x@@15))
 :qid |DafnyPreludebpl.1049:13|
 :skolemid |241|
 :pattern ( (|Seq#Index| T@@43 s@@19 i@@8))
)))
 :qid |DafnyPreludebpl.1046:18|
 :skolemid |242|
 :pattern ( (|Seq#Contains| T@@43 (|Seq#Take| T@@43 s@@19 n@@9) x@@15))
)))
(assert (forall ((a@@26 T@U) (b@@19 T@U) (T@@44 T@T) ) (!  (=> (|Set#Disjoint| T@@44 a@@26 b@@19) (and (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@26 b@@19) a@@26) b@@19) (= (|Set#Difference| T@@44 (|Set#Union| T@@44 a@@26 b@@19) b@@19) a@@26)))
 :qid |DafnyPreludebpl.694:18|
 :skolemid |138|
 :pattern ( (|Set#Union| T@@44 a@@26 b@@19))
)))
(assert (forall ((a@@27 T@U) (b@@20 T@U) (T@@45 T@T) ) (!  (=> (|ISet#Disjoint| T@@45 a@@27 b@@20) (and (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@27 b@@20) a@@27) b@@20) (= (|ISet#Difference| T@@45 (|ISet#Union| T@@45 a@@27 b@@20) b@@20) a@@27)))
 :qid |DafnyPreludebpl.776:18|
 :skolemid |162|
 :pattern ( (|ISet#Union| T@@45 a@@27 b@@20))
)))
(assert (forall ((a@@28 T@U) (b@@21 T@U) (T@@46 T@T) ) (! (= (|MultiSet#Equal| T@@46 a@@28 b@@21) (forall ((o@@12 T@U) ) (! (= (U_2_int (MapType0Select T@@46 intType a@@28 o@@12)) (U_2_int (MapType0Select T@@46 intType b@@21 o@@12)))
 :qid |DafnyPreludebpl.906:36|
 :skolemid |206|
 :pattern ( (MapType0Select T@@46 intType a@@28 o@@12))
 :pattern ( (MapType0Select T@@46 intType b@@21 o@@12))
)))
 :qid |DafnyPreludebpl.905:18|
 :skolemid |207|
 :pattern ( (|MultiSet#Equal| T@@46 a@@28 b@@21))
)))
(assert (forall ((a@@29 T@U) (b@@22 T@U) (T@@47 T@T) ) (! (= (|MultiSet#Subset| T@@47 a@@29 b@@22) (forall ((o@@13 T@U) ) (! (<= (U_2_int (MapType0Select T@@47 intType a@@29 o@@13)) (U_2_int (MapType0Select T@@47 intType b@@22 o@@13)))
 :qid |DafnyPreludebpl.902:37|
 :skolemid |204|
 :pattern ( (MapType0Select T@@47 intType a@@29 o@@13))
 :pattern ( (MapType0Select T@@47 intType b@@22 o@@13))
)))
 :qid |DafnyPreludebpl.901:18|
 :skolemid |205|
 :pattern ( (|MultiSet#Subset| T@@47 a@@29 b@@22))
)))
(assert (forall ((m@@14 T@U) (U@@14 T@T) (V@@14 T@T) ) (! (= (= (|Map#Card| U@@14 V@@14 m@@14) 0) (= m@@14 (|Map#Empty| U@@14 V@@14)))
 :qid |DafnyPreludebpl.1190:21|
 :skolemid |275|
 :pattern ( (|Map#Card| U@@14 V@@14 m@@14))
)))
(assert (forall ((s@@20 T@U) (x@@16 T@U) (T@@48 T@T) ) (! (= (|Seq#Contains| T@@48 s@@20 x@@16) (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| T@@48 s@@20))) (= (|Seq#Index| T@@48 s@@20 i@@9) x@@16))
 :qid |DafnyPreludebpl.1032:13|
 :skolemid |236|
 :pattern ( (|Seq#Index| T@@48 s@@20 i@@9))
)))
 :qid |DafnyPreludebpl.1030:18|
 :skolemid |237|
 :pattern ( (|Seq#Contains| T@@48 s@@20 x@@16))
)))
(assert (forall ((s@@21 T@U) (i@@10 Int) (v@@17 T@U) (n@@10 Int) (T@@49 T@T) ) (!  (=> (and (and (<= 0 i@@10) (< i@@10 n@@10)) (<= n@@10 (|Seq#Length| T@@49 s@@21))) (= (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10) (|Seq#Drop| T@@49 s@@21 n@@10)))
 :qid |DafnyPreludebpl.1139:18|
 :skolemid |264|
 :pattern ( (|Seq#Drop| T@@49 (|Seq#Update| T@@49 s@@21 i@@10 v@@17) n@@10))
)))
(assert (forall ((a@@30 T@U) (b@@23 T@U) (o@@14 T@U) (T@@50 T@T) ) (! (= (U_2_bool (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@30 b@@23) o@@14))  (and (U_2_bool (MapType0Select T@@50 boolType a@@30 o@@14)) (U_2_bool (MapType0Select T@@50 boolType b@@23 o@@14))))
 :qid |DafnyPreludebpl.704:18|
 :skolemid |139|
 :pattern ( (MapType0Select T@@50 boolType (|Set#Intersection| T@@50 a@@30 b@@23) o@@14))
)))
(assert (forall ((a@@31 T@U) (b@@24 T@U) (o@@15 T@U) (T@@51 T@T) ) (! (= (U_2_bool (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@31 b@@24) o@@15))  (and (U_2_bool (MapType0Select T@@51 boolType a@@31 o@@15)) (U_2_bool (MapType0Select T@@51 boolType b@@24 o@@15))))
 :qid |DafnyPreludebpl.782:18|
 :skolemid |163|
 :pattern ( (MapType0Select T@@51 boolType (|ISet#Intersection| T@@51 a@@31 b@@24) o@@15))
)))
(assert (forall ((o@@16 T@U) (p@@2 T@U) ) (!  (or (or (|ORD#Less| o@@16 p@@2) (= o@@16 p@@2)) (|ORD#Less| p@@2 o@@16))
 :qid |DafnyPreludebpl.422:15|
 :skolemid |88|
 :pattern ( (|ORD#Less| o@@16 p@@2) (|ORD#Less| p@@2 o@@16))
)))
(assert (forall ((a@@32 T@U) (b@@25 T@U) (o@@17 T@U) (T@@52 T@T) ) (! (= (U_2_bool (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@32 b@@25) o@@17))  (and (U_2_bool (MapType0Select T@@52 boolType a@@32 o@@17)) (not (U_2_bool (MapType0Select T@@52 boolType b@@25 o@@17)))))
 :qid |DafnyPreludebpl.719:18|
 :skolemid |145|
 :pattern ( (MapType0Select T@@52 boolType (|Set#Difference| T@@52 a@@32 b@@25) o@@17))
)))
(assert (forall ((a@@33 T@U) (b@@26 T@U) (o@@18 T@U) (T@@53 T@T) ) (! (= (U_2_bool (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@33 b@@26) o@@18))  (and (U_2_bool (MapType0Select T@@53 boolType a@@33 o@@18)) (not (U_2_bool (MapType0Select T@@53 boolType b@@26 o@@18)))))
 :qid |DafnyPreludebpl.796:18|
 :skolemid |168|
 :pattern ( (MapType0Select T@@53 boolType (|ISet#Difference| T@@53 a@@33 b@@26) o@@18))
)))
(assert (forall ((v@@18 T@U) (t0@@7 T@U) (h@@7 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@7) h@@7) (forall ((bx@@6 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@18 bx@@6)) ($IsAllocBox BoxType bx@@6 t0@@7 h@@7))
 :qid |DafnyPreludebpl.297:11|
 :skolemid |66|
 :pattern ( (MapType0Select BoxType boolType v@@18 bx@@6))
)))
 :qid |DafnyPreludebpl.295:15|
 :skolemid |67|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@18 (TSet t0@@7) h@@7))
)))
(assert (forall ((v@@19 T@U) (t0@@8 T@U) (h@@8 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@8) h@@8) (forall ((bx@@7 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType v@@19 bx@@7)) ($IsAllocBox BoxType bx@@7 t0@@8 h@@8))
 :qid |DafnyPreludebpl.301:11|
 :skolemid |68|
 :pattern ( (MapType0Select BoxType boolType v@@19 bx@@7))
)))
 :qid |DafnyPreludebpl.299:15|
 :skolemid |69|
 :pattern ( ($IsAlloc (MapType0Type BoxType boolType) v@@19 (TISet t0@@8) h@@8))
)))
(assert (forall ((o@@19 T@U) (T@@54 T@T) ) (! (= (U_2_int (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@19)) 0)
 :qid |DafnyPreludebpl.842:18|
 :skolemid |186|
 :pattern ( (MapType0Select T@@54 intType (|MultiSet#Empty| T@@54) o@@19))
)))
(assert (= (Ctor DatatypeTypeType) 9))
(assert (forall ((m@@15 T@U) (item T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@15) item))  (and (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item)))))
 :qid |DafnyPreludebpl.1242:15|
 :skolemid |287|
 :pattern ( (MapType0Select BoxType boolType (|Map#Items| BoxType BoxType m@@15) item))
)))
(assert (forall ((m@@16 T@U) (item@@0 T@U) ) (! (= (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@16) item@@0))  (and (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType m@@16) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType m@@16) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))))
 :qid |DafnyPreludebpl.1378:15|
 :skolemid |317|
 :pattern ( (MapType0Select BoxType boolType (|IMap#Items| BoxType BoxType m@@16) item@@0))
)))
(assert (forall ((m@@17 T@U) (v@@20 T@U) (U@@15 T@T) (V@@15 T@T) ) (! (= (U_2_bool (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@17) v@@20)) (exists ((u@@5 T@U) ) (!  (and (U_2_bool (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@17) u@@5)) (= v@@20 (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@17) u@@5)))
 :qid |DafnyPreludebpl.1223:10|
 :skolemid |285|
 :pattern ( (MapType0Select U@@15 boolType (|Map#Domain| U@@15 V@@15 m@@17) u@@5))
 :pattern ( (MapType0Select U@@15 V@@15 (|Map#Elements| U@@15 V@@15 m@@17) u@@5))
)))
 :qid |DafnyPreludebpl.1221:20|
 :skolemid |286|
 :pattern ( (MapType0Select V@@15 boolType (|Map#Values| U@@15 V@@15 m@@17) v@@20))
)))
(assert (forall ((m@@18 T@U) (v@@21 T@U) (U@@16 T@T) (V@@16 T@T) ) (! (= (U_2_bool (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@18) v@@21)) (exists ((u@@6 T@U) ) (!  (and (U_2_bool (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@18) u@@6)) (= v@@21 (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@18) u@@6)))
 :qid |DafnyPreludebpl.1363:10|
 :skolemid |315|
 :pattern ( (MapType0Select U@@16 boolType (|IMap#Domain| U@@16 V@@16 m@@18) u@@6))
 :pattern ( (MapType0Select U@@16 V@@16 (|IMap#Elements| U@@16 V@@16 m@@18) u@@6))
)))
 :qid |DafnyPreludebpl.1361:20|
 :skolemid |316|
 :pattern ( (MapType0Select V@@16 boolType (|IMap#Values| U@@16 V@@16 m@@18) v@@21))
)))
(assert  (and (and (forall ((arg0@@9 T@T) (arg1@@2 T@T) ) (! (= (Ctor (MapType arg0@@9 arg1@@2)) 10)
 :qid |ctor:MapType|
)) (forall ((arg0@@10 T@T) (arg1@@3 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@10 arg1@@3)) arg0@@10)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@10 arg1@@3))
))) (forall ((arg0@@11 T@T) (arg1@@4 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@11 arg1@@4)) arg1@@4)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@11 arg1@@4))
))))
(assert (forall ((v@@22 T@U) (t0@@9 T@U) (t1@@1 T@U) (h@@9 T@U) ) (! (= ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@9 t1@@1) h@@9) (forall ((bx@@8 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@8)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@8) t1@@1 h@@9) ($IsAllocBox BoxType bx@@8 t0@@9 h@@9)))
 :qid |DafnyPreludebpl.316:19|
 :skolemid |74|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@22) bx@@8))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@22) bx@@8))
)))
 :qid |DafnyPreludebpl.313:15|
 :skolemid |75|
 :pattern ( ($IsAlloc (MapType BoxType BoxType) v@@22 (TMap t0@@9 t1@@1) h@@9))
)))
(assert  (and (and (forall ((arg0@@12 T@T) (arg1@@5 T@T) ) (! (= (Ctor (IMapType arg0@@12 arg1@@5)) 11)
 :qid |ctor:IMapType|
)) (forall ((arg0@@13 T@T) (arg1@@6 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@13 arg1@@6)) arg0@@13)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@13 arg1@@6))
))) (forall ((arg0@@14 T@T) (arg1@@7 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@14 arg1@@7)) arg1@@7)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@14 arg1@@7))
))))
(assert (forall ((v@@23 T@U) (t0@@10 T@U) (t1@@2 T@U) (h@@10 T@U) ) (! (= ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@10 t1@@2) h@@10) (forall ((bx@@9 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@9)) (and ($IsAllocBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@9) t1@@2 h@@10) ($IsAllocBox BoxType bx@@9 t0@@10 h@@10)))
 :qid |DafnyPreludebpl.325:19|
 :skolemid |76|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@23) bx@@9))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@23) bx@@9))
)))
 :qid |DafnyPreludebpl.322:15|
 :skolemid |77|
 :pattern ( ($IsAlloc (IMapType BoxType BoxType) v@@23 (TIMap t0@@10 t1@@2) h@@10))
)))
(assert (forall ((o@@20 T@U) (p@@3 T@U) ) (!  (and (=> (= o@@20 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@20 p@@3) p@@3)) (=> (= p@@3 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@20 p@@3) o@@20)))
 :qid |DafnyPreludebpl.444:15|
 :skolemid |93|
 :pattern ( (|ORD#Plus| o@@20 p@@3))
)))
(assert (forall ((x@@17 Int) (y@@1 Int) ) (! (= (INTERNAL_div_boogie x@@17 y@@1) (div x@@17 y@@1))
 :qid |DafnyPreludebpl.1454:30|
 :skolemid |335|
 :pattern ( (INTERNAL_div_boogie x@@17 y@@1))
)))
(assert (forall ((x@@18 Int) (y@@2 Int) ) (! (= (Div x@@18 y@@2) (div x@@18 y@@2))
 :qid |DafnyPreludebpl.1462:14|
 :skolemid |342|
 :pattern ( (Div x@@18 y@@2))
)))
(assert (forall ((o@@21 T@U) (p@@4 T@U) ) (! (= (|ORD#LessThanLimit| o@@21 p@@4) (|ORD#Less| o@@21 p@@4))
 :qid |DafnyPreludebpl.432:15|
 :skolemid |90|
 :pattern ( (|ORD#LessThanLimit| o@@21 p@@4))
)))
(assert (forall ((a@@34 T@U) (b@@27 T@U) (T@@55 T@T) ) (!  (=> (|Set#Equal| T@@55 a@@34 b@@27) (= a@@34 b@@27))
 :qid |DafnyPreludebpl.741:18|
 :skolemid |152|
 :pattern ( (|Set#Equal| T@@55 a@@34 b@@27))
)))
(assert (forall ((a@@35 T@U) (b@@28 T@U) (T@@56 T@T) ) (!  (=> (|ISet#Equal| T@@56 a@@35 b@@28) (= a@@35 b@@28))
 :qid |DafnyPreludebpl.808:18|
 :skolemid |174|
 :pattern ( (|ISet#Equal| T@@56 a@@35 b@@28))
)))
(assert (forall ((a@@36 T@U) (b@@29 T@U) (T@@57 T@T) ) (!  (=> (|MultiSet#Equal| T@@57 a@@36 b@@29) (= a@@36 b@@29))
 :qid |DafnyPreludebpl.908:18|
 :skolemid |208|
 :pattern ( (|MultiSet#Equal| T@@57 a@@36 b@@29))
)))
(assert (forall ((a@@37 T@U) (b@@30 T@U) (T@@58 T@T) ) (!  (=> (|Seq#Equal| T@@58 a@@37 b@@30) (= a@@37 b@@30))
 :qid |DafnyPreludebpl.1063:18|
 :skolemid |247|
 :pattern ( (|Seq#Equal| T@@58 a@@37 b@@30))
)))
(assert (forall ((m@@19 T@U) (|m'@@0| T@U) (U@@17 T@T) (V@@17 T@T) ) (!  (=> (|Map#Equal| U@@17 V@@17 m@@19 |m'@@0|) (= m@@19 |m'@@0|))
 :qid |DafnyPreludebpl.1313:21|
 :skolemid |303|
 :pattern ( (|Map#Equal| U@@17 V@@17 m@@19 |m'@@0|))
)))
(assert (forall ((m@@20 T@U) (|m'@@1| T@U) (U@@18 T@T) (V@@18 T@T) ) (!  (=> (|IMap#Equal| U@@18 V@@18 m@@20 |m'@@1|) (= m@@20 |m'@@1|))
 :qid |DafnyPreludebpl.1423:21|
 :skolemid |327|
 :pattern ( (|IMap#Equal| U@@18 V@@18 m@@20 |m'@@1|))
)))
(assert (forall ((a@@38 T@U) (x@@19 T@U) (y@@3 T@U) (T@@59 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@59 boolType a@@38 y@@3)) (U_2_bool (MapType0Select T@@59 boolType (|Set#UnionOne| T@@59 a@@38 x@@19) y@@3)))
 :qid |DafnyPreludebpl.680:18|
 :skolemid |132|
 :pattern ( (|Set#UnionOne| T@@59 a@@38 x@@19) (MapType0Select T@@59 boolType a@@38 y@@3))
)))
(assert (forall ((a@@39 T@U) (b@@31 T@U) (y@@4 T@U) (T@@60 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@60 boolType a@@39 y@@4)) (U_2_bool (MapType0Select T@@60 boolType (|Set#Union| T@@60 a@@39 b@@31) y@@4)))
 :qid |DafnyPreludebpl.690:18|
 :skolemid |136|
 :pattern ( (|Set#Union| T@@60 a@@39 b@@31) (MapType0Select T@@60 boolType a@@39 y@@4))
)))
(assert (forall ((a@@40 T@U) (b@@32 T@U) (y@@5 T@U) (T@@61 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@61 boolType b@@32 y@@5)) (U_2_bool (MapType0Select T@@61 boolType (|Set#Union| T@@61 a@@40 b@@32) y@@5)))
 :qid |DafnyPreludebpl.692:18|
 :skolemid |137|
 :pattern ( (|Set#Union| T@@61 a@@40 b@@32) (MapType0Select T@@61 boolType b@@32 y@@5))
)))
(assert (forall ((a@@41 T@U) (x@@20 T@U) (y@@6 T@U) (T@@62 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@62 boolType a@@41 y@@6)) (U_2_bool (MapType0Select T@@62 boolType (|ISet#UnionOne| T@@62 a@@41 x@@20) y@@6)))
 :qid |DafnyPreludebpl.766:18|
 :skolemid |158|
 :pattern ( (|ISet#UnionOne| T@@62 a@@41 x@@20) (MapType0Select T@@62 boolType a@@41 y@@6))
)))
(assert (forall ((a@@42 T@U) (b@@33 T@U) (y@@7 T@U) (T@@63 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@63 boolType a@@42 y@@7)) (U_2_bool (MapType0Select T@@63 boolType (|ISet#Union| T@@63 a@@42 b@@33) y@@7)))
 :qid |DafnyPreludebpl.772:18|
 :skolemid |160|
 :pattern ( (|ISet#Union| T@@63 a@@42 b@@33) (MapType0Select T@@63 boolType a@@42 y@@7))
)))
(assert (forall ((a@@43 T@U) (b@@34 T@U) (y@@8 T@U) (T@@64 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@64 boolType b@@34 y@@8)) (U_2_bool (MapType0Select T@@64 boolType (|ISet#Union| T@@64 a@@43 b@@34) y@@8)))
 :qid |DafnyPreludebpl.774:18|
 :skolemid |161|
 :pattern ( (|ISet#Union| T@@64 a@@43 b@@34) (MapType0Select T@@64 boolType b@@34 y@@8))
)))
(assert (forall ((x@@21 Int) ) (! (= (q@Real x@@21) (to_real x@@21))
 :qid |DafnyPreludebpl.577:15|
 :skolemid |113|
 :pattern ( (q@Real x@@21))
)))
(assert (forall ((a@@44 T@U) (x@@22 T@U) (o@@22 T@U) (T@@65 T@T) ) (! (= (U_2_bool (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@44 x@@22) o@@22))  (or (= o@@22 x@@22) (U_2_bool (MapType0Select T@@65 boolType a@@44 o@@22))))
 :qid |DafnyPreludebpl.676:18|
 :skolemid |130|
 :pattern ( (MapType0Select T@@65 boolType (|Set#UnionOne| T@@65 a@@44 x@@22) o@@22))
)))
(assert (forall ((a@@45 T@U) (x@@23 T@U) (o@@23 T@U) (T@@66 T@T) ) (! (= (U_2_bool (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@45 x@@23) o@@23))  (or (= o@@23 x@@23) (U_2_bool (MapType0Select T@@66 boolType a@@45 o@@23))))
 :qid |DafnyPreludebpl.762:18|
 :skolemid |156|
 :pattern ( (MapType0Select T@@66 boolType (|ISet#UnionOne| T@@66 a@@45 x@@23) o@@23))
)))
(assert (forall ((s@@22 T@U) (n@@11 Int) (T@@67 T@T) ) (!  (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| T@@67 s@@22))) (= (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)) n@@11))
 :qid |DafnyPreludebpl.1073:18|
 :skolemid |250|
 :pattern ( (|Seq#Length| T@@67 (|Seq#Take| T@@67 s@@22 n@@11)))
)))
(assert (forall ((a@@46 T@U) (b@@35 T@U) (c T@U) ) (!  (=> (or (not (= a@@46 c)) (not true)) (=> (and ($HeapSucc a@@46 b@@35) ($HeapSucc b@@35 c)) ($HeapSucc a@@46 c)))
 :qid |DafnyPreludebpl.604:15|
 :skolemid |116|
 :pattern ( ($HeapSucc a@@46 b@@35) ($HeapSucc b@@35 c))
)))
(assert (forall ((a@@47 T@U) (b@@36 T@U) (y@@9 T@U) (T@@68 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@68 boolType b@@36 y@@9)) (not (U_2_bool (MapType0Select T@@68 boolType (|Set#Difference| T@@68 a@@47 b@@36) y@@9))))
 :qid |DafnyPreludebpl.721:18|
 :skolemid |146|
 :pattern ( (|Set#Difference| T@@68 a@@47 b@@36) (MapType0Select T@@68 boolType b@@36 y@@9))
)))
(assert (forall ((a@@48 T@U) (b@@37 T@U) (y@@10 T@U) (T@@69 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@69 boolType b@@37 y@@10)) (not (U_2_bool (MapType0Select T@@69 boolType (|ISet#Difference| T@@69 a@@48 b@@37) y@@10))))
 :qid |DafnyPreludebpl.798:18|
 :skolemid |169|
 :pattern ( (|ISet#Difference| T@@69 a@@48 b@@37) (MapType0Select T@@69 boolType b@@37 y@@10))
)))
(assert (forall ((m@@21 T@U) (U@@19 T@T) (V@@19 T@T) ) (! (= (= m@@21 (|IMap#Empty| U@@19 V@@19)) (= (|IMap#Domain| U@@19 V@@19 m@@21) (|ISet#Empty| U@@19)))
 :qid |DafnyPreludebpl.1344:21|
 :skolemid |312|
 :pattern ( (|IMap#Domain| U@@19 V@@19 m@@21))
)))
(assert (forall ((m@@22 T@U) (U@@20 T@T) (V@@20 T@T) ) (! (= (= m@@22 (|IMap#Empty| U@@20 V@@20)) (= (|IMap#Values| U@@20 V@@20 m@@22) (|ISet#Empty| V@@20)))
 :qid |DafnyPreludebpl.1347:21|
 :skolemid |313|
 :pattern ( (|IMap#Values| U@@20 V@@20 m@@22))
)))
(assert (forall ((m@@23 T@U) (U@@21 T@T) (V@@21 T@T) ) (! (= (= m@@23 (|IMap#Empty| U@@21 V@@21)) (= (|IMap#Items| U@@21 V@@21 m@@23) (|ISet#Empty| BoxType)))
 :qid |DafnyPreludebpl.1350:21|
 :skolemid |314|
 :pattern ( (|IMap#Items| U@@21 V@@21 m@@23))
)))
(assert (forall ((m@@24 T@U) (U@@22 T@T) (V@@22 T@T) ) (!  (or (= m@@24 (|Map#Empty| U@@22 V@@22)) (exists ((k@@5 T@U) (v@@24 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|Map#Items| U@@22 V@@22 m@@24) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@5 v@@24))))
 :qid |DafnyPreludebpl.1202:31|
 :skolemid |280|
)))
 :qid |DafnyPreludebpl.1200:21|
 :skolemid |281|
 :pattern ( (|Map#Items| U@@22 V@@22 m@@24))
)))
(assert (forall ((m@@25 T@U) (U@@23 T@T) (V@@23 T@T) ) (!  (or (= m@@25 (|IMap#Empty| U@@23 V@@23)) (exists ((k@@6 T@U) (v@@25 T@U) ) (! (U_2_bool (MapType0Select BoxType boolType (|IMap#Items| U@@23 V@@23 m@@25) ($Box DatatypeTypeType (|#_System._tuple#2._#Make2| k@@6 v@@25))))
 :qid |DafnyPreludebpl.1342:32|
 :skolemid |310|
)))
 :qid |DafnyPreludebpl.1340:21|
 :skolemid |311|
 :pattern ( (|IMap#Items| U@@23 V@@23 m@@25))
)))
(assert (forall ((cl T@U) (nm T@U) (T@@70 T@T) ) (!  (and (= (DeclType T@@70 (FieldOfDecl T@@70 cl nm)) cl) (= (DeclName T@@70 (FieldOfDecl T@@70 cl nm)) nm))
 :qid |DafnyPreludebpl.532:18|
 :skolemid |106|
 :pattern ( (FieldOfDecl T@@70 cl nm))
)))
(assert (forall ((bx@@10 T@U) ) (!  (=> ($IsBox BoxType bx@@10 TInt) (and (= ($Box intType ($Unbox intType bx@@10)) bx@@10) ($Is intType ($Unbox intType bx@@10) TInt)))
 :qid |DafnyPreludebpl.174:15|
 :skolemid |26|
 :pattern ( ($IsBox BoxType bx@@10 TInt))
)))
(assert (forall ((bx@@11 T@U) ) (!  (=> ($IsBox BoxType bx@@11 TReal) (and (= ($Box realType ($Unbox realType bx@@11)) bx@@11) ($Is realType ($Unbox realType bx@@11) TReal)))
 :qid |DafnyPreludebpl.177:15|
 :skolemid |27|
 :pattern ( ($IsBox BoxType bx@@11 TReal))
)))
(assert (forall ((bx@@12 T@U) ) (!  (=> ($IsBox BoxType bx@@12 TBool) (and (= ($Box boolType ($Unbox boolType bx@@12)) bx@@12) ($Is boolType ($Unbox boolType bx@@12) TBool)))
 :qid |DafnyPreludebpl.180:15|
 :skolemid |28|
 :pattern ( ($IsBox BoxType bx@@12 TBool))
)))
(assert (= (Ctor charType) 12))
(assert (forall ((bx@@13 T@U) ) (!  (=> ($IsBox BoxType bx@@13 TChar) (and (= ($Box charType ($Unbox charType bx@@13)) bx@@13) ($Is charType ($Unbox charType bx@@13) TChar)))
 :qid |DafnyPreludebpl.183:15|
 :skolemid |29|
 :pattern ( ($IsBox BoxType bx@@13 TChar))
)))
(assert (forall ((a@@49 T@U) (b@@38 T@U) (T@@71 T@T) ) (!  (and (= (+ (+ (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@49 b@@38)) (|Set#Card| T@@71 (|Set#Difference| T@@71 b@@38 a@@49))) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@49 b@@38))) (|Set#Card| T@@71 (|Set#Union| T@@71 a@@49 b@@38))) (= (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@49 b@@38)) (- (|Set#Card| T@@71 a@@49) (|Set#Card| T@@71 (|Set#Intersection| T@@71 a@@49 b@@38)))))
 :qid |DafnyPreludebpl.723:18|
 :skolemid |147|
 :pattern ( (|Set#Card| T@@71 (|Set#Difference| T@@71 a@@49 b@@38)))
)))
(assert (forall ((v@@26 T@U) (t@@8 T@U) (T@@72 T@T) ) (! (= ($IsBox BoxType ($Box T@@72 v@@26) t@@8) ($Is T@@72 v@@26 t@@8))
 :qid |DafnyPreludebpl.212:18|
 :skolemid |37|
 :pattern ( ($IsBox BoxType ($Box T@@72 v@@26) t@@8))
)))
(assert (forall ((s@@23 T@U) (a@@50 T@U) (T@@73 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@50)) 0)  (not (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@50)))) (= (= (U_2_int (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@50)) 1) (U_2_bool (MapType0Select T@@73 boolType s@@23 a@@50))))
 :qid |DafnyPreludebpl.917:18|
 :skolemid |211|
 :pattern ( (MapType0Select T@@73 intType (|MultiSet#FromSet| T@@73 s@@23) a@@50))
)))
(assert (forall ((t@@9 T@U) (T@@74 T@T) ) (! (= (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0) t@@9)
 :qid |DafnyPreludebpl.1016:18|
 :skolemid |232|
 :pattern ( (|Seq#Index| T@@74 (|Seq#Singleton| T@@74 t@@9) 0))
)))
(assert (forall ((s@@24 T@U) (i@@11 Int) (v@@27 T@U) (n@@12 Int) (T@@75 T@T) ) (!  (=> (and (<= n@@12 i@@11) (< i@@11 (|Seq#Length| T@@75 s@@24))) (= (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12) (|Seq#Take| T@@75 s@@24 n@@12)))
 :qid |DafnyPreludebpl.1133:18|
 :skolemid |262|
 :pattern ( (|Seq#Take| T@@75 (|Seq#Update| T@@75 s@@24 i@@11 v@@27) n@@12))
)))
(assert (forall ((r@@1 T@U) (o@@24 T@U) (T@@76 T@T) ) (!  (and (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@1) o@@24)) 1) (= r@@1 o@@24)) (= (= (U_2_int (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@1) o@@24)) 0)  (or (not (= r@@1 o@@24)) (not true))))
 :qid |DafnyPreludebpl.848:18|
 :skolemid |189|
 :pattern ( (MapType0Select T@@76 intType (|MultiSet#Singleton| T@@76 r@@1) o@@24))
)))
(assert (forall ((o@@25 T@U) ) (! (<= 0 (|ORD#Offset| o@@25))
 :qid |DafnyPreludebpl.404:15|
 :skolemid |84|
 :pattern ( (|ORD#Offset| o@@25))
)))
(assert (forall ((o@@26 T@U) ) (! (<= 0 (_System.array.Length o@@26))
 :qid |DafnyPreludebpl.569:15|
 :skolemid |111|
 :pattern ( (_System.array.Length o@@26))
)))
(assert (forall ((s@@25 T@U) (T@@77 T@T) ) (! (<= 0 (|Set#Card| T@@77 s@@25))
 :qid |DafnyPreludebpl.659:18|
 :skolemid |123|
 :pattern ( (|Set#Card| T@@77 s@@25))
)))
(assert (forall ((s@@26 T@U) (T@@78 T@T) ) (! (<= 0 (|MultiSet#Card| T@@78 s@@26))
 :qid |DafnyPreludebpl.837:18|
 :skolemid |184|
 :pattern ( (|MultiSet#Card| T@@78 s@@26))
)))
(assert (forall ((s@@27 T@U) (T@@79 T@T) ) (! (<= 0 (|Seq#Length| T@@79 s@@27))
 :qid |DafnyPreludebpl.962:18|
 :skolemid |221|
 :pattern ( (|Seq#Length| T@@79 s@@27))
)))
(assert (forall ((m@@26 T@U) (U@@24 T@T) (V@@24 T@T) ) (! (<= 0 (|Map#Card| U@@24 V@@24 m@@26))
 :qid |DafnyPreludebpl.1188:20|
 :skolemid |274|
 :pattern ( (|Map#Card| U@@24 V@@24 m@@26))
)))
(assert (forall ((ty@@0 T@U) ) (!  (=> ($AlwaysAllocated ty@@0) (forall ((h@@11 T@U) (v@@28 T@U) ) (!  (=> ($IsBox BoxType v@@28 ty@@0) ($IsAllocBox BoxType v@@28 ty@@0 h@@11))
 :qid |DafnyPreludebpl.335:13|
 :skolemid |78|
 :pattern ( ($IsAllocBox BoxType v@@28 ty@@0 h@@11))
)))
 :qid |DafnyPreludebpl.333:17|
 :skolemid |79|
 :pattern ( ($AlwaysAllocated ty@@0))
)))
(assert (forall ((s@@28 T@U) (i@@12 Int) (j@@2 Int) (T@@80 T@T) ) (!  (=> (and (and (<= 0 i@@12) (< i@@12 j@@2)) (<= j@@2 (|Seq#Length| T@@80 s@@28))) (< (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))) (|Seq#Rank| T@@80 s@@28)))
 :qid |DafnyPreludebpl.1161:18|
 :skolemid |270|
 :pattern ( (|Seq#Rank| T@@80 (|Seq#Append| T@@80 (|Seq#Take| T@@80 s@@28 i@@12) (|Seq#Drop| T@@80 s@@28 j@@2))))
)))
(assert (forall ((a@@51 T@U) (b@@39 T@U) (o@@27 T@U) (T@@81 T@T) ) (! (= (U_2_int (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@51 b@@39) o@@27)) (|Math#min| (U_2_int (MapType0Select T@@81 intType a@@51 o@@27)) (U_2_int (MapType0Select T@@81 intType b@@39 o@@27))))
 :qid |DafnyPreludebpl.877:18|
 :skolemid |198|
 :pattern ( (MapType0Select T@@81 intType (|MultiSet#Intersection| T@@81 a@@51 b@@39) o@@27))
)))
(assert (forall ((t@@10 T@U) (u@@7 T@U) ) (! (= (Inv0_TMap (TMap t@@10 u@@7)) t@@10)
 :qid |DafnyPreludebpl.57:15|
 :skolemid |9|
 :pattern ( (TMap t@@10 u@@7))
)))
(assert (forall ((t@@11 T@U) (u@@8 T@U) ) (! (= (Inv1_TMap (TMap t@@11 u@@8)) u@@8)
 :qid |DafnyPreludebpl.58:15|
 :skolemid |10|
 :pattern ( (TMap t@@11 u@@8))
)))
(assert (forall ((t@@12 T@U) (u@@9 T@U) ) (! (= (Tag (TMap t@@12 u@@9)) TagMap)
 :qid |DafnyPreludebpl.59:15|
 :skolemid |11|
 :pattern ( (TMap t@@12 u@@9))
)))
(assert (forall ((t@@13 T@U) (u@@10 T@U) ) (! (= (Inv0_TIMap (TIMap t@@13 u@@10)) t@@13)
 :qid |DafnyPreludebpl.62:15|
 :skolemid |12|
 :pattern ( (TIMap t@@13 u@@10))
)))
(assert (forall ((t@@14 T@U) (u@@11 T@U) ) (! (= (Inv1_TIMap (TIMap t@@14 u@@11)) u@@11)
 :qid |DafnyPreludebpl.63:15|
 :skolemid |13|
 :pattern ( (TIMap t@@14 u@@11))
)))
(assert (forall ((t@@15 T@U) (u@@12 T@U) ) (! (= (Tag (TIMap t@@15 u@@12)) TagIMap)
 :qid |DafnyPreludebpl.64:15|
 :skolemid |14|
 :pattern ( (TIMap t@@15 u@@12))
)))
(assert (forall ((v@@29 T@U) (t0@@11 T@U) (h@@12 T@U) ) (! (= ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@11) h@@12) (forall ((i@@13 Int) ) (!  (=> (and (<= 0 i@@13) (< i@@13 (|Seq#Length| BoxType v@@29))) ($IsAllocBox BoxType (|Seq#Index| BoxType v@@29 i@@13) t0@@11 h@@12))
 :qid |DafnyPreludebpl.309:11|
 :skolemid |72|
 :pattern ( (|Seq#Index| BoxType v@@29 i@@13))
)))
 :qid |DafnyPreludebpl.307:15|
 :skolemid |73|
 :pattern ( ($IsAlloc (SeqType BoxType) v@@29 (TSeq t0@@11) h@@12))
)))
(assert (forall ((a@@52 T@U) (x@@24 T@U) (T@@82 T@T) ) (! (U_2_bool (MapType0Select T@@82 boolType (|Set#UnionOne| T@@82 a@@52 x@@24) x@@24))
 :qid |DafnyPreludebpl.678:18|
 :skolemid |131|
 :pattern ( (|Set#UnionOne| T@@82 a@@52 x@@24))
)))
(assert (forall ((a@@53 T@U) (x@@25 T@U) (T@@83 T@T) ) (! (U_2_bool (MapType0Select T@@83 boolType (|ISet#UnionOne| T@@83 a@@53 x@@25) x@@25))
 :qid |DafnyPreludebpl.764:18|
 :skolemid |157|
 :pattern ( (|ISet#UnionOne| T@@83 a@@53 x@@25))
)))
(assert (forall ((a@@54 T@U) (x@@26 T@U) (T@@84 T@T) ) (!  (=> (U_2_bool (MapType0Select T@@84 boolType a@@54 x@@26)) (= (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@54 x@@26)) (|Set#Card| T@@84 a@@54)))
 :qid |DafnyPreludebpl.682:18|
 :skolemid |133|
 :pattern ( (|Set#Card| T@@84 (|Set#UnionOne| T@@84 a@@54 x@@26)))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |DafnyPreludebpl.38:15|
 :skolemid |0|
 :pattern ( (TBitvector w))
)))
(assert (forall ((t@@16 T@U) ) (! (= (Inv0_TSet (TSet t@@16)) t@@16)
 :qid |DafnyPreludebpl.41:15|
 :skolemid |1|
 :pattern ( (TSet t@@16))
)))
(assert (forall ((t@@17 T@U) ) (! (= (Tag (TSet t@@17)) TagSet)
 :qid |DafnyPreludebpl.42:15|
 :skolemid |2|
 :pattern ( (TSet t@@17))
)))
(assert (forall ((t@@18 T@U) ) (! (= (Inv0_TISet (TISet t@@18)) t@@18)
 :qid |DafnyPreludebpl.45:15|
 :skolemid |3|
 :pattern ( (TISet t@@18))
)))
(assert (forall ((t@@19 T@U) ) (! (= (Tag (TISet t@@19)) TagISet)
 :qid |DafnyPreludebpl.46:15|
 :skolemid |4|
 :pattern ( (TISet t@@19))
)))
(assert (forall ((t@@20 T@U) ) (! (= (Inv0_TMultiSet (TMultiSet t@@20)) t@@20)
 :qid |DafnyPreludebpl.49:15|
 :skolemid |5|
 :pattern ( (TMultiSet t@@20))
)))
(assert (forall ((t@@21 T@U) ) (! (= (Tag (TMultiSet t@@21)) TagMultiSet)
 :qid |DafnyPreludebpl.50:15|
 :skolemid |6|
 :pattern ( (TMultiSet t@@21))
)))
(assert (forall ((t@@22 T@U) ) (! (= (Inv0_TSeq (TSeq t@@22)) t@@22)
 :qid |DafnyPreludebpl.53:15|
 :skolemid |7|
 :pattern ( (TSeq t@@22))
)))
(assert (forall ((t@@23 T@U) ) (! (= (Tag (TSeq t@@23)) TagSeq)
 :qid |DafnyPreludebpl.54:15|
 :skolemid |8|
 :pattern ( (TSeq t@@23))
)))
(assert (forall ((i@@14 Int) ) (! (= (FDim BoxType (IndexField i@@14)) 1)
 :qid |DafnyPreludebpl.513:15|
 :skolemid |102|
 :pattern ( (IndexField i@@14))
)))
(assert (forall ((i@@15 Int) ) (! (= (IndexField_Inverse BoxType (IndexField i@@15)) i@@15)
 :qid |DafnyPreludebpl.515:15|
 :skolemid |103|
 :pattern ( (IndexField i@@15))
)))
(assert (forall ((i@@16 Int) ) (! (= (q@Int (q@Real i@@16)) i@@16)
 :qid |DafnyPreludebpl.578:15|
 :skolemid |114|
 :pattern ( (q@Int (q@Real i@@16)))
)))
(assert (forall ((x@@27 T@U) (T@@85 T@T) ) (! (= ($Unbox T@@85 ($Box T@@85 x@@27)) x@@27)
 :qid |DafnyPreludebpl.167:18|
 :skolemid |25|
 :pattern ( ($Box T@@85 x@@27))
)))
(assert (forall ((r@@2 T@U) (T@@86 T@T) ) (! (= (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@2)) 1)
 :qid |DafnyPreludebpl.673:18|
 :skolemid |129|
 :pattern ( (|Set#Card| T@@86 (|Set#Singleton| T@@86 r@@2)))
)))
(assert (forall ((t@@24 T@U) (T@@87 T@T) ) (! (= (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)) 1)
 :qid |DafnyPreludebpl.980:18|
 :skolemid |224|
 :pattern ( (|Seq#Length| T@@87 (|Seq#Singleton| T@@87 t@@24)))
)))
(assert (forall ((v@@30 T@U) (t0@@12 T@U) (t1@@3 T@U) ) (! (= ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@12 t1@@3)) (forall ((bx@@14 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@14)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@14) t1@@3) ($IsBox BoxType bx@@14 t0@@12)))
 :qid |DafnyPreludebpl.259:19|
 :skolemid |54|
 :pattern ( (MapType0Select BoxType BoxType (|Map#Elements| BoxType BoxType v@@30) bx@@14))
 :pattern ( (MapType0Select BoxType boolType (|Map#Domain| BoxType BoxType v@@30) bx@@14))
)))
 :qid |DafnyPreludebpl.256:15|
 :skolemid |55|
 :pattern ( ($Is (MapType BoxType BoxType) v@@30 (TMap t0@@12 t1@@3)))
)))
(assert (forall ((v@@31 T@U) (t0@@13 T@U) (t1@@4 T@U) ) (! (= ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@13 t1@@4)) (forall ((bx@@15 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@15)) (and ($IsBox BoxType (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@15) t1@@4) ($IsBox BoxType bx@@15 t0@@13)))
 :qid |DafnyPreludebpl.274:19|
 :skolemid |57|
 :pattern ( (MapType0Select BoxType BoxType (|IMap#Elements| BoxType BoxType v@@31) bx@@15))
 :pattern ( (MapType0Select BoxType boolType (|IMap#Domain| BoxType BoxType v@@31) bx@@15))
)))
 :qid |DafnyPreludebpl.271:15|
 :skolemid |58|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@31 (TIMap t0@@13 t1@@4)))
)))
(assert (forall ((o@@28 T@U) (p@@5 T@U) ) (!  (and (and (and (=> (|ORD#Less| o@@28 p@@5) (or (not (= o@@28 p@@5)) (not true))) (=> (and (|ORD#IsNat| o@@28) (not (|ORD#IsNat| p@@5))) (|ORD#Less| o@@28 p@@5))) (=> (and (|ORD#IsNat| o@@28) (|ORD#IsNat| p@@5)) (= (|ORD#Less| o@@28 p@@5) (< (|ORD#Offset| o@@28) (|ORD#Offset| p@@5))))) (=> (and (|ORD#Less| o@@28 p@@5) (|ORD#IsNat| p@@5)) (|ORD#IsNat| o@@28)))
 :qid |DafnyPreludebpl.416:15|
 :skolemid |87|
 :pattern ( (|ORD#Less| o@@28 p@@5))
)))
(assert (forall ((h@@13 T@U) (i@@17 Int) (v@@32 T@U) (a@@55 T@U) ) (!  (=> (and (<= 0 i@@17) (< i@@17 (_System.array.Length a@@55))) (= (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@13 a@@55 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@13 a@@55) (IndexField i@@17) ($Box BoxType v@@32))) a@@55) (|Seq#Update| BoxType (|Seq#FromArray| h@@13 a@@55) i@@17 v@@32)))
 :qid |DafnyPreludebpl.1125:15|
 :skolemid |260|
 :pattern ( (|Seq#FromArray| (MapType0Store refType (MapType1Type BoxType) h@@13 a@@55 (MapType1Store BoxType BoxType (MapType0Select refType (MapType1Type BoxType) h@@13 a@@55) (IndexField i@@17) ($Box BoxType v@@32))) a@@55))
)))
(assert (forall ((r@@3 T@U) (T@@88 T@T) ) (! (U_2_bool (MapType0Select T@@88 boolType (|Set#Singleton| T@@88 r@@3) r@@3))
 :qid |DafnyPreludebpl.671:18|
 :skolemid |127|
 :pattern ( (|Set#Singleton| T@@88 r@@3))
)))
(assert (forall ((x@@28 Int) (y@@11 Int) ) (! (= (INTERNAL_lt_boogie x@@28 y@@11) (< x@@28 y@@11))
 :qid |DafnyPreludebpl.1456:51|
 :skolemid |337|
 :pattern ( (INTERNAL_lt_boogie x@@28 y@@11))
)))
(assert (forall ((x@@29 Int) (y@@12 Int) ) (! (= (INTERNAL_gt_boogie x@@29 y@@12) (> x@@29 y@@12))
 :qid |DafnyPreludebpl.1458:51|
 :skolemid |339|
 :pattern ( (INTERNAL_gt_boogie x@@29 y@@12))
)))
(assert (forall ((m@@27 T@U) (n@@13 T@U) (u@@13 T@U) (U@@25 T@T) (V@@25 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@27 n@@13)) u@@13)) (and (=> (not (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13))) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@27 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 m@@27) u@@13))) (=> (U_2_bool (MapType0Select U@@25 boolType (|Map#Domain| U@@25 V@@25 n@@13) u@@13)) (= (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@27 n@@13)) u@@13) (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 n@@13) u@@13)))))
 :qid |DafnyPreludebpl.1291:21|
 :skolemid |297|
 :pattern ( (MapType0Select U@@25 V@@25 (|Map#Elements| U@@25 V@@25 (|Map#Merge| U@@25 V@@25 m@@27 n@@13)) u@@13))
)))
(assert (forall ((m@@28 T@U) (n@@14 T@U) (u@@14 T@U) (U@@26 T@T) (V@@26 T@T) ) (!  (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@28 n@@14)) u@@14)) (and (=> (not (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14))) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@28 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 m@@28) u@@14))) (=> (U_2_bool (MapType0Select U@@26 boolType (|IMap#Domain| U@@26 V@@26 n@@14) u@@14)) (= (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@28 n@@14)) u@@14) (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 n@@14) u@@14)))))
 :qid |DafnyPreludebpl.1432:21|
 :skolemid |329|
 :pattern ( (MapType0Select U@@26 V@@26 (|IMap#Elements| U@@26 V@@26 (|IMap#Merge| U@@26 V@@26 m@@28 n@@14)) u@@14))
)))
(assert (forall ((s@@29 T@U) (i@@18 Int) (v@@33 T@U) (x@@30 T@U) (T@@89 T@T) ) (!  (=> (and (<= 0 i@@18) (< i@@18 (|Seq#Length| T@@89 s@@29))) (= (U_2_int (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30)) (U_2_int (MapType0Select T@@89 intType (|MultiSet#Union| T@@89 (|MultiSet#Difference| T@@89 (|MultiSet#FromSeq| T@@89 s@@29) (|MultiSet#Singleton| T@@89 (|Seq#Index| T@@89 s@@29 i@@18))) (|MultiSet#Singleton| T@@89 v@@33)) x@@30))))
 :qid |DafnyPreludebpl.946:18|
 :skolemid |218|
 :pattern ( (MapType0Select T@@89 intType (|MultiSet#FromSeq| T@@89 (|Seq#Update| T@@89 s@@29 i@@18 v@@33)) x@@30))
)))
(assert (forall ((a@@56 T@U) (b@@40 T@U) (T@@90 T@T) ) (! (= (|Set#Union| T@@90 a@@56 (|Set#Union| T@@90 a@@56 b@@40)) (|Set#Union| T@@90 a@@56 b@@40))
 :qid |DafnyPreludebpl.709:18|
 :skolemid |141|
 :pattern ( (|Set#Union| T@@90 a@@56 (|Set#Union| T@@90 a@@56 b@@40)))
)))
(assert (forall ((a@@57 T@U) (b@@41 T@U) (T@@91 T@T) ) (! (= (|Set#Intersection| T@@91 a@@57 (|Set#Intersection| T@@91 a@@57 b@@41)) (|Set#Intersection| T@@91 a@@57 b@@41))
 :qid |DafnyPreludebpl.713:18|
 :skolemid |143|
 :pattern ( (|Set#Intersection| T@@91 a@@57 (|Set#Intersection| T@@91 a@@57 b@@41)))
)))
(assert (forall ((a@@58 T@U) (b@@42 T@U) (T@@92 T@T) ) (! (= (|ISet#Union| T@@92 a@@58 (|ISet#Union| T@@92 a@@58 b@@42)) (|ISet#Union| T@@92 a@@58 b@@42))
 :qid |DafnyPreludebpl.787:18|
 :skolemid |165|
 :pattern ( (|ISet#Union| T@@92 a@@58 (|ISet#Union| T@@92 a@@58 b@@42)))
)))
(assert (forall ((a@@59 T@U) (b@@43 T@U) (T@@93 T@T) ) (! (= (|ISet#Intersection| T@@93 a@@59 (|ISet#Intersection| T@@93 a@@59 b@@43)) (|ISet#Intersection| T@@93 a@@59 b@@43))
 :qid |DafnyPreludebpl.791:18|
 :skolemid |167|
 :pattern ( (|ISet#Intersection| T@@93 a@@59 (|ISet#Intersection| T@@93 a@@59 b@@43)))
)))
(assert (forall ((a@@60 T@U) (b@@44 T@U) (T@@94 T@T) ) (! (= (|MultiSet#Intersection| T@@94 a@@60 (|MultiSet#Intersection| T@@94 a@@60 b@@44)) (|MultiSet#Intersection| T@@94 a@@60 b@@44))
 :qid |DafnyPreludebpl.883:18|
 :skolemid |200|
 :pattern ( (|MultiSet#Intersection| T@@94 a@@60 (|MultiSet#Intersection| T@@94 a@@60 b@@44)))
)))
(assert (forall ((m@@29 T@U) (u@@15 T@U) (|u'| T@U) (v@@34 T@U) (U@@27 T@T) (V@@27 T@T) ) (!  (and (=> (= |u'| u@@15) (and (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|)) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|) v@@34))) (=> (or (not (= |u'| u@@15)) (not true)) (and (= (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|)) (U_2_bool (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 m@@29) |u'|))) (= (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|) (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 m@@29) |u'|)))))
 :qid |DafnyPreludebpl.1275:21|
 :skolemid |293|
 :pattern ( (MapType0Select U@@27 boolType (|Map#Domain| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|))
 :pattern ( (MapType0Select U@@27 V@@27 (|Map#Elements| U@@27 V@@27 (|Map#Build| U@@27 V@@27 m@@29 u@@15 v@@34)) |u'|))
)))
(assert (forall ((m@@30 T@U) (u@@16 T@U) (|u'@@0| T@U) (v@@35 T@U) (U@@28 T@T) (V@@28 T@T) ) (!  (and (=> (= |u'@@0| u@@16) (and (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|)) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|) v@@35))) (=> (or (not (= |u'@@0| u@@16)) (not true)) (and (= (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|)) (U_2_bool (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 m@@30) |u'@@0|))) (= (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|) (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 m@@30) |u'@@0|)))))
 :qid |DafnyPreludebpl.1409:21|
 :skolemid |323|
 :pattern ( (MapType0Select U@@28 boolType (|IMap#Domain| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|))
 :pattern ( (MapType0Select U@@28 V@@28 (|IMap#Elements| U@@28 V@@28 (|IMap#Build| U@@28 V@@28 m@@30 u@@16 v@@35)) |u'@@0|))
)))
(assert (forall ((f@@2 T@U) (ly@@0 T@U) (A@@0 T@T) ) (! (= (AtLayer A@@0 f@@2 ($LS ly@@0)) (AtLayer A@@0 f@@2 ly@@0))
 :qid |DafnyPreludebpl.500:18|
 :skolemid |101|
 :pattern ( (AtLayer A@@0 f@@2 ($LS ly@@0)))
)))
(assert (forall ((n@@15 Int) ) (!  (=> (and (<= 0 n@@15) (< n@@15 65536)) (= (|char#ToInt| (|char#FromInt| n@@15)) n@@15))
 :qid |DafnyPreludebpl.131:15|
 :skolemid |21|
 :pattern ( (|char#FromInt| n@@15))
)))
(assert (forall ((bx@@16 T@U) (s@@30 T@U) (t@@25 T@U) ) (!  (=> ($IsBox BoxType bx@@16 (TMap s@@30 t@@25)) (and (= ($Box (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@16)) bx@@16) ($Is (MapType BoxType BoxType) ($Unbox (MapType BoxType BoxType) bx@@16) (TMap s@@30 t@@25))))
 :qid |DafnyPreludebpl.205:15|
 :skolemid |35|
 :pattern ( ($IsBox BoxType bx@@16 (TMap s@@30 t@@25)))
)))
(assert (forall ((bx@@17 T@U) (s@@31 T@U) (t@@26 T@U) ) (!  (=> ($IsBox BoxType bx@@17 (TIMap s@@31 t@@26)) (and (= ($Box (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@17)) bx@@17) ($Is (IMapType BoxType BoxType) ($Unbox (IMapType BoxType BoxType) bx@@17) (TIMap s@@31 t@@26))))
 :qid |DafnyPreludebpl.208:15|
 :skolemid |36|
 :pattern ( ($IsBox BoxType bx@@17 (TIMap s@@31 t@@26)))
)))
(assert (forall ((a@@61 T@U) (b@@45 T@U) (T@@95 T@T) ) (! (= (|MultiSet#Disjoint| T@@95 a@@61 b@@45) (forall ((o@@29 T@U) ) (!  (or (= (U_2_int (MapType0Select T@@95 intType a@@61 o@@29)) 0) (= (U_2_int (MapType0Select T@@95 intType b@@45 o@@29)) 0))
 :qid |DafnyPreludebpl.913:39|
 :skolemid |209|
 :pattern ( (MapType0Select T@@95 intType a@@61 o@@29))
 :pattern ( (MapType0Select T@@95 intType b@@45 o@@29))
)))
 :qid |DafnyPreludebpl.912:18|
 :skolemid |210|
 :pattern ( (|MultiSet#Disjoint| T@@95 a@@61 b@@45))
)))
(assert (forall ((o@@30 T@U) (T@@96 T@T) ) (!  (not (U_2_bool (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@30)))
 :qid |DafnyPreludebpl.662:18|
 :skolemid |124|
 :pattern ( (MapType0Select T@@96 boolType (|Set#Empty| T@@96) o@@30))
)))
(assert (forall ((o@@31 T@U) (T@@97 T@T) ) (!  (not (U_2_bool (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@31)))
 :qid |DafnyPreludebpl.755:18|
 :skolemid |155|
 :pattern ( (MapType0Select T@@97 boolType (|ISet#Empty| T@@97) o@@31))
)))
(assert (forall ((h0 T@U) (h1 T@U) (a@@62 T@U) ) (!  (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (= (MapType0Select refType (MapType1Type BoxType) h0 a@@62) (MapType0Select refType (MapType1Type BoxType) h1 a@@62))) (= (|Seq#FromArray| h0 a@@62) (|Seq#FromArray| h1 a@@62)))
 :qid |DafnyPreludebpl.1120:15|
 :skolemid |259|
 :pattern ( (|Seq#FromArray| h1 a@@62) ($HeapSucc h0 h1))
)))
(assert (forall ((s@@32 T@U) (i@@19 Int) (v@@36 T@U) (T@@98 T@T) ) (!  (=> (and (<= 0 i@@19) (< i@@19 (|Seq#Length| T@@98 s@@32))) (= (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)) (|Seq#Length| T@@98 s@@32)))
 :qid |DafnyPreludebpl.1022:18|
 :skolemid |234|
 :pattern ( (|Seq#Length| T@@98 (|Seq#Update| T@@98 s@@32 i@@19 v@@36)))
)))
(assert (forall ((x@@31 Int) (y@@13 Int) ) (! (= (INTERNAL_mod_boogie x@@31 y@@13) (mod x@@31 y@@13))
 :qid |DafnyPreludebpl.1455:30|
 :skolemid |336|
 :pattern ( (INTERNAL_mod_boogie x@@31 y@@13))
)))
(assert (forall ((x@@32 Int) (y@@14 Int) ) (! (= (Mod x@@32 y@@14) (mod x@@32 y@@14))
 :qid |DafnyPreludebpl.1463:14|
 :skolemid |343|
 :pattern ( (Mod x@@32 y@@14))
)))
(assert (forall ((a@@63 T@U) (b@@46 T@U) (t0@@14 T@U) (t1@@5 T@U) ) (!  (=> (forall ((bx@@18 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@63 bx@@18)) (and ($IsBox BoxType bx@@18 t0@@14) ($IsBox BoxType (MapType0Select BoxType BoxType b@@46 bx@@18) t1@@5)))
 :qid |DafnyPreludebpl.1264:11|
 :skolemid |291|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@63 b@@46 (TMap t0@@14 t1@@5)) (TMap t0@@14 t1@@5)))
 :qid |DafnyPreludebpl.1261:15|
 :skolemid |292|
 :pattern ( (|Map#Glue| BoxType BoxType a@@63 b@@46 (TMap t0@@14 t1@@5)))
)))
(assert (forall ((a@@64 T@U) (b@@47 T@U) (t0@@15 T@U) (t1@@6 T@U) ) (!  (=> (forall ((bx@@19 T@U) ) (!  (=> (U_2_bool (MapType0Select BoxType boolType a@@64 bx@@19)) (and ($IsBox BoxType bx@@19 t0@@15) ($IsBox BoxType (MapType0Select BoxType BoxType b@@47 bx@@19) t1@@6)))
 :qid |DafnyPreludebpl.1399:11|
 :skolemid |321|
)) ($Is (MapType BoxType BoxType) (|Map#Glue| BoxType BoxType a@@64 b@@47 (TIMap t0@@15 t1@@6)) (TIMap t0@@15 t1@@6)))
 :qid |DafnyPreludebpl.1396:15|
 :skolemid |322|
 :pattern ( (|IMap#Glue| BoxType BoxType a@@64 b@@47 (TIMap t0@@15 t1@@6)))
)))
(assert (forall ((h@@14 T@U) (a@@65 T@U) ) (! (= (|Seq#Length| BoxType (|Seq#FromArray| h@@14 a@@65)) (_System.array.Length a@@65))
 :qid |DafnyPreludebpl.1105:15|
 :skolemid |256|
 :pattern ( (|Seq#Length| BoxType (|Seq#FromArray| h@@14 a@@65)))
)))
(assert (forall ((a@@66 T@U) (b@@48 T@U) ) (!  (and (= (TypeTupleCar (TypeTuple a@@66 b@@48)) a@@66) (= (TypeTupleCdr (TypeTuple a@@66 b@@48)) b@@48))
 :qid |DafnyPreludebpl.359:15|
 :skolemid |80|
 :pattern ( (TypeTuple a@@66 b@@48))
)))
(assert (forall ((f@@3 T@U) (i@@20 Int) ) (!  (and (= (MultiIndexField_Inverse0 BoxType (MultiIndexField f@@3 i@@20)) f@@3) (= (MultiIndexField_Inverse1 BoxType (MultiIndexField f@@3 i@@20)) i@@20))
 :qid |DafnyPreludebpl.521:15|
 :skolemid |105|
 :pattern ( (MultiIndexField f@@3 i@@20))
)))
(assert (forall ((s@@33 T@U) (val@@4 T@U) (T@@99 T@T) ) (!  (and (= (|Seq#Build_inv0| T@@99 (|Seq#Build| T@@99 s@@33 val@@4)) s@@33) (= (|Seq#Build_inv1| T@@99 (|Seq#Build| T@@99 s@@33 val@@4)) val@@4))
 :qid |DafnyPreludebpl.985:18|
 :skolemid |225|
 :pattern ( (|Seq#Build| T@@99 s@@33 val@@4))
)))
(assert (forall ((m@@31 T@U) (|m'@@2| T@U) (U@@29 T@T) (V@@29 T@T) ) (! (= (|Map#Equal| U@@29 V@@29 m@@31 |m'@@2|)  (and (forall ((u@@17 T@U) ) (! (= (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@31) u@@17)) (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 |m'@@2|) u@@17)))
 :qid |DafnyPreludebpl.1310:35|
 :skolemid |300|
)) (forall ((u@@18 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@29 boolType (|Map#Domain| U@@29 V@@29 m@@31) u@@18)) (= (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 m@@31) u@@18) (MapType0Select U@@29 V@@29 (|Map#Elements| U@@29 V@@29 |m'@@2|) u@@18)))
 :qid |DafnyPreludebpl.1311:35|
 :skolemid |301|
))))
 :qid |DafnyPreludebpl.1308:21|
 :skolemid |302|
 :pattern ( (|Map#Equal| U@@29 V@@29 m@@31 |m'@@2|))
)))
(assert (forall ((m@@32 T@U) (|m'@@3| T@U) (U@@30 T@T) (V@@30 T@T) ) (! (= (|IMap#Equal| U@@30 V@@30 m@@32 |m'@@3|)  (and (forall ((u@@19 T@U) ) (! (= (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@32) u@@19)) (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 |m'@@3|) u@@19)))
 :qid |DafnyPreludebpl.1420:36|
 :skolemid |324|
)) (forall ((u@@20 T@U) ) (!  (=> (U_2_bool (MapType0Select U@@30 boolType (|IMap#Domain| U@@30 V@@30 m@@32) u@@20)) (= (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 m@@32) u@@20) (MapType0Select U@@30 V@@30 (|IMap#Elements| U@@30 V@@30 |m'@@3|) u@@20)))
 :qid |DafnyPreludebpl.1421:35|
 :skolemid |325|
))))
 :qid |DafnyPreludebpl.1418:21|
 :skolemid |326|
 :pattern ( (|IMap#Equal| U@@30 V@@30 m@@32 |m'@@3|))
)))
(assert (forall ((o@@32 T@U) (m@@33 Int) (n@@16 Int) ) (!  (=> (and (<= 0 m@@33) (<= 0 n@@16)) (= (|ORD#Plus| (|ORD#Plus| o@@32 (|ORD#FromNat| m@@33)) (|ORD#FromNat| n@@16)) (|ORD#Plus| o@@32 (|ORD#FromNat| (+ m@@33 n@@16)))))
 :qid |DafnyPreludebpl.459:15|
 :skolemid |96|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@32 (|ORD#FromNat| m@@33)) (|ORD#FromNat| n@@16)))
)))
(assert (forall ((x@@33 Int) (y@@15 Int) ) (! (= (INTERNAL_le_boogie x@@33 y@@15) (<= x@@33 y@@15))
 :qid |DafnyPreludebpl.1457:51|
 :skolemid |338|
 :pattern ( (INTERNAL_le_boogie x@@33 y@@15))
)))
(assert (forall ((x@@34 Int) (y@@16 Int) ) (! (= (INTERNAL_ge_boogie x@@34 y@@16) (>= x@@34 y@@16))
 :qid |DafnyPreludebpl.1459:51|
 :skolemid |340|
 :pattern ( (INTERNAL_ge_boogie x@@34 y@@16))
)))
(assert (forall ((x@@35 Int) (y@@17 Int) ) (! (= (INTERNAL_sub_boogie x@@35 y@@17) (- x@@35 y@@17))
 :qid |DafnyPreludebpl.1452:30|
 :skolemid |333|
 :pattern ( (INTERNAL_sub_boogie x@@35 y@@17))
)))
(assert (forall ((x@@36 Int) (y@@18 Int) ) (! (= (Sub x@@36 y@@18) (- x@@36 y@@18))
 :qid |DafnyPreludebpl.1465:14|
 :skolemid |345|
 :pattern ( (Sub x@@36 y@@18))
)))
(assert (forall ((x@@37 Int) (y@@19 Int) ) (! (= (INTERNAL_add_boogie x@@37 y@@19) (+ x@@37 y@@19))
 :qid |DafnyPreludebpl.1451:30|
 :skolemid |332|
 :pattern ( (INTERNAL_add_boogie x@@37 y@@19))
)))
(assert (forall ((x@@38 Int) (y@@20 Int) ) (! (= (Add x@@38 y@@20) (+ x@@38 y@@20))
 :qid |DafnyPreludebpl.1464:14|
 :skolemid |344|
 :pattern ( (Add x@@38 y@@20))
)))
(assert (forall ((x@@39 Int) (y@@21 Int) ) (! (= (INTERNAL_mul_boogie x@@39 y@@21) (* x@@39 y@@21))
 :qid |DafnyPreludebpl.1453:30|
 :skolemid |334|
 :pattern ( (INTERNAL_mul_boogie x@@39 y@@21))
)))
(assert (forall ((x@@40 Int) (y@@22 Int) ) (! (= (Mul x@@40 y@@22) (* x@@40 y@@22))
 :qid |DafnyPreludebpl.1461:14|
 :skolemid |341|
 :pattern ( (Mul x@@40 y@@22))
)))
(assert (forall ((d T@U) ) (! (= (BoxRank ($Box DatatypeTypeType d)) (DtRank d))
 :qid |DafnyPreludebpl.389:15|
 :skolemid |83|
 :pattern ( (BoxRank ($Box DatatypeTypeType d)))
)))
(assert (forall ((r@@4 T@U) (T@@100 T@T) ) (! (= (|MultiSet#Singleton| T@@100 r@@4) (|MultiSet#UnionOne| T@@100 (|MultiSet#Empty| T@@100) r@@4))
 :qid |DafnyPreludebpl.850:18|
 :skolemid |190|
 :pattern ( (|MultiSet#Singleton| T@@100 r@@4))
)))
(assert (forall ((s@@34 T@U) (T@@101 T@T) ) (! (= (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)) (|Set#Card| T@@101 s@@34))
 :qid |DafnyPreludebpl.920:18|
 :skolemid |212|
 :pattern ( (|MultiSet#Card| T@@101 (|MultiSet#FromSet| T@@101 s@@34)))
)))
(assert (forall ((s@@35 T@U) (T@@102 T@T) ) (! (= (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)) (|Seq#Length| T@@102 s@@35))
 :qid |DafnyPreludebpl.931:18|
 :skolemid |215|
 :pattern ( (|MultiSet#Card| T@@102 (|MultiSet#FromSeq| T@@102 s@@35)))
)))
(assert (forall ((m@@34 T@U) (U@@31 T@T) (V@@31 T@T) ) (! (= (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@34)) (|Map#Card| U@@31 V@@31 m@@34))
 :qid |DafnyPreludebpl.1204:21|
 :skolemid |282|
 :pattern ( (|Set#Card| U@@31 (|Map#Domain| U@@31 V@@31 m@@34)))
 :pattern ( (|Map#Card| U@@31 V@@31 m@@34))
)))
(assert (forall ((m@@35 T@U) (U@@32 T@T) (V@@32 T@T) ) (! (= (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@35)) (|Map#Card| U@@32 V@@32 m@@35))
 :qid |DafnyPreludebpl.1210:21|
 :skolemid |284|
 :pattern ( (|Set#Card| BoxType (|Map#Items| U@@32 V@@32 m@@35)))
 :pattern ( (|Map#Card| U@@32 V@@32 m@@35))
)))
(assert (forall ((m@@36 T@U) (U@@33 T@T) (V@@33 T@T) ) (! (<= (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@36)) (|Map#Card| U@@33 V@@33 m@@36))
 :qid |DafnyPreludebpl.1207:21|
 :skolemid |283|
 :pattern ( (|Set#Card| V@@33 (|Map#Values| U@@33 V@@33 m@@36)))
 :pattern ( (|Map#Card| U@@33 V@@33 m@@36))
)))
(assert (forall ((s@@36 T@U) (n@@17 Int) (x@@41 T@U) (T@@103 T@T) ) (! (= (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41) (exists ((i@@21 Int) ) (!  (and (and (and (<= 0 n@@17) (<= n@@17 i@@21)) (< i@@21 (|Seq#Length| T@@103 s@@36))) (= (|Seq#Index| T@@103 s@@36 i@@21) x@@41))
 :qid |DafnyPreludebpl.1054:13|
 :skolemid |243|
 :pattern ( (|Seq#Index| T@@103 s@@36 i@@21))
)))
 :qid |DafnyPreludebpl.1051:18|
 :skolemid |244|
 :pattern ( (|Seq#Contains| T@@103 (|Seq#Drop| T@@103 s@@36 n@@17) x@@41))
)))
(assert (forall ((a@@67 Int) (b@@49 Int) ) (! (= (<= a@@67 b@@49) (= (|Math#min| a@@67 b@@49) a@@67))
 :qid |DafnyPreludebpl.820:15|
 :skolemid |177|
 :pattern ( (|Math#min| a@@67 b@@49))
)))
(assert (forall ((a@@68 Int) (b@@50 Int) ) (! (= (<= b@@50 a@@68) (= (|Math#min| a@@68 b@@50) b@@50))
 :qid |DafnyPreludebpl.821:15|
 :skolemid |178|
 :pattern ( (|Math#min| a@@68 b@@50))
)))
(assert (forall ((o@@33 T@U) (m@@37 Int) (n@@18 Int) ) (!  (=> (and (and (<= 0 m@@37) (<= 0 n@@18)) (<= n@@18 (+ (|ORD#Offset| o@@33) m@@37))) (and (=> (<= 0 (- m@@37 n@@18)) (= (|ORD#Minus| (|ORD#Plus| o@@33 (|ORD#FromNat| m@@37)) (|ORD#FromNat| n@@18)) (|ORD#Plus| o@@33 (|ORD#FromNat| (- m@@37 n@@18))))) (=> (<= (- m@@37 n@@18) 0) (= (|ORD#Minus| (|ORD#Plus| o@@33 (|ORD#FromNat| m@@37)) (|ORD#FromNat| n@@18)) (|ORD#Minus| o@@33 (|ORD#FromNat| (- n@@18 m@@37)))))))
 :qid |DafnyPreludebpl.469:15|
 :skolemid |98|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@33 (|ORD#FromNat| m@@37)) (|ORD#FromNat| n@@18)))
)))
(assert (forall ((o@@34 T@U) (m@@38 Int) (n@@19 Int) ) (!  (=> (and (and (<= 0 m@@38) (<= 0 n@@19)) (<= n@@19 (+ (|ORD#Offset| o@@34) m@@38))) (and (=> (<= 0 (- m@@38 n@@19)) (= (|ORD#Plus| (|ORD#Minus| o@@34 (|ORD#FromNat| m@@38)) (|ORD#FromNat| n@@19)) (|ORD#Minus| o@@34 (|ORD#FromNat| (- m@@38 n@@19))))) (=> (<= (- m@@38 n@@19) 0) (= (|ORD#Plus| (|ORD#Minus| o@@34 (|ORD#FromNat| m@@38)) (|ORD#FromNat| n@@19)) (|ORD#Plus| o@@34 (|ORD#FromNat| (- n@@19 m@@38)))))))
 :qid |DafnyPreludebpl.475:15|
 :skolemid |99|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@34 (|ORD#FromNat| m@@38)) (|ORD#FromNat| n@@19)))
)))
(assert (forall ((bx@@20 T@U) ) (!  (=> ($IsBox BoxType bx@@20 (TBitvector 0)) (and (= ($Box intType ($Unbox intType bx@@20)) bx@@20) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@20) (TBitvector 0))))
 :qid |DafnyPreludebpl.189:15|
 :skolemid |30|
 :pattern ( ($IsBox BoxType bx@@20 (TBitvector 0)))
)))
(assert (forall ((bx@@21 T@U) (t@@27 T@U) ) (!  (=> ($IsBox BoxType bx@@21 (TSet t@@27)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@21)) bx@@21) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@21) (TSet t@@27))))
 :qid |DafnyPreludebpl.193:15|
 :skolemid |31|
 :pattern ( ($IsBox BoxType bx@@21 (TSet t@@27)))
)))
(assert (forall ((bx@@22 T@U) (t@@28 T@U) ) (!  (=> ($IsBox BoxType bx@@22 (TISet t@@28)) (and (= ($Box (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@22)) bx@@22) ($Is (MapType0Type BoxType boolType) ($Unbox (MapType0Type BoxType boolType) bx@@22) (TISet t@@28))))
 :qid |DafnyPreludebpl.196:15|
 :skolemid |32|
 :pattern ( ($IsBox BoxType bx@@22 (TISet t@@28)))
)))
(assert (forall ((bx@@23 T@U) (t@@29 T@U) ) (!  (=> ($IsBox BoxType bx@@23 (TMultiSet t@@29)) (and (= ($Box (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@23)) bx@@23) ($Is (MapType0Type BoxType intType) ($Unbox (MapType0Type BoxType intType) bx@@23) (TMultiSet t@@29))))
 :qid |DafnyPreludebpl.199:15|
 :skolemid |33|
 :pattern ( ($IsBox BoxType bx@@23 (TMultiSet t@@29)))
)))
(assert (forall ((bx@@24 T@U) (t@@30 T@U) ) (!  (=> ($IsBox BoxType bx@@24 (TSeq t@@30)) (and (= ($Box (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@24)) bx@@24) ($Is (SeqType BoxType) ($Unbox (SeqType BoxType) bx@@24) (TSeq t@@30))))
 :qid |DafnyPreludebpl.202:15|
 :skolemid |34|
 :pattern ( ($IsBox BoxType bx@@24 (TSeq t@@30)))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (T@@104 T@T) ) (! (= (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)) (|MultiSet#UnionOne| T@@104 (|MultiSet#FromSeq| T@@104 s@@37) v@@37))
 :qid |DafnyPreludebpl.935:18|
 :skolemid |216|
 :pattern ( (|MultiSet#FromSeq| T@@104 (|Seq#Build| T@@104 s@@37 v@@37)))
)))
(assert (forall ((m@@39 T@U) (s@@38 T@U) (U@@34 T@T) (V@@34 T@T) ) (! (= (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@39 s@@38)) (|Set#Difference| U@@34 (|Map#Domain| U@@34 V@@34 m@@39) s@@38))
 :qid |DafnyPreludebpl.1298:21|
 :skolemid |298|
 :pattern ( (|Map#Domain| U@@34 V@@34 (|Map#Subtract| U@@34 V@@34 m@@39 s@@38)))
)))
(assert (forall ((m@@40 T@U) (s@@39 T@U) (U@@35 T@T) (V@@35 T@T) ) (! (= (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@40 s@@39)) (|Set#Difference| U@@35 (|IMap#Domain| U@@35 V@@35 m@@40) s@@39))
 :qid |DafnyPreludebpl.1439:21|
 :skolemid |330|
 :pattern ( (|IMap#Domain| U@@35 V@@35 (|IMap#Subtract| U@@35 V@@35 m@@40 s@@39)))
)))
(assert (forall ((ch T@U) ) (!  (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (and (<= 0 (|char#ToInt| ch)) (< (|char#ToInt| ch) 65536)))
 :qid |DafnyPreludebpl.136:15|
 :skolemid |22|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((o@@35 T@U) ) (!  (=> (|ORD#IsNat| o@@35) (= o@@35 (|ORD#FromNat| (|ORD#Offset| o@@35))))
 :qid |DafnyPreludebpl.412:15|
 :skolemid |86|
 :pattern ( (|ORD#Offset| o@@35))
 :pattern ( (|ORD#IsNat| o@@35))
)))
(assert (forall ((s@@40 T@U) (T@@105 T@T) ) (!  (and (= (= (|Set#Card| T@@105 s@@40) 0) (= s@@40 (|Set#Empty| T@@105))) (=> (or (not (= (|Set#Card| T@@105 s@@40) 0)) (not true)) (exists ((x@@42 T@U) ) (! (U_2_bool (MapType0Select T@@105 boolType s@@40 x@@42))
 :qid |DafnyPreludebpl.665:33|
 :skolemid |125|
))))
 :qid |DafnyPreludebpl.663:18|
 :skolemid |126|
 :pattern ( (|Set#Card| T@@105 s@@40))
)))
(assert (forall ((h@@15 T@U) (r@@5 T@U) (f@@4 T@U) (x@@43 T@U) (alpha@@0 T@T) ) (!  (=> ($IsGoodHeap (MapType0Store refType (MapType1Type BoxType) h@@15 r@@5 (MapType1Store alpha@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h@@15 r@@5) f@@4 ($Box alpha@@0 x@@43)))) ($HeapSucc h@@15 (MapType0Store refType (MapType1Type BoxType) h@@15 r@@5 (MapType1Store alpha@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h@@15 r@@5) f@@4 ($Box alpha@@0 x@@43)))))
 :qid |DafnyPreludebpl.601:22|
 :skolemid |115|
 :pattern ( (MapType0Store refType (MapType1Type BoxType) h@@15 r@@5 (MapType1Store alpha@@0 BoxType (MapType0Select refType (MapType1Type BoxType) h@@15 r@@5) f@@4 ($Box alpha@@0 x@@43))))
)))
(assert (forall ((a@@69 T@U) (b@@51 T@U) (T@@106 T@T) ) (! (= (|Set#Subset| T@@106 a@@69 b@@51) (forall ((o@@36 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@106 boolType a@@69 o@@36)) (U_2_bool (MapType0Select T@@106 boolType b@@51 o@@36)))
 :qid |DafnyPreludebpl.732:32|
 :skolemid |148|
 :pattern ( (MapType0Select T@@106 boolType a@@69 o@@36))
 :pattern ( (MapType0Select T@@106 boolType b@@51 o@@36))
)))
 :qid |DafnyPreludebpl.731:18|
 :skolemid |149|
 :pattern ( (|Set#Subset| T@@106 a@@69 b@@51))
)))
(assert (forall ((a@@70 T@U) (b@@52 T@U) (T@@107 T@T) ) (! (= (|ISet#Subset| T@@107 a@@70 b@@52) (forall ((o@@37 T@U) ) (!  (=> (U_2_bool (MapType0Select T@@107 boolType a@@70 o@@37)) (U_2_bool (MapType0Select T@@107 boolType b@@52 o@@37)))
 :qid |DafnyPreludebpl.803:33|
 :skolemid |170|
 :pattern ( (MapType0Select T@@107 boolType a@@70 o@@37))
 :pattern ( (MapType0Select T@@107 boolType b@@52 o@@37))
)))
 :qid |DafnyPreludebpl.802:18|
 :skolemid |171|
 :pattern ( (|ISet#Subset| T@@107 a@@70 b@@52))
)))
(assert (forall ((ty@@1 T@U) (heap@@0 T@U) (len@@0 Int) (init@@0 T@U) ) (!  (=> (and ($IsGoodHeap heap@@0) (<= 0 len@@0)) (= (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@0 len@@0 init@@0)) len@@0))
 :qid |DafnyPreludebpl.1002:15|
 :skolemid |229|
 :pattern ( (|Seq#Length| BoxType (|Seq#Create| ty@@1 heap@@0 len@@0 init@@0)))
)))
(assert (forall ((s@@41 T@U) (n@@20 Int) (k@@7 Int) (T@@108 T@T) ) (!  (=> (and (and (<= 0 n@@20) (<= n@@20 k@@7)) (< k@@7 (|Seq#Length| T@@108 s@@41))) (= (|Seq#Index| T@@108 (|Seq#Drop| T@@108 s@@41 n@@20) (- k@@7 n@@20)) (|Seq#Index| T@@108 s@@41 k@@7)))
 :qid |DafnyPreludebpl.1090:18|
 :weight 25
 :skolemid |254|
 :pattern ( (|Seq#Index| T@@108 s@@41 k@@7) (|Seq#Drop| T@@108 s@@41 n@@20))
)))
(assert (forall ((v@@38 T@U) (t0@@16 T@U) (h@@16 T@U) ) (! (= ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@16) h@@16) (forall ((bx@@25 T@U) ) (!  (=> (< 0 (U_2_int (MapType0Select BoxType intType v@@38 bx@@25))) ($IsAllocBox BoxType bx@@25 t0@@16 h@@16))
 :qid |DafnyPreludebpl.305:11|
 :skolemid |70|
 :pattern ( (MapType0Select BoxType intType v@@38 bx@@25))
)))
 :qid |DafnyPreludebpl.303:15|
 :skolemid |71|
 :pattern ( ($IsAlloc (MapType0Type BoxType intType) v@@38 (TMultiSet t0@@16) h@@16))
)))
(assert (forall ((o@@38 T@U) (p@@6 T@U) ) (!  (=> (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@38))) (or (and (= p@@6 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@38 p@@6) o@@38)) (and (or (not (= p@@6 (|ORD#FromNat| 0))) (not true)) (|ORD#Less| (|ORD#Minus| o@@38 p@@6) o@@38))))
 :qid |DafnyPreludebpl.453:15|
 :skolemid |95|
 :pattern ( (|ORD#Minus| o@@38 p@@6))
)))
(assert (forall ((a@@71 T@U) (x@@44 T@U) (T@@109 T@T) ) (!  (=> (not (U_2_bool (MapType0Select T@@109 boolType a@@71 x@@44))) (= (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@71 x@@44)) (+ (|Set#Card| T@@109 a@@71) 1)))
 :qid |DafnyPreludebpl.684:18|
 :skolemid |134|
 :pattern ( (|Set#Card| T@@109 (|Set#UnionOne| T@@109 a@@71 x@@44)))
)))
(assert (forall ((s@@42 T@U) ) (! ($Is (MapType0Type BoxType boolType) (SetRef_to_SetBox s@@42) (TSet Tclass._System.object?))
 :qid |DafnyPreludebpl.370:15|
 :skolemid |82|
 :pattern ( (SetRef_to_SetBox s@@42))
)))
(assert (forall ((s@@43 T@U) (m@@41 Int) (n@@21 Int) (T@@110 T@T) ) (!  (=> (and (and (<= 0 m@@41) (<= 0 n@@21)) (<= (+ m@@41 n@@21) (|Seq#Length| T@@110 s@@43))) (= (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@41) n@@21) (|Seq#Drop| T@@110 s@@43 (+ m@@41 n@@21))))
 :qid |DafnyPreludebpl.1170:18|
 :skolemid |273|
 :pattern ( (|Seq#Drop| T@@110 (|Seq#Drop| T@@110 s@@43 m@@41) n@@21))
)))
(assert (forall ((s0@@4 T@U) (s1@@2 T@U) (n@@22 Int) (T@@111 T@T) ) (! (= (|Seq#SameUntil| T@@111 s0@@4 s1@@2 n@@22) (forall ((j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 n@@22)) (= (|Seq#Index| T@@111 s0@@4 j@@3) (|Seq#Index| T@@111 s1@@2 j@@3)))
 :qid |DafnyPreludebpl.1069:13|
 :skolemid |248|
 :pattern ( (|Seq#Index| T@@111 s0@@4 j@@3))
 :pattern ( (|Seq#Index| T@@111 s1@@2 j@@3))
)))
 :qid |DafnyPreludebpl.1067:18|
 :skolemid |249|
 :pattern ( (|Seq#SameUntil| T@@111 s0@@4 s1@@2 n@@22))
)))
(assert (forall ((a@@72 T@U) (b@@53 T@U) (T@@112 T@T) ) (! (= (|Set#Disjoint| T@@112 a@@72 b@@53) (forall ((o@@39 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@112 boolType a@@72 o@@39))) (not (U_2_bool (MapType0Select T@@112 boolType b@@53 o@@39))))
 :qid |DafnyPreludebpl.746:34|
 :skolemid |153|
 :pattern ( (MapType0Select T@@112 boolType a@@72 o@@39))
 :pattern ( (MapType0Select T@@112 boolType b@@53 o@@39))
)))
 :qid |DafnyPreludebpl.745:18|
 :skolemid |154|
 :pattern ( (|Set#Disjoint| T@@112 a@@72 b@@53))
)))
(assert (forall ((a@@73 T@U) (b@@54 T@U) (T@@113 T@T) ) (! (= (|ISet#Disjoint| T@@113 a@@73 b@@54) (forall ((o@@40 T@U) ) (!  (or (not (U_2_bool (MapType0Select T@@113 boolType a@@73 o@@40))) (not (U_2_bool (MapType0Select T@@113 boolType b@@54 o@@40))))
 :qid |DafnyPreludebpl.813:35|
 :skolemid |175|
 :pattern ( (MapType0Select T@@113 boolType a@@73 o@@40))
 :pattern ( (MapType0Select T@@113 boolType b@@54 o@@40))
)))
 :qid |DafnyPreludebpl.812:18|
 :skolemid |176|
 :pattern ( (|ISet#Disjoint| T@@113 a@@73 b@@54))
)))
(assert (forall ((a@@74 T@U) (x@@45 T@U) (y@@23 T@U) (T@@114 T@T) ) (!  (=> (or (not (= x@@45 y@@23)) (not true)) (= (U_2_int (MapType0Select T@@114 intType a@@74 y@@23)) (U_2_int (MapType0Select T@@114 intType (|MultiSet#UnionOne| T@@114 a@@74 x@@45) y@@23))))
 :qid |DafnyPreludebpl.863:18|
 :skolemid |194|
 :pattern ( (|MultiSet#UnionOne| T@@114 a@@74 x@@45) (MapType0Select T@@114 intType a@@74 y@@23))
)))
(assert (forall ((s0@@5 T@U) (s1@@3 T@U) (n@@23 Int) (T@@115 T@T) ) (!  (and (=> (< n@@23 (|Seq#Length| T@@115 s0@@5)) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@5 s1@@3) n@@23) (|Seq#Index| T@@115 s0@@5 n@@23))) (=> (<= (|Seq#Length| T@@115 s0@@5) n@@23) (= (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@5 s1@@3) n@@23) (|Seq#Index| T@@115 s1@@3 (- n@@23 (|Seq#Length| T@@115 s0@@5))))))
 :qid |DafnyPreludebpl.1017:18|
 :skolemid |233|
 :pattern ( (|Seq#Index| T@@115 (|Seq#Append| T@@115 s0@@5 s1@@3) n@@23))
)))
(assert (forall ((o@@41 T@U) (p@@7 T@U) ) (!  (and (=> (|ORD#IsNat| (|ORD#Plus| o@@41 p@@7)) (and (|ORD#IsNat| o@@41) (|ORD#IsNat| p@@7))) (=> (|ORD#IsNat| p@@7) (and (= (|ORD#IsNat| (|ORD#Plus| o@@41 p@@7)) (|ORD#IsNat| o@@41)) (= (|ORD#Offset| (|ORD#Plus| o@@41 p@@7)) (+ (|ORD#Offset| o@@41) (|ORD#Offset| p@@7))))))
 :qid |DafnyPreludebpl.436:15|
 :skolemid |91|
 :pattern ( (|ORD#Plus| o@@41 p@@7))
)))
(assert (forall ((a@@75 Int) ) (!  (=> (< a@@75 0) (= (|Math#clip| a@@75) 0))
 :qid |DafnyPreludebpl.826:15|
 :skolemid |181|
 :pattern ( (|Math#clip| a@@75))
)))
(assert (forall ((x@@46 Int) ) (! (= ($Box intType (int_2_U (LitInt x@@46))) (Lit BoxType ($Box intType (int_2_U x@@46))))
 :qid |DafnyPreludebpl.109:15|
 :skolemid |18|
 :pattern ( ($Box intType (int_2_U (LitInt x@@46))))
)))
(assert (forall ((x@@47 Real) ) (! (= ($Box realType (real_2_U (LitReal x@@47))) (Lit BoxType ($Box realType (real_2_U x@@47))))
 :qid |DafnyPreludebpl.112:15|
 :skolemid |20|
 :pattern ( ($Box realType (real_2_U (LitReal x@@47))))
)))
(assert (forall ((x@@48 T@U) (T@@116 T@T) ) (! (= ($Box T@@116 (Lit T@@116 x@@48)) (Lit BoxType ($Box T@@116 x@@48)))
 :qid |DafnyPreludebpl.103:18|
 :skolemid |16|
 :pattern ( ($Box T@@116 (Lit T@@116 x@@48)))
)))
(assert (forall ((a@@76 T@U) (b@@55 T@U) (T@@117 T@T) ) (! (= (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@76 b@@55)) (|MultiSet#Union| T@@117 (|MultiSet#FromSeq| T@@117 a@@76) (|MultiSet#FromSeq| T@@117 b@@55)))
 :qid |DafnyPreludebpl.941:18|
 :skolemid |217|
 :pattern ( (|MultiSet#FromSeq| T@@117 (|Seq#Append| T@@117 a@@76 b@@55)))
)))
(assert (forall ((m@@42 T@U) (n@@24 T@U) (U@@36 T@T) (V@@36 T@T) ) (! (= (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@42 n@@24)) (|Set#Union| U@@36 (|Map#Domain| U@@36 V@@36 m@@42) (|Map#Domain| U@@36 V@@36 n@@24)))
 :qid |DafnyPreludebpl.1288:21|
 :skolemid |296|
 :pattern ( (|Map#Domain| U@@36 V@@36 (|Map#Merge| U@@36 V@@36 m@@42 n@@24)))
)))
(assert (forall ((m@@43 T@U) (n@@25 T@U) (U@@37 T@T) (V@@37 T@T) ) (! (= (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@43 n@@25)) (|Set#Union| U@@37 (|IMap#Domain| U@@37 V@@37 m@@43) (|IMap#Domain| U@@37 V@@37 n@@25)))
 :qid |DafnyPreludebpl.1429:21|
 :skolemid |328|
 :pattern ( (|IMap#Domain| U@@37 V@@37 (|IMap#Merge| U@@37 V@@37 m@@43 n@@25)))
)))
(assert (forall ((s@@44 T@U) (T@@118 T@T) ) (!  (=> (= (|Seq#Length| T@@118 s@@44) 0) (= s@@44 (|Seq#Empty| T@@118)))
 :qid |DafnyPreludebpl.967:18|
 :skolemid |223|
 :pattern ( (|Seq#Length| T@@118 s@@44))
)))
(assert (forall ((s@@45 T@U) (n@@26 Int) (T@@119 T@T) ) (!  (=> (= n@@26 0) (= (|Seq#Take| T@@119 s@@45 n@@26) (|Seq#Empty| T@@119)))
 :qid |DafnyPreludebpl.1168:18|
 :skolemid |272|
 :pattern ( (|Seq#Take| T@@119 s@@45 n@@26))
)))
(assert (forall ((s@@46 T@U) (x@@49 T@U) (n@@27 T@U) (T@@120 T@T) ) (!  (=> (<= 0 (U_2_int n@@27)) (= (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)) (+ (- (|MultiSet#Card| T@@120 s@@46) (U_2_int (MapType0Select T@@120 intType s@@46 x@@49))) (U_2_int n@@27))))
 :qid |DafnyPreludebpl.838:18|
 :skolemid |185|
 :pattern ( (|MultiSet#Card| T@@120 (MapType0Store T@@120 intType s@@46 x@@49 n@@27)))
)))
(assert (forall ((a@@77 T@U) (b@@56 T@U) (o@@42 T@U) (T@@121 T@T) ) (! (= (U_2_bool (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@77 b@@56) o@@42))  (or (U_2_bool (MapType0Select T@@121 boolType a@@77 o@@42)) (U_2_bool (MapType0Select T@@121 boolType b@@56 o@@42))))
 :qid |DafnyPreludebpl.688:18|
 :skolemid |135|
 :pattern ( (MapType0Select T@@121 boolType (|Set#Union| T@@121 a@@77 b@@56) o@@42))
)))
(assert (forall ((a@@78 T@U) (b@@57 T@U) (o@@43 T@U) (T@@122 T@T) ) (! (= (U_2_bool (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@78 b@@57) o@@43))  (or (U_2_bool (MapType0Select T@@122 boolType a@@78 o@@43)) (U_2_bool (MapType0Select T@@122 boolType b@@57 o@@43))))
 :qid |DafnyPreludebpl.770:18|
 :skolemid |159|
 :pattern ( (MapType0Select T@@122 boolType (|ISet#Union| T@@122 a@@78 b@@57) o@@43))
)))
(assert (forall ((h@@17 T@U) (v@@39 T@U) ) (! ($IsAlloc intType v@@39 TInt h@@17)
 :qid |DafnyPreludebpl.287:14|
 :skolemid |60|
 :pattern ( ($IsAlloc intType v@@39 TInt h@@17))
)))
(assert (forall ((h@@18 T@U) (v@@40 T@U) ) (! ($IsAlloc realType v@@40 TReal h@@18)
 :qid |DafnyPreludebpl.288:14|
 :skolemid |61|
 :pattern ( ($IsAlloc realType v@@40 TReal h@@18))
)))
(assert (forall ((h@@19 T@U) (v@@41 T@U) ) (! ($IsAlloc boolType v@@41 TBool h@@19)
 :qid |DafnyPreludebpl.289:14|
 :skolemid |62|
 :pattern ( ($IsAlloc boolType v@@41 TBool h@@19))
)))
(assert (forall ((h@@20 T@U) (v@@42 T@U) ) (! ($IsAlloc charType v@@42 TChar h@@20)
 :qid |DafnyPreludebpl.290:14|
 :skolemid |63|
 :pattern ( ($IsAlloc charType v@@42 TChar h@@20))
)))
(assert (forall ((h@@21 T@U) (v@@43 T@U) ) (! ($IsAlloc BoxType v@@43 TORDINAL h@@21)
 :qid |DafnyPreludebpl.291:14|
 :skolemid |64|
 :pattern ( ($IsAlloc BoxType v@@43 TORDINAL h@@21))
)))
(assert (forall ((s@@47 T@U) (i@@22 Int) (v@@44 T@U) (n@@28 Int) (T@@123 T@T) ) (!  (=> (and (and (<= 0 i@@22) (< i@@22 n@@28)) (<= n@@28 (|Seq#Length| T@@123 s@@47))) (= (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28) (|Seq#Update| T@@123 (|Seq#Take| T@@123 s@@47 n@@28) i@@22 v@@44)))
 :qid |DafnyPreludebpl.1130:18|
 :skolemid |261|
 :pattern ( (|Seq#Take| T@@123 (|Seq#Update| T@@123 s@@47 i@@22 v@@44) n@@28))
)))
(assert (forall ((v@@45 T@U) (t0@@17 T@U) ) (! (= ($Is (SeqType BoxType) v@@45 (TSeq t0@@17)) (forall ((i@@23 Int) ) (!  (=> (and (<= 0 i@@23) (< i@@23 (|Seq#Length| BoxType v@@45))) ($IsBox BoxType (|Seq#Index| BoxType v@@45 i@@23) t0@@17))
 :qid |DafnyPreludebpl.252:11|
 :skolemid |52|
 :pattern ( (|Seq#Index| BoxType v@@45 i@@23))
)))
 :qid |DafnyPreludebpl.250:15|
 :skolemid |53|
 :pattern ( ($Is (SeqType BoxType) v@@45 (TSeq t0@@17)))
)))
(assert (forall ((s@@48 T@U) (i@@24 Int) ) (!  (=> (and (<= 0 i@@24) (< i@@24 (|Seq#Length| BoxType s@@48))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))) (|Seq#Rank| BoxType s@@48)))
 :qid |DafnyPreludebpl.1152:15|
 :skolemid |267|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| BoxType s@@48 i@@24))))
)))
(assert (forall ((v@@46 T@U) (t0@@18 T@U) (t1@@7 T@U) ) (!  (=> ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@18 t1@@7)) (and (and ($Is (MapType0Type BoxType boolType) (|Map#Domain| BoxType BoxType v@@46) (TSet t0@@18)) ($Is (MapType0Type BoxType boolType) (|Map#Values| BoxType BoxType v@@46) (TSet t1@@7))) ($Is (MapType0Type BoxType boolType) (|Map#Items| BoxType BoxType v@@46) (TSet (Tclass._System.Tuple2 t0@@18 t1@@7)))))
 :qid |DafnyPreludebpl.265:15|
 :skolemid |56|
 :pattern ( ($Is (MapType BoxType BoxType) v@@46 (TMap t0@@18 t1@@7)))
)))
(assert (forall ((v@@47 T@U) (t0@@19 T@U) (t1@@8 T@U) ) (!  (=> ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@19 t1@@8)) (and (and ($Is (MapType0Type BoxType boolType) (|IMap#Domain| BoxType BoxType v@@47) (TISet t0@@19)) ($Is (MapType0Type BoxType boolType) (|IMap#Values| BoxType BoxType v@@47) (TISet t1@@8))) ($Is (MapType0Type BoxType boolType) (|IMap#Items| BoxType BoxType v@@47) (TISet (Tclass._System.Tuple2 t0@@19 t1@@8)))))
 :qid |DafnyPreludebpl.279:15|
 :skolemid |59|
 :pattern ( ($Is (IMapType BoxType BoxType) v@@47 (TIMap t0@@19 t1@@8)))
)))
(assert (forall ((v@@48 T@U) ) (! ($Is intType v@@48 TInt)
 :qid |DafnyPreludebpl.226:14|
 :skolemid |39|
 :pattern ( ($Is intType v@@48 TInt))
)))
(assert (forall ((v@@49 T@U) ) (! ($Is realType v@@49 TReal)
 :qid |DafnyPreludebpl.227:14|
 :skolemid |40|
 :pattern ( ($Is realType v@@49 TReal))
)))
(assert (forall ((v@@50 T@U) ) (! ($Is boolType v@@50 TBool)
 :qid |DafnyPreludebpl.228:14|
 :skolemid |41|
 :pattern ( ($Is boolType v@@50 TBool))
)))
(assert (forall ((v@@51 T@U) ) (! ($Is charType v@@51 TChar)
 :qid |DafnyPreludebpl.229:14|
 :skolemid |42|
 :pattern ( ($Is charType v@@51 TChar))
)))
(assert (forall ((v@@52 T@U) ) (! ($Is BoxType v@@52 TORDINAL)
 :qid |DafnyPreludebpl.230:14|
 :skolemid |43|
 :pattern ( ($Is BoxType v@@52 TORDINAL))
)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $Heap () T@U)
(declare-fun $IsHeapAnchor (T@U) Bool)
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
