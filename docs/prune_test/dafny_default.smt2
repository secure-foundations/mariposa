(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.case_split 3)
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
(declare-fun TInt () T@U)
(declare-fun TagInt () T@U)
(declare-fun alloc () T@U)
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
(declare-fun Tag (T@U) T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun _module.__default.secretPredicate (T@U Int) Bool)
(declare-fun $LS (T@U) T@U)
(declare-fun |_module.__default.secretPredicate#canCall| (Int) Bool)
(declare-fun LitInt (Int) Int)
(declare-fun Lit (T@T T@U) T@U)
(declare-fun |_module.__default.magicNum#canCall| () Bool)
(declare-fun StartFuel__module._default.secretPredicate () T@U)
(declare-fun MoreFuel__module._default.secretPredicate0 () T@U)
(declare-fun StartFuelAssert__module._default.secretPredicate () T@U)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun _module.__default.magicNum () Int)
(declare-fun MoreFuel__module._default.secretPredicate1 () T@U)
(declare-fun $LZ () T@U)
(declare-fun MapType0Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun refType () T@T)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType1Select (T@T T@T T@U T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun MapType2Select (T@T T@T T@U T@U) T@U)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType0Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun MapType1Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun $IsAlloc (T@T T@U T@U T@U) Bool)
(declare-fun $Is (T@T T@U T@U) Bool)
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
(assert (distinct TInt TagInt alloc)
)
(assert (= (Tag TInt) TagInt))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly T@U) (|q#0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0|) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly) |q#0|) (> |q#0| 1234)))
 :qid |foodfy.1:21|
 :skolemid |486|
 :pattern ( (_module.__default.secretPredicate ($LS $ly) |q#0|))
))))
(assert (forall ((x@@2 Int) ) (! (= (LitInt x@@2) x@@2)
 :qid |DafnyPreludebpl.108:29|
 :skolemid |17|
 :pattern ( (LitInt x@@2))
)))
(assert (forall ((x@@3 T@U) (T T@T) ) (! (= (Lit T x@@3) x@@3)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit T x@@3))
)))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) true)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@0 T@U) (|q#0@@0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| (LitInt |q#0@@0|)) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)) (U_2_bool (Lit boolType (bool_2_U (> |q#0@@0| 1234))))))
 :qid |foodfy.1:21|
 :weight 3
 :skolemid |487|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)))
))))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate0)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate0)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate0) MoreFuel__module._default.secretPredicate0)) (= _module.__default.magicNum (LitInt 15213))))))
(assert  (=> (<= 1 $FunctionContextHeight) (=> (or |_module.__default.magicNum#canCall| (< 1 $FunctionContextHeight)) (and (and (and (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate1)) (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate1)))) (= (AsFuelBottom MoreFuel__module._default.secretPredicate1) MoreFuel__module._default.secretPredicate1)) (= _module.__default.magicNum (LitInt 15213))))))
(assert (forall (($ly@@1 T@U) (|q#0@@1| Int) ) (! (= (_module.__default.secretPredicate $ly@@1 |q#0@@1|) (_module.__default.secretPredicate $LZ |q#0@@1|))
 :qid |foodfy.1:21|
 :skolemid |483|
 :pattern ( (_module.__default.secretPredicate (AsFuelBottom $ly@@1) |q#0@@1|))
)))
(assert (forall (($ly@@2 T@U) (|q#0@@2| Int) ) (! (= (_module.__default.secretPredicate ($LS $ly@@2) |q#0@@2|) (_module.__default.secretPredicate $ly@@2 |q#0@@2|))
 :qid |foodfy.1:21|
 :skolemid |482|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@2) |q#0@@2|))
)))
(assert  (and (and (and (and (and (and (and (and (and (forall ((t0 T@T) (t1 T@T) (t2 T@T) (val T@U) (m T@U) (x0 T@U) (x1 T@U) ) (! (= (MapType0Select t0 t1 t2 (MapType0Store t0 t1 t2 m x0 x1 val) x0 x1) val)
 :qid |mapAx0:MapType0Select|
 :weight 0
)) (and (and (forall ((u0 T@T) (u1 T@T) (s0 T@T) (t0@@0 T@T) (val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (x1@@0 T@U) (y0 T@U) (y1 T@U) ) (!  (or (= s0 t0@@0) (= (MapType0Select t0@@0 u0 u1 (MapType0Store s0 u0 u1 m@@0 x0@@0 x1@@0 val@@0) y0 y1) (MapType0Select t0@@0 u0 u1 m@@0 y0 y1)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((u0@@0 T@T) (u1@@0 T@T) (s0@@0 T@T) (t0@@1 T@T) (val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (x1@@1 T@U) (y0@@0 T@U) (y1@@0 T@U) ) (!  (or (= x0@@1 y0@@0) (= (MapType0Select t0@@1 u0@@0 u1@@0 (MapType0Store s0@@0 u0@@0 u1@@0 m@@1 x0@@1 x1@@1 val@@1) y0@@0 y1@@0) (MapType0Select t0@@1 u0@@0 u1@@0 m@@1 y0@@0 y1@@0)))
 :qid |mapAx1:MapType0Select:1|
 :weight 0
))) (forall ((u0@@1 T@T) (u1@@1 T@T) (s0@@1 T@T) (t0@@2 T@T) (val@@2 T@U) (m@@2 T@U) (x0@@2 T@U) (x1@@2 T@U) (y0@@1 T@U) (y1@@1 T@U) ) (!  (or (= x1@@2 y1@@1) (= (MapType0Select t0@@2 u0@@1 u1@@1 (MapType0Store s0@@1 u0@@1 u1@@1 m@@2 x0@@2 x1@@2 val@@2) y0@@1 y1@@1) (MapType0Select t0@@2 u0@@1 u1@@1 m@@2 y0@@1 y1@@1)))
 :qid |mapAx1:MapType0Select:2|
 :weight 0
)))) (= (Ctor refType) 3)) (forall ((t0@@3 T@T) (t1@@0 T@T) (val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) ) (! (= (MapType1Select t0@@3 t1@@0 (MapType1Store t0@@3 t1@@0 m@@3 x0@@3 val@@3) x0@@3) val@@3)
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((u0@@2 T@T) (s0@@2 T@T) (t0@@4 T@T) (val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (y0@@2 T@U) ) (!  (or (= s0@@2 t0@@4) (= (MapType1Select t0@@4 u0@@2 (MapType1Store s0@@2 u0@@2 m@@4 x0@@4 val@@4) y0@@2) (MapType1Select t0@@4 u0@@2 m@@4 y0@@2)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((u0@@3 T@T) (s0@@3 T@T) (t0@@5 T@T) (val@@5 T@U) (m@@5 T@U) (x0@@5 T@U) (y0@@3 T@U) ) (!  (or (= x0@@5 y0@@3) (= (MapType1Select t0@@5 u0@@3 (MapType1Store s0@@3 u0@@3 m@@5 x0@@5 val@@5) y0@@3) (MapType1Select t0@@5 u0@@3 m@@5 y0@@3)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
)))) (= (Ctor BoxType) 4)) (forall ((t0@@6 T@T) (t1@@1 T@T) (val@@6 T@U) (m@@6 T@U) (x0@@6 T@U) ) (! (= (MapType2Select t0@@6 t1@@1 (MapType2Store t0@@6 t1@@1 m@@6 x0@@6 val@@6) x0@@6) val@@6)
 :qid |mapAx0:MapType2Select|
 :weight 0
))) (forall ((u0@@4 T@T) (u1@@2 T@T) (val@@7 T@U) (m@@7 T@U) (x0@@7 T@U) (y0@@4 T@U) ) (!  (or (= x0@@7 y0@@4) (= (MapType2Select u0@@4 u1@@2 (MapType2Store u0@@4 u1@@2 m@@7 x0@@7 val@@7) y0@@4) (MapType2Select u0@@4 u1@@2 m@@7 y0@@4)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
))) (forall ((arg0@@2 T@T) ) (! (= (Ctor (MapType1Type arg0@@2)) 5)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@3 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@3)) arg0@@3)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@3))
))))
(assert (forall ((|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ($o T@U) ($f T@U) (alpha T@T) ) (! (= (U_2_bool (MapType0Select alpha refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o $f))  (=> (and (or (not (= $o |l#0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType2Select refType (MapType1Type BoxType) |l#1| $o) |l#2|)))) |l#3|))
 :qid |DafnyPreludebpl.156:1|
 :skolemid |491|
 :pattern ( (MapType0Select alpha refType boolType (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o $f))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@3 T@U) (|q#0@@3| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0@@3|) (< 0 $FunctionContextHeight)) true)
 :qid |foodfy.1:21|
 :skolemid |484|
 :pattern ( (_module.__default.secretPredicate $ly@@3 |q#0@@3|))
))))
(assert (forall ((h T@U) (v T@U) ) (! ($IsAlloc intType v TInt h)
 :qid |DafnyPreludebpl.287:14|
 :skolemid |60|
 :pattern ( ($IsAlloc intType v TInt h))
)))
(assert (forall ((v@@0 T@U) ) (! ($Is intType v@@0 TInt)
 :qid |DafnyPreludebpl.226:14|
 :skolemid |39|
 :pattern ( ($Is intType v@@0 TInt))
)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $Heap@0 () T@U)
(declare-fun $IsHeapAnchor (T@U) Bool)
(declare-fun $Heap () T@U)
(declare-fun MoreFuel__module._default.secretPredicate2 () T@U)
(declare-fun reveal__module._default.secretPredicate () Bool)
(declare-fun |##q#0@0| () Int)
(declare-fun $_ReadsFrame@0 () T@U)
(declare-fun null () T@U)
(set-info :boogie-vc-id CheckWellformed$$_module.__default.magicNum)
(set-option :timeout 0)
(set-option :rlimit 0)
(assert (not
 (=> (= (ControlFlow 0 0) 5) (let ((anon4_Else_correct  (=> (and (and ($IsGoodHeap $Heap@0) ($IsHeapAnchor $Heap@0)) (and (= $Heap $Heap@0) (= StartFuel__module._default.secretPredicate ($LS MoreFuel__module._default.secretPredicate2)))) (=> (and (and (and (= StartFuelAssert__module._default.secretPredicate ($LS ($LS MoreFuel__module._default.secretPredicate2))) reveal__module._default.secretPredicate) (and (= (AsFuelBottom MoreFuel__module._default.secretPredicate2) MoreFuel__module._default.secretPredicate2) (= |##q#0@0| (LitInt 31984823)))) (and (and ($IsAlloc intType (int_2_U |##q#0@0|) TInt $Heap@0) (|_module.__default.secretPredicate#canCall| (LitInt 31984823))) (and (|_module.__default.secretPredicate#canCall| (LitInt 31984823)) (= (ControlFlow 0 3) (- 0 2))))) (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate (LitInt 31984823))))))
(let ((anon4_Then_correct true))
(let ((anon0_correct  (=> (= $_ReadsFrame@0 (|lambda#0| null $Heap alloc false)) (=> (and (= (AsFuelBottom StartFuel__module._default.secretPredicate) StartFuel__module._default.secretPredicate) (= (AsFuelBottom StartFuelAssert__module._default.secretPredicate) StartFuelAssert__module._default.secretPredicate)) (and (=> (= (ControlFlow 0 4) 1) anon4_Then_correct) (=> (= (ControlFlow 0 4) 3) anon4_Else_correct))))))
(let ((PreconditionGeneratedEntry_correct  (=> (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (and (= 1 $FunctionContextHeight) (= (ControlFlow 0 5) 4))) anon0_correct)))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)
(pop 1)
; Valid
(get-info :rlimit)
(reset)
(set-option :rlimit 0)
; did a full reset
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.case_split 3)
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
(declare-fun $FunctionContextHeight () Int)
(declare-fun _module.__default.secretPredicate (T@U Int) Bool)
(declare-fun $LS (T@U) T@U)
(declare-fun |_module.__default.secretPredicate#canCall| (Int) Bool)
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
(declare-fun LitInt (Int) Int)
(declare-fun Lit (T@T T@U) T@U)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun $LZ () T@U)
(declare-fun MapType0Select (T@T T@T T@T T@U T@U T@U) T@U)
(declare-fun refType () T@T)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType1Select (T@T T@T T@U T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun MapType2Select (T@T T@T T@U T@U) T@U)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType0Store (T@T T@T T@T T@U T@U T@U T@U) T@U)
(declare-fun MapType1Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@T T@T T@U T@U T@U) T@U)
(declare-fun MapType1TypeInv0 (T@T) T@T)
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
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly T@U) (|q#0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0|) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly) |q#0|) (> |q#0| 1234)))
 :qid |foodfy.1:21|
 :skolemid |486|
 :pattern ( (_module.__default.secretPredicate ($LS $ly) |q#0|))
))))
(assert (forall ((x@@2 Int) ) (! (= (LitInt x@@2) x@@2)
 :qid |DafnyPreludebpl.108:29|
 :skolemid |17|
 :pattern ( (LitInt x@@2))
)))
(assert (forall ((x@@3 T@U) (T T@T) ) (! (= (Lit T x@@3) x@@3)
 :qid |DafnyPreludebpl.102:29|
 :skolemid |15|
 :pattern ( (Lit T x@@3))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@0 T@U) (|q#0@@0| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| (LitInt |q#0@@0|)) (< 0 $FunctionContextHeight)) (= (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)) (U_2_bool (Lit boolType (bool_2_U (> |q#0@@0| 1234))))))
 :qid |foodfy.1:21|
 :weight 3
 :skolemid |487|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@0) (LitInt |q#0@@0|)))
))))
(assert (forall (($ly@@1 T@U) (|q#0@@1| Int) ) (! (= (_module.__default.secretPredicate $ly@@1 |q#0@@1|) (_module.__default.secretPredicate $LZ |q#0@@1|))
 :qid |foodfy.1:21|
 :skolemid |483|
 :pattern ( (_module.__default.secretPredicate (AsFuelBottom $ly@@1) |q#0@@1|))
)))
(assert (forall (($ly@@2 T@U) (|q#0@@2| Int) ) (! (= (_module.__default.secretPredicate ($LS $ly@@2) |q#0@@2|) (_module.__default.secretPredicate $ly@@2 |q#0@@2|))
 :qid |foodfy.1:21|
 :skolemid |482|
 :pattern ( (_module.__default.secretPredicate ($LS $ly@@2) |q#0@@2|))
)))
(assert  (and (and (and (and (and (and (and (and (and (forall ((t0 T@T) (t1 T@T) (t2 T@T) (val T@U) (m T@U) (x0 T@U) (x1 T@U) ) (! (= (MapType0Select t0 t1 t2 (MapType0Store t0 t1 t2 m x0 x1 val) x0 x1) val)
 :qid |mapAx0:MapType0Select|
 :weight 0
)) (and (and (forall ((u0 T@T) (u1 T@T) (s0 T@T) (t0@@0 T@T) (val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (x1@@0 T@U) (y0 T@U) (y1 T@U) ) (!  (or (= s0 t0@@0) (= (MapType0Select t0@@0 u0 u1 (MapType0Store s0 u0 u1 m@@0 x0@@0 x1@@0 val@@0) y0 y1) (MapType0Select t0@@0 u0 u1 m@@0 y0 y1)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((u0@@0 T@T) (u1@@0 T@T) (s0@@0 T@T) (t0@@1 T@T) (val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (x1@@1 T@U) (y0@@0 T@U) (y1@@0 T@U) ) (!  (or (= x0@@1 y0@@0) (= (MapType0Select t0@@1 u0@@0 u1@@0 (MapType0Store s0@@0 u0@@0 u1@@0 m@@1 x0@@1 x1@@1 val@@1) y0@@0 y1@@0) (MapType0Select t0@@1 u0@@0 u1@@0 m@@1 y0@@0 y1@@0)))
 :qid |mapAx1:MapType0Select:1|
 :weight 0
))) (forall ((u0@@1 T@T) (u1@@1 T@T) (s0@@1 T@T) (t0@@2 T@T) (val@@2 T@U) (m@@2 T@U) (x0@@2 T@U) (x1@@2 T@U) (y0@@1 T@U) (y1@@1 T@U) ) (!  (or (= x1@@2 y1@@1) (= (MapType0Select t0@@2 u0@@1 u1@@1 (MapType0Store s0@@1 u0@@1 u1@@1 m@@2 x0@@2 x1@@2 val@@2) y0@@1 y1@@1) (MapType0Select t0@@2 u0@@1 u1@@1 m@@2 y0@@1 y1@@1)))
 :qid |mapAx1:MapType0Select:2|
 :weight 0
)))) (= (Ctor refType) 3)) (forall ((t0@@3 T@T) (t1@@0 T@T) (val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) ) (! (= (MapType1Select t0@@3 t1@@0 (MapType1Store t0@@3 t1@@0 m@@3 x0@@3 val@@3) x0@@3) val@@3)
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((u0@@2 T@T) (s0@@2 T@T) (t0@@4 T@T) (val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (y0@@2 T@U) ) (!  (or (= s0@@2 t0@@4) (= (MapType1Select t0@@4 u0@@2 (MapType1Store s0@@2 u0@@2 m@@4 x0@@4 val@@4) y0@@2) (MapType1Select t0@@4 u0@@2 m@@4 y0@@2)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((u0@@3 T@T) (s0@@3 T@T) (t0@@5 T@T) (val@@5 T@U) (m@@5 T@U) (x0@@5 T@U) (y0@@3 T@U) ) (!  (or (= x0@@5 y0@@3) (= (MapType1Select t0@@5 u0@@3 (MapType1Store s0@@3 u0@@3 m@@5 x0@@5 val@@5) y0@@3) (MapType1Select t0@@5 u0@@3 m@@5 y0@@3)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
)))) (= (Ctor BoxType) 4)) (forall ((t0@@6 T@T) (t1@@1 T@T) (val@@6 T@U) (m@@6 T@U) (x0@@6 T@U) ) (! (= (MapType2Select t0@@6 t1@@1 (MapType2Store t0@@6 t1@@1 m@@6 x0@@6 val@@6) x0@@6) val@@6)
 :qid |mapAx0:MapType2Select|
 :weight 0
))) (forall ((u0@@4 T@T) (u1@@2 T@T) (val@@7 T@U) (m@@7 T@U) (x0@@7 T@U) (y0@@4 T@U) ) (!  (or (= x0@@7 y0@@4) (= (MapType2Select u0@@4 u1@@2 (MapType2Store u0@@4 u1@@2 m@@7 x0@@7 val@@7) y0@@4) (MapType2Select u0@@4 u1@@2 m@@7 y0@@4)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
))) (forall ((arg0@@2 T@T) ) (! (= (Ctor (MapType1Type arg0@@2)) 5)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@3 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@3)) arg0@@3)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@3))
))))
(assert (forall ((|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ($o T@U) ($f T@U) (alpha T@T) ) (! (= (U_2_bool (MapType0Select alpha refType boolType (|lambda#1| |l#0| |l#1| |l#2| |l#3|) $o $f))  (=> (and (or (not (= $o |l#0|)) (not true)) (U_2_bool ($Unbox boolType (MapType1Select boolType BoxType (MapType2Select refType (MapType1Type BoxType) |l#1| $o) |l#2|)))) |l#3|))
 :qid |DafnyPreludebpl.156:1|
 :skolemid |492|
 :pattern ( (MapType0Select alpha refType boolType (|lambda#1| |l#0| |l#1| |l#2| |l#3|) $o $f))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@3 T@U) (|q#0@@3| Int) ) (!  (=> (or (|_module.__default.secretPredicate#canCall| |q#0@@3|) (< 0 $FunctionContextHeight)) true)
 :qid |foodfy.1:21|
 :skolemid |484|
 :pattern ( (_module.__default.secretPredicate $ly@@3 |q#0@@3|))
))))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun |q#0@@4| () Int)
(declare-fun |q##0_0@0| () Int)
(declare-fun StartFuelAssert__module._default.secretPredicate () T@U)
(declare-fun StartFuel__module._default.secretPredicate () T@U)
(declare-fun $_ModifiesFrame@0 () T@U)
(declare-fun null () T@U)
(declare-fun $Heap () T@U)
(declare-fun alloc () T@U)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $IsHeapAnchor (T@U) Bool)
(set-info :boogie-vc-id Impl$$_module.__default.barLemma)
(set-option :timeout 0)
(set-option :rlimit 0)
(assert (not
 (=> (= (ControlFlow 0 0) 5) (let ((anon3_Else_correct true))
(let ((anon3_Then_correct  (=> (> |q#0@@4| 6789) (=> (and (= |q##0_0@0| (- |q#0@@4| 1)) (= (ControlFlow 0 2) (- 0 1))) (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate |q##0_0@0|)))))
(let ((anon0_correct  (=> (= (AsFuelBottom StartFuel__module._default.secretPredicate) StartFuel__module._default.secretPredicate) (=> (and (= (AsFuelBottom StartFuelAssert__module._default.secretPredicate) StartFuelAssert__module._default.secretPredicate) (= $_ModifiesFrame@0 (|lambda#1| null $Heap alloc false))) (and (=> (= (ControlFlow 0 4) 2) anon3_Then_correct) (=> (= (ControlFlow 0 4) 3) anon3_Else_correct))))))
(let ((PreconditionGeneratedEntry_correct  (=> (and (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (= 2 $FunctionContextHeight)) (and (_module.__default.secretPredicate StartFuelAssert__module._default.secretPredicate |q#0@@4|) (= (ControlFlow 0 5) 4))) anon0_correct)))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)
(get-info :reason-unknown)
(assert (not (= (ControlFlow 0 2) (- 1))))
(check-sat)
(pop 1)
; Invalid
(get-info :rlimit)
