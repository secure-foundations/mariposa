type Ty;
function  Lit<T>(x: T) : T;
axiom (forall<T> x: T ::   Lit(x): T == x);
type ref;
const null: ref;
type Box;
function $Box<T>(T) : Box;
function $Unbox<T>(Box) : T;
function $Is<T>(T, Ty) : bool;
function $IsAlloc<T>(T, Ty, Heap) : bool;
function $IsAllocBox<T>(T, Ty, Heap) : bool;
type HandleType;
function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;
type DatatypeType;
type DtCtorId;
function DatatypeCtorId(DatatypeType) : DtCtorId;
type ORDINAL = Box;
function  ORD#IsLimit() : bool
;
function ORD#FromNat(int) : ORDINAL;
function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;
function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;
axiom (forall o: ORDINAL, m: int, n: int :: 
  0 <= m && 0 <= n
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));
const $FunctionContextHeight: int;
type Field _;
function IndexField(int) : Field Box;
const unique alloc: Field bool;
type Heap = <alpha>[]alpha;
function  read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
;
function  update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
;
function $IsGoodHeap(Heap) : bool;
function $IsHeapAnchor(Heap) : bool;
var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
type Set T = [T]bool;
function Set#Empty<T>() : Set T;
type Seq _;
function Seq#Length<T>(Seq T) : int;
function Seq#Append<T>(Seq T, Seq T) : Seq T;
function Seq#Index<T>(Seq T, int) : T;
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
function Seq#Contains<T>(Seq T, T) : bool;
axiom (forall<T> s: Seq T, x: T :: 
  Seq#Contains(s, x)
     == (exists i: int :: 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T :: 
  Seq#Contains(Seq#Take(s, n), x)
     == (exists i: int :: 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
function Seq#Take<T>(s: Seq T, howMany: int) : Seq T;
function Seq#FromArray(h: Heap, a: ref) : Seq Box;
axiom (forall h: Heap, a: ref :: 
  (forall i: int :: 
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));
function Handle2([Heap,Box,Box]Box, [Heap,Box,Box]bool, [Heap,Box,Box]Set Box) : HandleType;
function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box :: 
  r[heap, bx0, bx1] ==> Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1));
function  Requires2#canCall() : bool
;
function Tclass._System.___hFunc1(Ty, Ty) : Ty;
function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set Box) : HandleType;
function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;
function Reads1(Ty, Ty, Heap, HandleType, Box) : Set Box;
axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box :: 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));
axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box, 
    bx: Box :: 
  Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] == rd[heap, bx0][bx]);
function  Requires1#canCall() : bool
;
function #Options.Option.None() : DatatypeType;
const unique ##Options.Option.None: DtCtorId;
axiom DatatypeCtorId(#Options.Option.None()) == ##Options.Option.None;
function Options.Option.None_q(DatatypeType) : bool;
function Tclass.Options.Option(Ty) : Ty;
function #Options.Option.Some(Box) : DatatypeType;
const unique ##Options.Option.Some: DtCtorId;
axiom (forall a#19#0#0: Box :: 
  DatatypeCtorId(#Options.Option.Some(a#19#0#0)) == ##Options.Option.Some);
function Options.Option.Some_q(DatatypeType) : bool;
axiom (forall d: DatatypeType :: 
  Options.Option.Some_q(d)
     ==> (exists a#20#0#0: Box :: d == #Options.Option.Some(a#20#0#0)));
axiom (forall Options.Option$V: Ty, a#22#0#0: Box, $h: Heap :: 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Options.Option.Some(a#22#0#0), Tclass.Options.Option(Options.Option$V), $h)
       == $IsAllocBox(a#22#0#0, Options.Option$V, $h)));
function Options.Option.value(DatatypeType) : Box;
axiom (forall a#24#0#0: Box :: 
  Options.Option.value(#Options.Option.Some(a#24#0#0)) == a#24#0#0);
function Options.Option#Equal(DatatypeType, DatatypeType) : bool;
axiom (forall a: DatatypeType, b: DatatypeType :: 
  Options.Option.None_q(a) && Options.Option.None_q(b)
     ==> (Options.Option#Equal(a, b)
       <==> Options.Option.value(a) == Options.Option.value(b)));
function Options.__default.MapOption(Options._default.MapOption$V0: Ty, 
    Options._default.MapOption$V1: Ty, 
    $heap: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   : DatatypeType;
function Options.__default.MapOption#canCall(Options._default.MapOption$V0: Ty, 
    Options._default.MapOption$V1: Ty, 
    $heap: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   : bool;
axiom 1 <= $FunctionContextHeight
   ==> (forall Options._default.MapOption$V0: Ty, 
      Options._default.MapOption$V1: Ty, 
      $Heap: Heap, 
      opt#0: DatatypeType, 
      f#0: HandleType :: 
    Options.__default.MapOption#canCall(Options._default.MapOption$V0, Options._default.MapOption$V1, $Heap, opt#0, f#0)
         || (1 != $FunctionContextHeight
           && (Options.Option.Some_q(opt#0)
             ==> Requires1(Options._default.MapOption$V0, 
              Options._default.MapOption$V1, 
              $Heap, 
              f#0, 
              Options.Option.value(opt#0))))
       ==> Options.__default.MapOption(Options._default.MapOption$V0, Options._default.MapOption$V1, $Heap, opt#0, f#0)
         == (if Options.Option.None_q(opt#0)
           then #Options.Option.None()
           else (var v#1 := Options.Option.value(opt#0); 
            #Options.Option.Some(Apply1(Options._default.MapOption$V0, Options._default.MapOption$V1, $Heap, f#0, v#1)))));
procedure CheckWellformed$$Options.__default.MapOption(Options._default.MapOption$V0: Ty, 
    Options._default.MapOption$V1: Ty, 
    opt#0: DatatypeType
       where $Is(opt#0, Tclass.Options.Option(Options._default.MapOption$V0)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(Options._default.MapOption$V0, Options._default.MapOption$V1)))
   returns (result#0: DatatypeType
       where $Is(result#0, Tclass.Options.Option(Options._default.MapOption$V1)));
  ensures Options.Option.Some_q(result#0)
     ==> Options.Option.value(result#0)
       == Apply1(Options._default.MapOption$V0, 
        Options._default.MapOption$V1, 
        $Heap, 
        f#0, 
        Options.Option.value(opt#0));
implementation CheckWellformed$$Options.__default.MapOption(Options._default.MapOption$V0: Ty, 
    Options._default.MapOption$V1: Ty, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   returns (result#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if Options.Option.Some_q(opt#0)
           then Reads1(Options._default.MapOption$V0, 
            Options._default.MapOption$V1, 
            $Heap, 
            f#0, 
            Options.Option.value(opt#0))
           else Set#Empty(): Set Box)[$Box($o)]);
    if (Options.Option.Some_q(opt#0))
    {}
    else
    {}
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (if Options.Option.Some_q(opt#0)
               then Reads1(Options._default.MapOption$V0, 
                Options._default.MapOption$V1, 
                $Heap, 
                f#0, 
                Options.Option.value(opt#0))
               else Set#Empty(): Set Box)[$Box($o)]);
        if (opt#0 == #Options.Option.None())
        {
            assume Options.__default.MapOption(Options._default.MapOption$V0, Options._default.MapOption$V1, $Heap, opt#0, f#0)
               == Lit(#Options.Option.None());
        }
        else
        {
            assume false;
        }
        assume Options.__default.MapOption(Options._default.MapOption$V0, Options._default.MapOption$V1, $Heap, opt#0, f#0)
           == result#0;
    }
}
function Options.__default.FlatMapOption(Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    $heap: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   : DatatypeType;
function Options.__default.FlatMapOption#canCall(Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    $heap: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   : bool;
axiom (forall Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    $h0: Heap, 
    $h1: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType :: 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (if Options.Option.Some_q(opt#0)
             then Reads1(Options._default.FlatMapOption$V0, 
              Tclass.Options.Option(Options._default.FlatMapOption$V1), 
              $h0, 
              f#0, 
              Options.Option.value(opt#0))
             else Set#Empty(): Set Box)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
        Options._default.FlatMapOption$V1, 
        $h0, 
        opt#0, 
        f#0)
       == Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
        Options._default.FlatMapOption$V1, 
        $h1, 
        opt#0, 
        f#0));
axiom 2 <= $FunctionContextHeight
   ==> (forall Options._default.FlatMapOption$V0: Ty, 
      Options._default.FlatMapOption$V1: Ty, 
      $Heap: Heap, 
      opt#0: DatatypeType, 
      f#0: HandleType :: 
    Options.__default.FlatMapOption#canCall(Options._default.FlatMapOption$V0, 
          Options._default.FlatMapOption$V1, 
          $Heap, 
          opt#0, 
          f#0)
         || (2 != $FunctionContextHeight
           && (Options.Option.Some_q(opt#0)
             ==> Requires1(Options._default.FlatMapOption$V0, 
              Tclass.Options.Option(Options._default.FlatMapOption$V1), 
              $Heap, 
              f#0, 
              Options.Option.value(opt#0))))
       ==> (Options.Option.Some_q(opt#0)
             && Options.Option.Some_q($Unbox(Apply1(Options._default.FlatMapOption$V0, 
                  Tclass.Options.Option(Options._default.FlatMapOption$V1), 
                  $Heap, 
                  f#0, 
                  Options.Option.value(opt#0))): DatatypeType))
         && $Is(Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
            Options._default.FlatMapOption$V1, 
            $Heap, 
            opt#0, 
            f#0), 
          Tclass.Options.Option(Options._default.FlatMapOption$V1)));
function Options.__default.FlatMapOption#requires(Ty, Ty, Heap, DatatypeType, HandleType) : bool;
axiom (forall Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    $Heap: Heap, 
    opt#0: DatatypeType, 
    f#0: HandleType :: 
  $IsGoodHeap($Heap)
     ==> Options.__default.FlatMapOption#requires(Options._default.FlatMapOption$V0, 
        Options._default.FlatMapOption$V1, 
        $Heap, 
        opt#0, 
        f#0)
       == (Options.Option.Some_q(opt#0)
         ==> Requires1(Options._default.FlatMapOption$V0, 
          Tclass.Options.Option(Options._default.FlatMapOption$V1), 
          $Heap, 
          f#0, 
          Options.Option.value(opt#0))));
axiom 2 <= $FunctionContextHeight
   ==> (forall Options._default.FlatMapOption$V0: Ty, 
      Options._default.FlatMapOption$V1: Ty, 
      $Heap: Heap, 
      opt#0: DatatypeType, 
      f#0: HandleType :: 
    Options.__default.FlatMapOption#canCall(Options._default.FlatMapOption$V0, 
          Options._default.FlatMapOption$V1, 
          $Heap, 
          opt#0, 
          f#0)
         || (2 != $FunctionContextHeight
           && (Options.Option.Some_q(opt#0)
             ==> Requires1(Options._default.FlatMapOption$V0, 
              Tclass.Options.Option(Options._default.FlatMapOption$V1), 
              $Heap, 
              f#0, 
              Options.Option.value(opt#0))))
       ==> Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
          Options._default.FlatMapOption$V1, 
          $Heap, 
          opt#0, 
          f#0)
         == (if Options.Option.None_q(opt#0)
           then #Options.Option.None()
           else (var v#1 := Options.Option.value(opt#0); 
            $Unbox(Apply1(Options._default.FlatMapOption$V0, 
                Tclass.Options.Option(Options._default.FlatMapOption$V1), 
                $Heap, 
                f#0, 
                v#1)): DatatypeType)));
procedure CheckWellformed$$Options.__default.FlatMapOption(Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    opt#0: DatatypeType
       where $Is(opt#0, Tclass.Options.Option(Options._default.FlatMapOption$V0)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(Options._default.FlatMapOption$V0, 
          Tclass.Options.Option(Options._default.FlatMapOption$V1))))
   returns (result#0: DatatypeType
       where $Is(result#0, Tclass.Options.Option(Options._default.FlatMapOption$V1)));
  ensures Options.Option.Some_q(opt#0)
       && Options.Option.Some_q($Unbox(Apply1(Options._default.FlatMapOption$V0, 
            Tclass.Options.Option(Options._default.FlatMapOption$V1), 
            $Heap, 
            f#0, 
            Options.Option.value(opt#0))): DatatypeType)
     ==> Options.Option.value(result#0)
       == Options.Option.value($Unbox(Apply1(Options._default.FlatMapOption$V0, 
            Tclass.Options.Option(Options._default.FlatMapOption$V1), 
            $Heap, 
            f#0, 
            Options.Option.value(opt#0))): DatatypeType);
implementation CheckWellformed$$Options.__default.FlatMapOption(Options._default.FlatMapOption$V0: Ty, 
    Options._default.FlatMapOption$V1: Ty, 
    opt#0: DatatypeType, 
    f#0: HandleType)
   returns (result#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#1: bool;
  var _mcc#0#0: Box;
  var v#2: Box;
  var let#0#0#0: Box;
  var b$reqreads#2: bool;
    if (Options.Option.Some_q(opt#0))
    {
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
             ==> (if Options.Option.Some_q(opt#0)
               then Reads1(Options._default.FlatMapOption$V0, 
                Tclass.Options.Option(Options._default.FlatMapOption$V1), 
                $Heap, 
                f#0, 
                Options.Option.value(opt#0))
               else Set#Empty(): Set Box)[$Box($o)]);
        if (opt#0 == #Options.Option.None())
        {}
        else if (opt#0 == #Options.Option.Some(_mcc#0#0))
        {
            assume let#0#0#0 == _mcc#0#0;
            assume v#2 == let#0#0#0;
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                 ==> $_Frame[$o, $f]);
            assume Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
                Options._default.FlatMapOption$V1, 
                $Heap, 
                opt#0, 
                f#0)
               == $Unbox(Apply1(Options._default.FlatMapOption$V0, 
                  Tclass.Options.Option(Options._default.FlatMapOption$V1), 
                  $Heap, 
                  f#0, 
                  v#2)): DatatypeType;
            assume $Is(Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
                Options._default.FlatMapOption$V1, 
                $Heap, 
                opt#0, 
                f#0), 
              Tclass.Options.Option(Options._default.FlatMapOption$V1));
        }
        else
        {
            assume false;
        }
        assume Options.__default.FlatMapOption(Options._default.FlatMapOption$V0, 
            Options._default.FlatMapOption$V1, 
            $Heap, 
            opt#0, 
            f#0)
           == result#0;
    }
}
