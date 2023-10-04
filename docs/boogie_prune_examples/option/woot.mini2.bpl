type Ty;
function  Lit<T>(x: T) : T;
axiom (forall<T> x: T ::   Lit(x): T == x);
type ref;
const null: ref;
type Box;
function $Box<T>(T) : Box;
function $Is<T>(T, Ty) : bool;
type HandleType;
function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;
type DatatypeType;
const $FunctionContextHeight: int;
type Field _;
const unique alloc: Field bool;
type Heap = <alpha>[]alpha;
function  read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha;
function $IsGoodHeap(Heap) : bool;
function $IsHeapAnchor(Heap) : bool;
var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);
type Set T = [T]bool;
function Set#Empty<T>() : Set T;
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
function #Options.Option.None() : DatatypeType;
function Options.Option.None_q(DatatypeType) : bool;
function Tclass.Options.Option(Ty) : Ty;
function #Options.Option.Some(Box) : DatatypeType;
function Options.Option.Some_q(DatatypeType) : bool;
axiom (forall d: DatatypeType :: 
  Options.Option.Some_q(d)
     ==> (exists a#20#0#0: Box :: d == #Options.Option.Some(a#20#0#0)));
function Options.Option.value(DatatypeType) : Box;
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
