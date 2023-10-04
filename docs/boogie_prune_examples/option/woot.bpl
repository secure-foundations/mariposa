type c;
function  e<j>(j) : j;
axiom (forall<j> g: j ::   e(g)== g);
type i;
type k;
function $k<j>(j) : k;
function $l<j>(j, c) : bool;
type m;
function n(c, c, p, m, k) : k;
type q;
type s a;
type p ;
var $p: p ;
type t j = [j]bool;
function t#ae<j>() : j;
function x.u.y(c, c) : c;
function af([p,k]k, [p,k]bool, [p,k]t k) : m;
function ag(c, c, p, m, k) : bool;
function ah(c, c, p, m, k) : t k;
axiom (forall ai, 
    aj: c, 
    ak: p, 
    h: [p,k]k, 
    r: [p,k]bool, 
    al: [p,k]t k, 
    am: k :: 
  ag(ai, aj, ak, af(h, r, al), am));
function #an.ao.ap() : q;
function an.ao.aq(q) : bool;
function #an.ao.ar(k) : q;
function an.ao.as(q) : bool;
axiom (forall d: q :: 
  (exists a#20#0#0: k :: d == #an.ao.ar(a#20#0#0)));
function an.ao.at(q) : k;
axiom (forall a, b: q :: 
  an.ao.at(a) == an.ao.at(b));
function an.au.av(aw, 
    ax: c, 
    ak: p, 
    #: q, 
    #0: m)
   : q;
function an.au.av#w(aw, 
    ax: c, 
    ak: p, 
    #: q, 
    #0: m)
   : bool;
axiom (forall an.ay.av$az, 
      an.ay.av$ax: c, 
      $p: p, 
      ba#0: q, 
      f#0: m :: 
    an.au.av#w(an.ay.av$az, an.ay.av$ax, $p, ba#0, f#0)
         || ag(an.ay.av$az, 
              an.ay.av$ax, 
              $p, 
              f#0, 
              an.ao.at(ba#0))
       ==> an.au.av(an.ay.av$az, an.ay.av$ax, $p, ba#0, f#0)
         == if an.ao.aq(ba#0)
           then #an.ao.ap()
           else (var v#1 := an.ao.at(ba#0); 
            #an.ao.ar(n(an.ay.av$az, an.ay.av$ax, $p, f#0, v#1))));
procedure bb$$an.au.av(an.ay.av$az, 
    an.ay.av$ax: c, 
    ba#0: q
       , 
    f#0: m
       where $l(0, 
        x.u.y(an.ay.av$az, an.ay.av$ax)))
   returns (bc#0: q
       );
  ensures an.ao.as(bc#0)
     ==> an.ao.at(bc#0)
       == n(an.ay.av$az, 
        an.ay.av$ax, 
        $p, 
        f#0, 
        an.ao.at(ba#0));
implementation bb$$an.au.av(an.ay.av$az, 
    an.ay.av$ax: c, 
    ba#0: q, 
    f#0: m)
   returns (bc#0: q)
{
  var $bd: <be>[i,s be]bool;
    $bd := (lambda<ad> $o: i, f: s ad :: 
      (if an.ao.as(ba#0)
           then ah(an.ay.av$az, 
            an.ay.av$ax, 
            $p, 
            f#0, 
            an.ao.at(ba#0))
           else t#ae())[$k($o)]);
    if (an.ao.as(ba#0))
    {
        assume false;
    }
    else
    {
        $bd := (lambda<ad> $o: i, f: s ad :: 
          (if an.ao.as(ba#0)
               then ah(an.ay.av$az, 
                an.ay.av$ax, 
                $p, 
                f#0, 
                an.ao.at(ba#0))
               else t#ae())[$k($o)]);
        if (ba#0 == #an.ao.ap())
        {
            assume an.au.av(an.ay.av$az, an.ay.av$ax, $p, ba#0, f#0)
               == e(#an.ao.ap());
        }
        else
        {
            assume false;
        }
        assume an.au.av(an.ay.av$az, an.ay.av$ax, $p, ba#0, f#0)
           == bc#0;
    }
}
