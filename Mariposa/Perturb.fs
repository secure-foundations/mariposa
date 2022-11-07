module Perturb
open SMTLib
open System
open Util

let id (s : stmt list) = s

let random_seed (seed : int32) (s : stmt list) =
    SetOption("random-seed", Val(Int(bigint(seed)))) :: s

let random_var_generator (seed : int32) =
    let R = System.Random(seed)
    fun (x : unit) ->
        let len = R.Next(2, 10)
        let v = System.String [|for _ in 1..len -> R.Next(26) + 97 |> char|]
        (v, v)
        

type AlphaState = {
    var : unit -> ident
    vars : Map<string, ident>;
    disallowed : Set<ident>
    }

let reserved =
    [""; "!"; "_"; "as"; "DECIMAL"; "exists"; "forall"; "let"; "NUMERAL"; "par"; "STRING"; 
     // Commands:
     "assert"; "check-sat"; "declare-sort"; "declare-fun"; "define-sort;"; "define-fun"; "exit";
     "get-assertions"; "get-assignment"; "get-info"; "get-option;"; "get-proof"; "get-unsat-core";
     "get-value"; "pop"; "push"; "set-logic"; "set-info"; "set-option";
     // Core theory:
     "and"; "or"; "not"; "iff"; "true"; "false"; "xor"; "distinct"; "ite"; "="; "Bool";
     "=>"; // implies (sic!)
     // Integers and reals
     "Int"; "Real"; "*"; "/"; "-"; "~"; "+"; "<"; "<="; ">"; ">="; "div"; "mod"; "rem";
     "^"; "sin"; "cos"; "tan"; "asin"; "acos"; "atan"; "sinh"; "cosh"; "tanh"; "asinh"; "acosh"; "atanh"; "pi"; "euler";
     "to_real"; "to_int"; "is_int";
     // Bitvectors
     "extract"; "concat"; 
     "bvnot"; "bvneg"; "bvand"; "bvor"; "bvadd"; "bvmul"; "bvudiv"; "bvurem"; "bvshl"; "bvlshr"; "bvult";
     // arrays
     "store"; "select"; "const"; "default"; "map"; "union"; "intersect"; "difference"; "complement";
     "subset"; "array-ext"; "as-array"; "Array";
     // Z3 (and not only?) extensions to bitvectors
     "bit1"; "bit0"; "bvsub"; "bvsdiv"; "bvsrem"; "bvsmod"; "bvsdiv0"; "bvudiv0"; "bvsrem0"; "bvurem0";
     "bvsmod0"; "bvsdiv_i"; "bvudiv_i"; "bvsrem_i"; "bvurem_i"; "bvumod_i"; "bvule"; "bvsle"; "bvuge";
     "bvsge"; "bvslt"; "bvugt"; "bvsgt"; "bvxor"; "bvnand"; "bvnor"; "bvxnor"; "sign_extend"; "zero_extend"; 
     "repeat"; "bvredor"; "bvredand"; "bvcomp"; "bvumul_noovfl"; "bvsmul_noovfl"; "bvsmul_noudfl"; "bvashr";
     "rotate_left"; "rotate_right"; "ext_rotate_left"; "ext_rotate_right"; "int2bv"; "bv2int"; "mkbv";
     // floating point (FIXME: Legacy; remove this)
     "plusInfinity"; "minusInfinity";
     "+"; "-"; "/"; "*"; "=="; "<"; ">"; "<="; ">="; 
     "abs"; "remainder"; "fusedMA"; "squareRoot"; "roundToIntegral"; 
     "isZero"; "isNZero"; "isPZero"; "isSignMinus"; "min"; "max"; "asFloat"; 
     // SMT v1 stuff (FIXME: Legacy; remove this)
     "flet"; "implies"; "!="; "if_then_else";
     // Z3 extensions
     "lblneg"; "lblpos"; "lbl-lit";
     "if"; "&&"; "||"; "equals"; "equiv"; "bool"; "minimize"; "maximize";
     // Boogie-defined
     "real_pow"; "UOrdering2"; "UOrdering3"; 
     // Floating point (final draft SMTLIB-v2.5)
     "NaN";
     "roundNearestTiesToEven"; "roundNearestTiesToAway"; "roundTowardPositive"; "roundTowardNegative"; "roundTowardZero"; 
     "RNE"; "RNA"; "RTP"; "RTN"; "RTZ";
     "fp.abs"; "fp.neg"; "fp.add"; "fp.sub"; "fp.mul"; "fp.div"; "fp.fma"; "fp.sqrt"; "fp.rem"; "fp.roundToIntegral";
     "fp.min"; "fp.max"; "fp.leq"; "fp.lt"; "fp.geq"; "fp.gt"; "fp.eq";
     "fp.isNormal"; "fp.isSubnormal"; "fp.isZero"; "fp.isInfinite"; "fp.isNaN"; "fp.isNegative"; "fp.isPositive";
     "fp"; "fp.to_ubv"; "fp.to_sbv"; "to_fp";
     "insert"; "map"; "head"; "tail"] |>
    List.map (fun x -> (x, x)) |>
    Set.ofList

let emptyAlphaState seed =
    {var = random_var_generator seed;
     vars = Map.empty;
     disallowed = reserved}

let rec newvar st k =
    let v = st.var ()
    if st.disallowed.Contains(v) then
        newvar st k
    else
        (v, {st with vars = st.vars.Add(fst k, v); disallowed = st.disallowed.Add(v)})

let lookup st k =
    if st.vars.ContainsKey(fst k) then
        st.vars.[fst k]
    else
        k

let rec alpha_rename_annotation (alpha_rename_a : AlphaState -> 'a -> 'a) st (annot : 'a annotation) =
    match annot with
    | Pattern xs ->
        xs |> List.map (alpha_rename_a st) |> Pattern
    | NoPattern a ->
        alpha_rename_a st a |> NoPattern
    | _ -> annot

let rec alpha_rename_bindings (st : AlphaState) (bindings : (ident * expr) list) =
    match bindings with
    | (x, v) :: xs ->
        let v' = alpha_rename_expr st v
        let (x', st') = newvar st x
        let (bindings', st'') = alpha_rename_bindings st' xs
        (((x', v') :: bindings'), st'')
    | [] -> ([], st)
and alpha_rename_expr (st : AlphaState) (e : expr) =
    match e with
    | Id x -> lookup st x |> Id
    | Annot(annots, e) ->
        let annots' = List.map (alpha_rename_annotation alpha_rename_expr st) annots
        let e' = alpha_rename_expr st e
        Annot(annots', e')
    | Lst es -> es |> List.map (alpha_rename_expr st) |> Lst
    | Not e -> alpha_rename_expr st e |> Not
    | And es -> es |> List.map (alpha_rename_expr st) |> And
    | Or es -> es |> List.map (alpha_rename_expr st) |> Or
    | Implies (e1, e2) -> Implies (alpha_rename_expr st e1,
                                   alpha_rename_expr st e2)
    | Eq (e1, e2) -> Eq (alpha_rename_expr st e1,
                         alpha_rename_expr st e2)
    | Let (bindings, body) ->
        let (bindings', st') = alpha_rename_bindings st bindings
        let body' = alpha_rename_expr st' body
        Let (bindings', body')
    | Forall (bindings, body) ->
        let (bindings', st') = alpha_rename_bindings st bindings
        let body' = alpha_rename_expr st' body
        Forall (bindings', body')
    | Exists (bindings, body) ->
        let (bindings', st') = alpha_rename_bindings st bindings
        let body' = alpha_rename_expr st' body
        Exists (bindings', body')
    | _ -> e

let alpha_rename_stmt (st : AlphaState) (s : stmt) =
    match s with
    | DeclareSort (x, n) ->
        let (x', st') = newvar st x
        (DeclareSort (x', n), st')
    | DeclareFun (x, types, returnType) ->
        let (x', st') = newvar st x
        (* types aren't dependent on x *)
        (DeclareFun (x',
                     types |> List.map (alpha_rename_expr st),
                     returnType |> alpha_rename_expr st),
         st')
    | DefineFun (x, bindings, returnType, body) ->
        let (x', st') = newvar st x
        let bindings', st'' = alpha_rename_bindings st bindings
        let returnType' = alpha_rename_expr st returnType
        let body' = alpha_rename_expr st'' body
        (DefineFun (x', bindings', returnType', body'),
         st')
    | Assert e -> (alpha_rename_expr st e |> Assert, st)
    | Eval e -> (alpha_rename_expr st e |> Eval, st)
    | _ -> (s, st)

let rec alpha_rename_stmts' st acc ss =
    match ss with
    | s :: ss' ->
        let s', st' = alpha_rename_stmt st s
        alpha_rename_stmts' st' (s' :: acc) ss'
    | [] -> acc

let alpha_rename_stmts st ss =
    alpha_rename_stmts' st [] ss |> List.rev


let alpha_rename (seed : int32) (ss : stmt list) =
    let st = emptyAlphaState seed
    alpha_rename_stmts st ss

let isAssert s =
    match s with
    | Assert _ -> true
    | _ -> false

let (|Asserts|NonAsserts|End|) ss =
    match ss with
    | s :: ss' when isAssert s -> Asserts(takeWhere isAssert ss)
    | s :: ss' -> NonAsserts(takeWhere (fun x -> not (isAssert x)) ss)
    | [] -> End

let rec permute_asserts (seed : int32) (ss : stmt list) =
    match ss with
    | Asserts(asserts, rest) -> (permute seed asserts) @ (permute_asserts seed rest)
    | NonAsserts(nonasserts, rest) -> nonasserts @ (permute_asserts seed rest)
    | End -> []

let permute_queries (seed : int32) ss =
    ss |> split is_reset |> permute seed |> join Reset


let isNamed annot =
    match annot with
    | Named _ -> true
    | _ -> false

let make_name n =
    let x = sprintf "a%d" n
    Named (x,x)

let make_unsat_core_stmt s =
    match s with
    | CheckSat -> [CheckSat; GetUnsatCore]
    | _ -> [s]

let make_unsat_core ss =
    ss |> List.collect make_unsat_core_stmt |>
    prepend (SetOption("produce-unsat-cores", (Val (Bool true))))

let name_assert (n, s) =
    match s with
    | Assert(Annot(annots, e)) ->
        if List.exists isNamed annots then
            s
        else
            Assert(Annot(((make_name n) :: annots), e))
    | Assert e ->
        Assert(Annot([make_name n], e))
    | _ -> s

let name_asserts ss =
    ss |> List.zip [2 .. ss.Length+1] |>
    List.map name_assert


let strip_names_stmt st =
    match st with
    | Assert e ->
        match e with
        | Annot(annots, e') ->
            Assert (Annot(List.filter (fun x -> (not (isNamed x))) annots, e'))
        | _ -> Assert e
    | _ -> st

let strip_names ss =
    ss |> List.map strip_names_stmt

let isNameIn names annot =
    match annot with
    | Named a -> Set.contains (fst a) names
    | _ -> false

let is_in_core names s =
    match s with
    | Assert(Annot(annots, e)) ->
        if List.exists (isNameIn names) annots then
            true
        else
            false
    | Assert _ -> false
    | _ -> true

let filter_asserts names ss =
    ss |> List.filter (is_in_core names)

let rec reorder_asserts_first names ss =
    match ss with
    | Asserts(asserts, rest) -> (List.sortBy (fun a -> if is_in_core names a then 0 else 1) asserts)
                                @ (reorder_asserts_first names rest)
    | NonAsserts(nonasserts, rest) -> nonasserts @ (reorder_asserts_first names rest)
    | End -> []

let rec reset_numbers_expr e =
    match e with
    | Val(Int(_)) -> Val(Int(bigint 1))
    | Lst(es) -> es |> List.map reset_numbers_expr |> Lst
    | Annot(annots, e) -> Annot(annots, reset_numbers_expr e)
    | Not(e) -> reset_numbers_expr e |> Not
    | And(es) -> es |> List.map reset_numbers_expr |> And
    | Or(es) -> es |> List.map reset_numbers_expr |> Or
    | Implies(e1, e2) -> Implies(reset_numbers_expr e1, reset_numbers_expr e2)
    | Eq(e1, e2) -> Eq(reset_numbers_expr e1, reset_numbers_expr e2)
    | Let(bindings, body) -> Let(bindings, reset_numbers_expr body)
    | Forall(bindings, body) -> Forall(bindings, reset_numbers_expr body)
    | Exists(bindings, body) -> Exists(bindings, reset_numbers_expr body)
    | _ -> e

let reset_numbers_stmt s =
    match s with
    | DefineFun(name, bindings, ret, body) -> DefineFun(name, bindings, ret, reset_numbers_expr body)
    | Assert(e) -> reset_numbers_expr e |> Assert
    | _ -> s

let reset_numbers ss =
    ss |> List.map reset_numbers_stmt

let is_set_timeout s =
    match s with
    | SetOption("TIMEOUT", _) -> true
    | _ -> false


// this is hacky, but should work for Dafny files.
let remove_resets_dfy ss =
    let clear_old_stuff ss =
        ss |> split is_set_timeout |> last
    let sections = ss |> split is_reset
    List.concat ((head sections) :: (List.map clear_old_stuff (tail sections)))
        

let (|IdArgs|_|) (args : string array) =
    if args.Length = 1 && args.[0] = "id" then
        Some()
    else
        None    

let (|RandomSeedArgs|_|) (args : string array) =
    if args.Length = 2 && args.[0] = "random-seed" then
        Some(Int32.Parse(args.[1]))
    else
        None    

let (|AlphaRename|_|) (args : string array) =
    if args.Length = 2 && args.[0] = "alpha-rename" then
        Some(Int32.Parse(args.[1]))
    else
        None

let (|PermuteAsserts|_|) (args : string array) =
    if args.Length = 2 && args.[0] = "permute-asserts" then
        Some(Int32.Parse(args.[1]))
    else
        None

let (|PermuteQueries|_|) (args : string array) =
    if args.Length = 2 && args.[0] = "permute-queries" then
        Some(Int32.Parse(args.[1]))
    else
        None

let (|UnsatCore|_|) (args : string array) =
    if args.Length = 1 && args.[0] = "unsat-core" then
        Some()
    else
        None

let (|NameAsserts|_|) (args : string array) =
    if args.Length = 1 && args.[0] = "name-asserts" then
        Some()
    else
        None

let (|FilterAsserts|_|) (args : string array) =
    if args.[0] = "filter-asserts" then
        args.[1..] |> Array.toList |> set |> Some
    else
        None

let (|StripNames|_|) (args : string array) =
    if args.[0] = "strip-names" then
        Some()
    else
        None

let (|ReorderAssertsFirst|_|) (args : string array) =
    if args.[0] = "reorder-asserts-first" then
        args.[1..] |> Array.toList |> set |> Some
    else
        None

let (|ResetNumbers|_|) (args : string array) =
    if args.[0] = "reset-numbers" then
        Some()
    else
        None    

let (|TreeShake|_|) (args : string array) =
    if args.[0] = "tree-shake" then
        args.[1..] |> Array.toList |> set |> Some
    else
        None    

let (|TreeShakeFstar|_|) (args : string array) =
    if args.[0] = "tree-shake-fstar" then
        args.[1..] |> Array.toList |> set |> Some
    else
        None    


let parseArgs (args : string array) =
    match args with
        | IdArgs -> id
        | RandomSeedArgs seed -> random_seed seed
        | AlphaRename seed -> alpha_rename seed
        | PermuteAsserts seed -> permute_asserts seed
        | PermuteQueries seed -> permute_queries seed
        | UnsatCore -> make_unsat_core
        | NameAsserts -> name_asserts
        | FilterAsserts names -> filter_asserts names
        | StripNames -> strip_names
        | ResetNumbers -> reset_numbers
        | TreeShake prohibited -> TreeShaking.process_stmts prohibited
        | TreeShakeFstar prohibited -> TreeShaking.process_stmts_fstar prohibited
        | _ -> failwithf "Got bad arguments %A" args


