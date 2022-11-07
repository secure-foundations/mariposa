module SMTLib.PrettyPrint
open Microsoft.FSharp.Collections

type sexp = A of string | E of sexp list

let rec string_of_sexp exp =
    match exp with
    | A s -> s
    | E l -> "(" + (l |> List.map string_of_sexp |> String.concat " ") + ")"

   
let sexp_of_value (v : value) =
    A (match v with
       | Int i -> sprintf "%A" i
       | Float f -> sprintf "%.1f" f
       | Bool b -> sprintf "%b" b
       | String s -> sprintf "\"%s\"" s)

let sexp_list_of_annot (sexp_of : 'a -> sexp) (a : 'a annotation) =
    match a with
    | QId(id) -> [A ":qid"; A (snd id)]
    | SkolemId(id) -> [A ":skolemid"; A (snd id)]
    | Weight(n) -> [A ":weight"; A (sprintf "%A" n)]
    | Pattern(pats) -> [A ":pattern"; pats |> List.map sexp_of |> E]
    | NoPattern(pat) -> [A ":no-pattern"; sexp_of pat]
    | LblPos(pos) -> [A ":lblpos"; A (snd pos)]
    | LblNeg(pos) -> [A ":lblneg"; A (snd pos)]
    | Named(id) -> [A ":named"; A (snd id)]
    
let prepend a l =
    a :: l

let rec sexp_of_expr (q : expr) =
    match q with
    | Val v -> sexp_of_value v
    | Id x -> A (snd x)
    | Lst l -> l |> List.map sexp_of_expr |> E
    | Annot (opts, q) ->
        E ([A "!"; sexp_of_expr q] @
           (List.collect (sexp_list_of_annot sexp_of_expr) opts))
    | Not q ->
        E [A "not"; sexp_of_expr q]
    | And es ->
        es |> List.map sexp_of_expr |> prepend (A "and") |> E
    | Or es ->
        es |> List.map sexp_of_expr |> prepend (A "or") |> E
    | Implies (q1, q2) ->
        E [A "=>"; sexp_of_expr q1; sexp_of_expr q2]
    | Eq (q1, q2) ->
        E [A "="; sexp_of_expr q1; sexp_of_expr q2]
    | Forall (bindings, body) ->
        E [A "forall";
           bindings |> List.map (fun (x, t) -> E [A (snd x); sexp_of_expr t]) |> E;
           sexp_of_expr body]
    | Exists (bindings, body) ->
        E [A "exists";
           bindings |> List.map (fun (x, t) -> E [A (snd x); sexp_of_expr t]) |> E;
           sexp_of_expr body]
    | Let (bindings, body) ->
        E [A "let";
           bindings |> List.map (fun (x, q) -> E [A (snd x); sexp_of_expr q]) |> E;
           sexp_of_expr body]

let sexp_of_arg (name, atype) =
    E [A (snd name); sexp_of_expr atype]

let sexp_of_constructor (name, args) =
    E (A (snd name) :: (args |> List.map sexp_of_arg))

let sexp_of_datatype (name, constructors) =
    E (A (snd name) :: (constructors |> List.map sexp_of_constructor))

let sexp_of_stmt (s : stmt) =
    match s with
    | SetOption (opt, v) ->
        E [A "set-option"; A (":" + opt); sexp_of_expr v]
    | SetInfo (opt, v) ->
        E [A "set-info"; A (":" + opt); sexp_of_expr v]
    | GetInfo (opt) ->
        E [A "get-info"; A (":" + opt)]
    | DeclareSort (name, arity) ->
        E [A "declare-sort"; A (snd name); A (sprintf "%A" arity)]
    | DeclareFun (name, types, ret) ->
        E [A "declare-fun"; A (snd name); types |> List.map sexp_of_expr |> E; sexp_of_expr ret]
    | DefineFun (name, args, ret, body) ->
        E [A "define-fun"; A (snd name); args |> List.map sexp_of_arg |> E; sexp_of_expr ret;
           sexp_of_expr body]
    | DeclareDatatypes (targs, datatypes) ->
        E [A "declare-datatypes"; targs |> List.map sexp_of_expr |> E;
           datatypes |> List.map sexp_of_datatype |> E ]
    | Assert q -> E [A "assert"; sexp_of_expr q]
    | Push (Some i) -> E [A "push"; A (sprintf "%A" i)]
    | Push None -> E [A "push"]
    | Pop (Some i) -> E [A "pop"; A (sprintf "%A" i)]
    | Pop None -> E [A "pop"]
    | CheckSat -> E [A "check-sat"]
    | GetUnsatCore -> E [A "get-unsat-core"]
    | Reset -> E [A "reset"]
    | Labels -> E [A "labels"]
    | Echo v -> E [A "echo"; sexp_of_value v]
    | Eval e -> E [A "eval"; sexp_of_expr e]

let string_of_stmt (s : stmt) =
    s |> sexp_of_stmt |> string_of_sexp
