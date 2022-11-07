// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open SMTLib
open SMTLib.Parse
open SMTLib.PrettyPrint

let isPattern annot =
    match annot with
    | Pattern _ -> true
    | _ -> false

let rec findPatternlessQuantifiersInExpr (e : expr) =
    match e with
    | Lst es -> List.collect findPatternlessQuantifiersInExpr es
    | Annot (a, e) -> findPatternlessQuantifiersInExpr e
    | Not e -> findPatternlessQuantifiersInExpr e
    | And es -> List.collect findPatternlessQuantifiersInExpr es
    | Or es -> List.collect findPatternlessQuantifiersInExpr es
    | Implies (e1, e2) -> findPatternlessQuantifiersInExpr e1 @ findPatternlessQuantifiersInExpr e2
    | Eq (e1, e2) -> findPatternlessQuantifiersInExpr e1 @ findPatternlessQuantifiersInExpr e2
    | Let (bindings, body) ->
        (List.collect (findPatternlessQuantifiersInExpr << snd) bindings) @
        findPatternlessQuantifiersInExpr body
    | Forall (_, Annot (annots, e)) when List.exists isPattern annots ->
        findPatternlessQuantifiersInExpr e
    | Forall _ -> [e]
    | Exists (_, Annot (annots, e)) when List.exists isPattern annots ->
        findPatternlessQuantifiersInExpr e
    | Exists _ -> [e]
    | _ -> []

let findPatternlessQuantifiersInStmt (s : stmt) =
    match s with
    | Assert e -> findPatternlessQuantifiersInExpr e
    | _ -> []

let write (s : string) = System.Console.WriteLine s

[<EntryPoint>]
let main argv =
    let inFile = argv.[0]
    let t = System.IO.File.ReadAllText(inFile)
    let stmts = parseSMT t
    let patternlessQuantifiers = List.collect findPatternlessQuantifiersInStmt stmts
    patternlessQuantifiers |> List.iter (write << string_of_sexp << sexp_of_expr)
    0
    
