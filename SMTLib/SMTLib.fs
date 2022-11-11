namespace SMTLib
(* idents track 1) name and 2) name-for-printing *)
type ident = string * string

type value =
    | Int of bigint
    | Float of float
    | Bool of bool
    | String of string

type 'a annotation =
    | QId of ident
    | SkolemId of ident
    | Weight of bigint
    | Pattern of 'a list
    | NoPattern of 'a
    | LblPos of ident
    | LblNeg of ident
    | Named of ident

type expr =
    | Val of value
    | Id of ident
    | Lst of expr list
    | Annot of (expr annotation) list * expr
    | Not of expr
    | And of expr list
    | Or of expr list
    | Implies of expr * expr
    | Eq of expr * expr
    | Let of (ident * expr) list * expr
    | Forall of (ident * expr) list * expr
    | Exists of (ident * expr) list * expr

type stmt =
    | SetOption of string * expr
    | SetInfo of string * expr
    | GetInfo of string
    | DeclareSort of ident * bigint
    | DeclareFun of ident * expr list * expr
    | DefineFun of ident * (ident * expr) list * expr * expr
    | DeclareDatatypes of (expr list) * (ident * (ident * (ident * expr) list) list) list
    | Assert of expr
    | Push of bigint option
    | Pop of bigint option
    | CheckSat
    | GetUnsatCore
    | Reset
    | Labels
    | Echo of value
    | Eval of expr

