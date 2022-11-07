module Util
open SMTLib

let takeWhere (f : 'a -> bool) (l : 'a list) =
    let rec takeWhere' l acc =
        match l with
        | x :: l' when f x -> takeWhere' l' (x :: acc)
        | _ -> (List.rev acc, l)
    takeWhere' l []

let permute seed l =
    let R = System.Random(seed)
    l |> List.map (fun x -> (x, R.NextDouble())) |> List.sortBy snd |> List.map fst

let prepend a l =
    a :: l

let split f l =
    let rec split' splits current remaining =
        match remaining with
        | x :: xs when f x ->
            split' ((List.rev current) :: splits) [] xs
        | x :: xs ->
            split' splits (x :: current) xs
        | [] ->
            if List.isEmpty current then
                List.rev splits
            else
                List.rev ((List.rev current) :: splits)
    split' [] [] l

let join (sep : 'a) (l : 'a list list) =
    if List.length l < 2 then
        List.concat l
    else
        (List.head l) @ (List.tail l |> List.map (fun sl -> sep :: sl) |> List.concat)

let last l =
    match l with
    | [] -> raise System.ArgumentException("Empty list")
    | [x] -> x
    | x :: xs -> last xs

let is_reset s =
    match s with
    | Reset -> true
    | _ -> false
