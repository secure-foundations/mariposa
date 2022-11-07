// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open SMTLib.Parse
open SMTLib.PrettyPrint
[<EntryPoint>]
let main argv  =
    let inFile = argv.[0]
    let outFile = argv.[1]
    let perturb = Perturb.parseArgs argv.[2..]
    let t = System.IO.File.ReadAllText(inFile)
    let inSMT2 = parseSMT t
    let outSMT2 = perturb inSMT2
    System.IO.File.WriteAllLines(outFile, outSMT2 |> List.map string_of_stmt)
    0
