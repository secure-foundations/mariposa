module SMTLib.Parse

open SMTLib
open Microsoft.FSharp.Text.Lexing

let parseSMT (s : string) : stmt list =
    let lexbuf = LexBuffer<char>.FromString s
    lexbuf.EndPos <- lexbuf.EndPos.NextLine
    try
        SMTLibParser.start SMTLibLexer.tokenize lexbuf
        with e ->
            let pos = lexbuf.EndPos
            let line = pos.Line
            let column = pos.Column
            let message = e.Message
            let lastToken = new System.String(lexbuf.Lexeme)
            printf "Parse failed at line %d column %d; last token was %s; message is %s\n" line column lastToken message
            exit 1

