open Ostap

let parse infile =
  let s = Util.read infile in
  Util.parse
    (object
       inherit Matcher.t s
       inherit Util.Lexers.decimal s
       inherit Util.Lexers.string s
       inherit Util.Lexers.char   s
       inherit Util.Lexers.ident ["skip";
                                  "if"; "then"; "else"; "elif"; "fi";
                                  "while"; "do"; "od";
                                  "repeat"; "until";
                                  "for";
                                  "fun"; "local"; "return";
                                  "length";
                                  "case"; "of"; "esac"; "when"] s
       inherit Util.Lexers.skip [
         Matcher.Skip.whitespaces " \t\n";
         Matcher.Skip.lineComment "--";
         Matcher.Skip.nestedComment "(*" "*)"
       ] s
     end
    )
    (ostap (!(Language.parse) -EOF))

let main =
  try
    let interpret  = Sys.argv.(1) = "-i"  in
    let stack      = Sys.argv.(1) = "-s"  in
    let to_compile = not (interpret || stack) in
    let infile     = Sys.argv.(if not to_compile then 2 else 1) in
    let proceed (prog : Language.t) =
            (*Printf.eprintf "parsed!\n";*)
            if to_compile
            then
              let basename = Filename.chop_suffix infile ".expr" in
              ignore @@ X86.build prog basename
            else
              let rec read acc =
                try
                  let r = read_int () in
                  Printf.printf "> ";
                  read (acc @ [r])
                with End_of_file -> acc
              in
              let input : int list = read [] in
              let output =
                if interpret
                then Language.eval prog input
                else SM.run (SM.compile prog) input
              in
              List.iter (fun i -> Printf.printf "%d\n" i) output in
    match (*Stdlib.time "parse"*) parse infile with
        | `Ok (prog : Language.t) -> (*Stdlib.time "proceed"*) proceed prog
        | `Fail er -> Printf.eprintf "Syntax error: %s\n" er
  with Invalid_argument _ ->
    Printf.printf "Usage: rc [-i | -s] <input file.expr>\n"
