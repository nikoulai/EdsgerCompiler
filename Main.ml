open Lexer
open Format
open Ast
open Semantic
open Codegen
open Llvm
open String

exception Error of string
let main =
  let i = Array.length Sys.argv in
  let argsl = Array.to_list Sys.argv in
  let o = List.exists (fun x -> x = "-o") argsl in
  let f = List.exists (fun x -> x = "-f") argsl in
  let i = List.exists (fun x -> x = "-i") argsl in
  let ast = List.exists (fun x -> x = "-ast") argsl in
  let name = List.find_opt (fun x -> Str.string_match (Str.regexp "[^.]*\.eds") x 0 ) argsl in
  let (chan,name) =

  if (not i && not f) then
  ( match name with
    | None ->  (raise (Error "wrong type source file given"))
    | Some name ->(
       Printf.printf "\n\n%s\n\n" name;
             let filename = String.sub name 0 ((String.length name) - 4 ) in (*remove .eds*)
       (open_in name,filename)

    )

    )
    else (stdin,"stdin")
  in
  try
    let lexbuf = Lexing.from_channel chan in
    (try
      Parser.start Lexer.e_lang lexbuf;
      let _ = if ast then print_ast !ast_tree else () in
      check_program !ast_tree;
      let llfile = (String.concat "" [name;".ll"]) in
      let immfile = (String.concat "" [name;".imm"]) in
      let sfile = (String.concat "" [name;".s"]) in
      let asmfile = (String.concat "" [name;".asm"]) in
      let a=    Codegen.codegen_main !ast_tree
        in print_module llfile Codegen.the_module;
      (*infer !ast_tree;*)
      let _ =if i then (Sys.command (String.concat "" ["cat ";llfile])) else 0 in
      let _ = if o then (Printf.printf "optimized"; (Sys.command (String.concat "" ["llc -O3 ";llfile])) )else (Sys.command (String.concat "" ["llc ";llfile])) in
      let _ =if f then (Sys.command (String.concat "" ["cat ";sfile])) else 0 in
      let _ = (Sys.command (String.concat "" ["clang++-6.0 -g ";sfile;" libs/edsger_lib/lib.a -o "; name])) in
      let _ = (Sys.command (String.concat "" ["mv  ";sfile;" ";asmfile; " && mv  ";llfile;" ";immfile])) in
      (* let status = Sys.command "llc llvm_code.ll && clang++-6.0 -g llvm_code.s libs/edsger_lib/lib.a -o out " in *)
      (* Printf.printf "status = %d\n" status; *)
      exit 0
    with
    | Parsing.Parse_error ->
       print_endline "Parse error";
       (* printf "Syntax Error: Ln %d.\n" !num_lines; *)
(*       exit 1
    | Terminate reason ->
       printf "Semantic Error: %s ...\n" reason;*)
       exit 1)
  with End_of_file ->
    close_in chan

(*let main () =
    try
        let lexbuf = Lexing.from_channel stdin in
        while true do
            Parser.program Lexer.e_lang lexbuf
        done
    with End_of_file -> exit 0
let _ = Printexc.print main ()
*)
