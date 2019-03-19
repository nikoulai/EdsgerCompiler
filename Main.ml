open Lexer
open Format
open Ast
open Semantic
open Codegen
open Llvm

let main =
  let chan =
    (if Array.length Sys.argv > 1 then
       open_in Sys.argv.(1)
    else
       stdin) in
  try
    let lexbuf = Lexing.from_channel chan in
    (try
      Parser.start Lexer.e_lang lexbuf;
      print_ast !ast_tree;
      check_program !ast_tree;
      let a=    Codegen.codegen_main !ast_tree
        in print_module ("llvm_code.ll") Codegen.the_module;
      (*infer !ast_tree;*)
      let status = Sys.command "llc llvm_code.ll && clang++-6.0 -g llvm_code.s libs/edsger_lib/lib.a -o out " in
      (* Printf.printf "status = %d\n" status; *)
      exit 0
    with
    | Parsing.Parse_error ->
       print_endline "Parse error";
       (*printf "Syntax Error: Ln %d.\n" !num_lines;*)
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
