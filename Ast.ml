open Format
open Types

type ast_declaration = Vardecl of ast_type * (ast_declarator list)
                    | Fundecl of ast_res_type * string * (ast_param list)
                    | Fundefi of ast_res_type * string * (ast_param list) * (ast_declaration list) * (ast_stmt list)               
and ast_declarator =  Decl of string * ast_expr option
and ast_param = Param of ast_type * string
              | ParamByRef of ast_type * string
and ast_stmt = Snull
             | Sexpr of ast_expr
             | Slist of ast_stmt list
             | Sif of ast_expr * ast_stmt * ast_stmt option
             | Sfor of (string ) * (ast_expr option) * (ast_expr option) * (ast_expr option)  * ast_stmt
             | Scont of string
             | Sbrk of string
             | Sreturn of ast_expr option
and ast_expr = Eid of string
             | Ebool of bool
             | Enull
             | Eint of int
             | Echar of string
             | Edoub of float
             | Estr of string
             | Eapp of string * ast_expr list
             | Eunop of ast_expr * ast_unop
             | Eunas of ast_expr * ast_unas
             | Eunas1 of ast_expr * ast_unas
             | Ebop of ast_expr * ast_expr * ast_bop
             | Ebas of ast_expr * ast_expr * ast_bas
             | Ecast of ast_type * ast_expr
             | Enew of ast_type * ast_expr
             | Edel of ast_expr
             | Emat of ast_expr * ast_expr
             | Eif of ast_expr * ast_expr * ast_expr
and ast_unop = Tuamp
             | Tutim
             | Tupl
             | Tumin
             | Tunot
and ast_unas = Tppl 
             | Tmmin
and ast_bop = Tbtim
             | Tbdiv
             | Tbmod
             | Tbpl
             | Tbmin
             | Tblss
             | Tbgrt
             | Tbleq
             | Tbgeq
             | Tbeq 
             | Tbneq
             | Tband
             | Tbor
             | Tbcom
and ast_bas = Tba
             | Tbatim
             | Tbadiv
             | Tbamod
             | Tbapl
             | Tbamin
and ast_res_type = ast_type             
(*and ast_res_type = Tvoid
                 | Ttype of ast_type             *)
and ast_type = Types.typ
(*and ast_type = Tint
              | Tchar
              | Tbool
              | Tdouble
              | Tptr of ast_type
*)

let ast_tree : (ast_declaration list) option ref = ref None

(* Pretty Prints the AST *)

let rec print_ast_program ppf ast =
  match ast with
  | []    -> 
    ()
  | h::[] -> 
    print_ast_declaration ppf h
  | h::t  -> 
    print_ast_declaration ppf h;
    print_newline ();
    print_newline ();
    print_ast_program ppf t

and print_ast_declaration ppf ast =
  match ast with
  | Vardecl (typ, decls) ->
  fprintf ppf "  Vardecl ";
    print_ast_type ppf typ;
    print_ast_declarators ppf decls;
    force_newline ();
  | Fundecl (typ, name, params) ->
  fprintf ppf "  Fundecl ";
    print_ast_res_type ppf typ;
    fprintf ppf "%s (" name;
    print_ast_params ppf params;
    fprintf ppf ")";
    force_newline ();
  | Fundefi (typ, name, params, decls, stmts) ->
  fprintf ppf "  Fundefi ";
    print_ast_res_type ppf typ;
    fprintf ppf "%s (" name;
    print_ast_params ppf params;
    fprintf ppf ")";
    force_newline ();
    fprintf ppf "{";
    force_newline ();
    open_hovbox 2;
(*     fprintf ppf "  decls ";
 *)    print_ast_program ppf decls;
    force_newline ();
    print_ast_stmts ppf stmts;
    close_box ();
    force_newline ();
    fprintf ppf "}"

and print_ast_declarators ppf vars =
  match vars with
  | [] ->
    ();
  | [var] ->
    print_ast_declarator ppf var;
  | var::rest ->
    print_ast_declarator ppf var;
    fprintf ppf ", ";
    print_ast_declarators ppf rest

and print_ast_declarator ppf var =
  match var with
  | Decl (name, maybe_expr) ->
    fprintf ppf "  Decl ";

    fprintf ppf "%s" name;
    (match maybe_expr with
       | None -> ()
       | Some i ->
        fprintf ppf "[";
        print_ast_expr ppf i;
        fprintf ppf "]";
    )

and print_ast_params ppf params =
  match params with
  | [] ->
    ()
  | [param] ->
    print_ast_param ppf param
  | param::rest ->
    print_ast_param ppf param;
    fprintf ppf ", ";
    print_ast_params ppf rest

and print_ast_param ppf ast =
  match ast with
  | Param (typ, name) ->
    fprintf ppf "  Param";

    print_ast_type ppf typ;
    fprintf ppf "%s" name
  | ParamByRef (typ, name) ->
    fprintf ppf " ParamByRef ";

    print_ast_type ppf typ;
    fprintf ppf "byref %s" name

and print_ast_stmts ppf stmts =
  match stmts with
  | [] ->
    ()
  | [stmt] ->
    print_ast_stmt ppf stmt
  | stmt::rest ->
    print_ast_stmt ppf stmt;
    force_newline ();
    print_ast_stmts ppf rest

and print_ast_stmt ppf stmt =
  match stmt with
   | Snull -> fprintf ppf "Snull ";fprintf ppf ";";
   | Sexpr expr ->fprintf ppf " Sexpr "; print_ast_expr ppf expr ;
   | Slist stmts -> fprintf ppf " Slist "; print_ast_stmts ppf stmts
   (*check stmt option*)
   | Sif (expr, stmt, maybe_stmt) ->
   fprintf ppf " Sif";
    fprintf ppf "if (";
    print_ast_expr ppf expr;
    fprintf ppf ") then ";
    print_ast_stmt ppf stmt;
    (match maybe_stmt with
     | None -> ()
     | Some else_stmt ->
      force_newline ();
      fprintf ppf "else ";
      print_ast_stmt ppf else_stmt;
      close_box ();
    )
   | Sfor (maybe_var, expr1, expr2,expr3,stmt) ->
   fprintf ppf " Sfor ";
    (* (match maybe_var with
         | None -> fprintf ppf "NO LABEL";
         | Some var  -> fprintf ppf "%s" var;
        ) *)
    fprintf ppf "%s" maybe_var;
    fprintf ppf ": for (";
    (match expr1 with
     | None -> ()
     | Some exp-> 
      print_ast_expr ppf exp;
    );
    fprintf ppf ";";
    (match expr2 with
     | None -> ()
     | Some exp-> 
      print_ast_expr ppf exp;
    );
    fprintf ppf ";";
    (match expr3 with
     | None -> ()
     | Some exp-> 
      print_ast_expr ppf exp;
    );
    fprintf ppf " )";
    force_newline ();
    open_hovbox 2;
    print_ast_stmt ppf stmt;
    close_box ();
   | Scont i -> fprintf ppf " Scont "; fprintf ppf "continue %s" i;
   | Sbrk i -> fprintf ppf " Sbrk";  fprintf ppf "break %s" i;
   | Sreturn expr -> 
   fprintf ppf " Sreturn"; 
    fprintf ppf "return ";
     (match expr with
     | None -> ()
     | Some exp-> 
      print_ast_expr ppf exp;
    );

and print_ast_expr ppf ast =
  match ast with
  | Eid name ->
  fprintf ppf "Eid "; 
    fprintf ppf "%s" name
  | Ebool b ->
  fprintf ppf " Ebool"; 
    fprintf ppf "%b" b
  | Enull ->
  fprintf ppf "Enull "; 
    fprintf ppf "NULL"
  | Eint i ->
  fprintf ppf " Eint"; 
    fprintf ppf "%d" i
  | Echar i ->
  fprintf ppf " Echar"; 
    fprintf ppf "%s" i
  | Edoub i ->
  fprintf ppf "Edoub "; 
    fprintf ppf "%f" i
  | Estr i ->
  fprintf ppf " Estr"; 
    fprintf ppf "%s" i
  | Eapp (name, exprs) ->
  fprintf ppf "Eapp "; 
    fprintf ppf "%s (" name;
    print_ast_actual_params ppf exprs;
    fprintf ppf ")";
  | Eunop (expr, unop) ->
  fprintf ppf "Eunop "; 
    print_ast_unop ppf unop;
    print_ast_expr ppf expr;
  | Eunas (expr, unas) ->
  fprintf ppf " Eunas"; 
    print_ast_unas ppf unas;
    print_ast_expr ppf expr;
  | Eunas1 (expr, unas) ->
  fprintf ppf "Eunas1 "; 
    print_ast_expr ppf expr;
    print_ast_unas ppf unas;
  | Ebop (expr1, expr2, bop) ->
  fprintf ppf "Ebop "; 
    print_ast_expr ppf expr1;
    print_ast_bop ppf bop;
    print_ast_expr ppf expr2;
  | Ebas (expr1, expr2, bas) ->
  fprintf ppf " Ebas"; 
    print_ast_expr ppf expr1;
    print_ast_bas ppf bas;
    print_ast_expr ppf expr2;
  | Ecast (typ, expr) ->
  fprintf ppf " Ecast"; 
    fprintf ppf "(";
    print_ast_type ppf typ;
    fprintf ppf ") ";
    print_ast_expr ppf expr;
  | Enew (typ, expr) ->
    fprintf ppf "NEW ";
    print_ast_type ppf typ;
    print_ast_expr ppf expr;
  | Edel expr ->
    fprintf ppf "DELETE ";
    print_ast_expr ppf expr;
  | Emat (expr1, expr2) ->
  fprintf ppf " Emat"; 
    print_ast_expr ppf expr1;
    fprintf ppf "[";
    print_ast_expr ppf expr2;
    fprintf ppf "] ";
  | Eif (expr1, expr2, expr3) ->
  fprintf ppf "Eif "; 
    print_ast_expr ppf expr1;
    fprintf ppf " ? ";
    print_ast_expr ppf expr2;
    fprintf ppf " : ";
    print_ast_expr ppf expr3;

and print_ast_actual_params ppf exprs =
  match exprs with
  | [] ->
    ()
  | [expr] ->
    print_ast_expr ppf expr
  | expr::rest ->
    print_ast_expr ppf expr;
    fprintf ppf ", ";
    print_ast_actual_params ppf rest

and print_ast_unop ppf unop =
    match unop with 
    | Tuamp ->
    fprintf ppf " Tuamp"; 
      fprintf ppf " &";
    | Tutim ->
    fprintf ppf " Tutim"; 
      fprintf ppf " *";
    | Tupl -> 
    fprintf ppf "Tupl "; 
      fprintf ppf " +";
    | Tumin ->
    fprintf ppf "Tumin "; 
      fprintf ppf " -";
    | Tunot ->
    fprintf ppf "Tunot "; 
      fprintf ppf " !";
    ;

and print_ast_unas ppf unas =
   match unas with
   | Tppl -> 
          fprintf ppf " ++ ";
   | Tmmin ->
          fprintf ppf " -- "; 
    ;      

and print_ast_bas ppf bas =
  match bas with
    | Tba  ->
       fprintf ppf " = ";
    | Tbatim  ->
       fprintf ppf " *= ";
    | Tbamod  ->
    fprintf ppf " %%";
    fprintf ppf "= ";
    | Tbapl ->
    fprintf ppf " +=";
    | Tbamin  ->
    fprintf ppf " -= ";
    | Tbadiv -> 
    fprintf ppf " /= ";
    

and print_ast_bop ppf ast =
  match ast with
   | Tbtim ->   fprintf ppf " * ";
   | Tbdiv ->   fprintf ppf " / ";
   | Tbmod ->   fprintf ppf " %% ";
   | Tbpl ->   fprintf ppf " + ";
   | Tbmin ->   fprintf ppf " - ";
   | Tblss ->   fprintf ppf " < ";
   | Tbgrt ->   fprintf ppf " > ";
   | Tbleq ->   fprintf ppf " <= ";
   | Tbgeq ->   fprintf ppf " >= ";
   | Tbeq ->   fprintf ppf " = "; 
   | Tbneq ->   fprintf ppf " != ";
   | Tband ->   fprintf ppf " && ";
   | Tbor ->   fprintf ppf " || ";
   | Tbcom ->   fprintf ppf " , ";


and print_ast_type ppf ast =
  match ast with
  | Tint ->   fprintf ppf "int ";
  | Tchar ->   fprintf ppf "char ";
  | Tbool ->   fprintf ppf "bool ";
  | Tdouble ->   fprintf ppf "double ";
  | Tptr (typ1) ->   print_ast_type ppf typ1; fprintf ppf "*";

and print_ast_res_type ppf ast =
  print_ast_type ppf ast
(*  match ast with
  | Tvoid ->   fprintf ppf "void ";
  | Ttype typ ->   print_ast_type ppf typ;
*)


and pretty_print ppf ast =
   match ast with
   | None ->
      eprintf "%s@." "AST is empty"
   | Some tree ->
      print_ast_program ppf tree

let print_ast ast_tree = 
  force_newline ();
  printf "*** Pretty Printing AST ***";
  force_newline ();
  printf "***************************";
  force_newline ();
  printf "%a" pretty_print ast_tree;
  force_newline ()
