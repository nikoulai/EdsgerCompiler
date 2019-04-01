open Format
open Ast
open Symbol
(*open Symbtest*)
open Types
open Identifier
open Str
(*open TypeInference*)
open Error

exception Terminate
exception Terror of string
 let rec printType x= match x with
| Tarray _ -> Printf.printf "This is array\n";()
| Tdouble -> Printf.printf "This is dobule\n";()
| Tchar -> Printf.printf "This is char\n";()
| Tint -> Printf.printf "This is int\n";()
| Tbool -> Printf.printf "This is bool\n";()
| Tptr x1-> Printf.printf "This is a pointer of \n"; printType x1;()
| Tnone -> Printf.printf "This is none type \n"
| Tvoid -> Printf.printf "This is void type \n"

let get_entry_k entry = match entry.entry_info with
|ENTRY_function x -> x

let  getEntryType entr = match entr.entry_info with
|ENTRY_variable x -> x.variable_type
|ENTRY_function x -> x.function_result
|ENTRY_parameter x -> x.parameter_type
|ENTRY_temporary x -> x.temporary_type

let rec  getType expr = match expr with
        | Eid x ->  getEntryType (lookupEntry (id_make x) LOOKUP_ALL_SCOPES true) (*add some warning message*)
        |Ebool _ -> Tbool
        |Echar _ -> Tchar
        |Eint _ -> Tint
        |Edoub _ -> Tdouble
        |Estr x ->Tarray(Tchar,String.length x)
        |Enull -> Tnone
(*        |EPointer x -> Tptr (getType x)*)
        | Eunop (x, z) -> (match z with
          | Tuamp -> Tptr (getType x)
          | _ -> getType x
          )
        | Eunas (x,_) -> if (getType x) = Tint then Tint else (match (getType x) with
          |Tptr a -> Tptr a
          |_->  (error "++ -- needs integer"; Tnone) )
        | Ebop (x,y,z) -> (match z with
          | Tbpl ->if (y==Enull || x == Enull) then (error "Error in sum";Tnone)else  (match (getType x,getType y) with | (Tptr x1,Tint) -> Tptr x1
            | (Tint,x1) -> x1
            | (x1,Tint) ->x1
            | (Tdouble,x1) ->Tdouble
            | (x1,Tdouble) ->Tdouble
            | (Tchar,x1) ->Tchar
            | (x1,Tchar) ->Tchar
            | _ -> error "Type problem";Tnone (*I shall add something for char + char etc*)
            )

          | Tbmod -> (match (getType x,getType y) with
            | (Tint,Tint) ->  Tint
            | (Tptr (Tint),Tint) -> Tint
            | (Tint ,Tptr (Tint)) -> Tint
            | (Tptr (Tint) ,Tptr (Tint)) -> Tint
            | _ -> (*Types.printType (getType x);Types.printType (getType y);*)error "Mod needs integer and integer" ; Tnone
            )
          | Tblss | Tbgrt | Tbleq | Tbgeq | Tbeq | Tbneq -> (match (getType x,getType y) with
            | (Tint,Tint) | (Tint,Tdouble) | (Tdouble,Tint) | (Tdouble ,Tdouble) | (Tbool ,Tbool)  -> Tbool
            | (Tarray (x,_), Tarray (y,_) ) | (Tptr x,Tptr y)-> if equalType x y then Tbool else (error "from c11" ;Tnone)
            | (Tarray (x,_), y) | (Tptr x,y)-> if equalType x y then Tbool else (error "from c12" ;Tnone)
            | (y,Tarray (x,_)) | (y,Tptr x)-> if equalType x y then Tbool else (error "from c13" ;Tnone)
            | _ ->error "sigkrisi xriazete arithmous";Tnone)
          | Tband | Tbor -> (match (getType x,getType y) with
            | (Tbool ,Tbool) ->Tbool
            | _ -> printType (getType x); printType (getType y);error "type missimatch on boolean action" ; Tnone )
          | Tbcom -> getType y
          | _ -> (match (getType x,getType y) with | (Tptr x1,Tint) -> Tptr x1
            | (Tint,x1) -> x1
            | (x1,Tint) ->x1
            | (Tdouble,x1) ->Tdouble
            | (x1,Tdouble) ->Tdouble
            | (Tchar,x1) ->Tchar
            | (x1,Tchar) ->Tchar
            | _ -> error "Type problem";Tnone (*I shall add something for char + char etc*)
            )
          )
        | Ebas (x,y,z) -> (match z with
          | Tbamod -> (match (getType x,getType y) with
                | (Tint,Tint) ->  Tint
                | (Tptr (Tint),Tint) -> Tint
                | (Tint ,Tptr (Tint)) -> Tint
                | (Tptr (Tint) ,Tptr (Tint)) -> Tint
                | _ -> (*Types.printType (getType x);Types.printType (getType y);*)error "Mod needs integer and integer" ; Tnone
                )
          | _ -> (match (getType x,getType y) with
            | (Tptr x1,Tint) -> Tptr x1
            | (x,_) -> x (*need to check later*)
            | _ ->error "Tproblem";Tnone (*I shall add something for char + char etc*)
            )
          )
        | Ecast (x,y) -> if castAllow x (getType y) then x else getType y
        | Eif (x,y,z)-> if (getType x = Tbool) then (if equalType (getType y) (getType z) then getType y else (error "question type1"; Tnone )) else (print_string ("aaa\n");  printType (getType x);error "type error questionmark"; Tnone)
        | Enew (x,_) -> x
        | Edel _ -> Tnone
        | Emat (x,y) -> if ((getType y) = Tint) then Tptr (exprArray x) else( error "type error array call" ; Tnone)
        | Eapp (x,_) -> if (check_name_lib x) then get_name_lib x else (get_entry_k (lookupEntry (id_make x) LOOKUP_ALL_SCOPES true)).function_result
        | _ -> Tnone
and  castAllow x y = match (x,  y) with
| (Tdouble ,Tint)| (Tint,Tdouble) -> true
| (Tbool ,_) -> true
| (Tchar ,Tint) -> true
| (Tint,Tchar ) -> true
| (y1,y2) ->if equalType y1 y2 then true else false
| (_,_) -> false  (*cast*)
and  exprArray x = match getType x with
| Tptr x1 -> x1
| Tarray (x1,x2) ->x1
| _ -> error "not a memory"; Tnone
and check_name_lib name = match name with
|"writeString" | "writeInteger" |"writeBoolean" | "writeChar" | "writeReal" | "readInteger" | "readBoolean" | "readChar" | "readReal" | "readString" | "abs" | "fabs" | "sqrt" |"sin" | "cos" | "tan" | "atan" | "exp" | "ln" |"pi" | "trunc" | "round" | "ord"|"chr" | "strlen" | "strcmp"|"strcpy" | "strcat"->true
| _ -> false
and get_name_lib name = match name with
        |"writeString"  | "writeInteger" |"writeBoolean" | "writeChar" | "writeReal" -> Tvoid
        | "readInteger" -> Tint
        | "readBoolean" -> Tbool
        | "readChar"->Tchar
        | "readReal" -> Tdouble
        | "readString"->Tptr (Tchar)
         | "abs" -> Tint
         | "fabs" | "sqrt" |"sin" | "cos" | "tan" | "atan" | "exp" | "ln" |"pi" -> Tdouble
         | "trunc" | "round" -> Tint
         | "ord" -> Tint
         |"chr"-> Tchar
         | "strlen" ->Tint
         | "strcmp" ->Tbool
         |"strcpy"->Tvoid
         | "strcat"->Tvoid;;
(* to compile with Str we use str.cma in ocaml *)

let find_return =  ref false
let for_loop = ref 0

let rec  check_program t = match t with
  | None -> printf("empty");
  | Some tree ->  openScope Tvoid; check_declarations (tree); check_main(); closeScope ()

and  check_declarations t = match t with
  | [] -> ()
  | x::rest -> check_declaration x;
               check_declarations rest;

and check_declaration t = match t with
  | Vardecl (ty, decs) ->
     check_declarators ty decs;
  | Fundecl (ty, name, params)->
     let fun_name = name in (* stopping support of same name functions *)
     (* let suffix = add_suffix params in *)
     (* let fun_name = String.concat "" [name;"_"; suffix] in *)
     (* let _ = Printf.printf "adding fun dec %s\n" fun_name in *)
     let t = ( newFunction (id_make fun_name) true) in
     openScope(ty);
     ignore (List.map (registerParams t) params);
     ignore (endFunctionHeader t (ty));
     ignore (forwardFunction t);
     closeScope();
  | Fundefi (ty, name, params, decls, stms) ->
     let fun_name = name in (* stopping support of same name functions *)
     (* let suffix = add_suffix params in *)
     (* let fun_name = String.concat "" [name;"_"; suffix] in *)
     (* let _  = Printf.printf "adding %s\n" fun_name in *)
     let t = ( Symbol.newFunction (id_make fun_name) true) in (* t is fun entry (ty, t)=a, params *)
     ignore(openScope(ty));
     ignore(List.map (registerParams t) params);
     ignore(endFunctionHeader t (ty));
     check_declarations decls;
     (try check_statements stms with Terror _ -> raise (Terror ""));
     if (equalType (!currentScope.sco_type) (Tvoid)) && not ( !find_return) then (  find_return := false)
     else if( !find_return) then ( find_return := false;)  else Error.error "Couldn't find return in non void function" ;
     closeScope()


and check_declarators ty decs = match decs with
  | [] -> ()
  | [dec] -> check_declarator ty dec
  | dec :: rest -> check_declarator ty dec;
                   check_declarators ty rest

(* if we have an array we must have an int expression and the type of the array *)
and check_declarator ty dec = match dec with
  | Decl (name, maybe_expr) ->
    (match maybe_expr with
       | None ->
         ignore (newVariable (id_make name) ( ty) true);
       | Some exp ->
         if (equalType (getType exp) Tint) then
          ignore (newVariable (id_make name) (Tarray(ty,0)) true) (*we don't care for the size just typechecking... *)
         else Printf.printf "Error in array declaration"
    )

(*  t is the function entry aka t in our case *)
and registerParams t param  = match param with
  | Param (typ, name)->
     ignore (newParameter (id_make name) (typ) PASS_BY_VALUE t true)
  | ParamByRef (typ, name)->
     ignore (newParameter (id_make name) (typ) PASS_BY_REFERENCE t true)


and check_statements stms = match stms with
  | [] -> ()
  | stm :: rest ->
     let _ = try check_statement stm with Terror _ -> Printf.printf "\nThe Error was found here:\n"; printf "%a\n" print_ast_stmt stm; raise (Terror "") in
     check_statements rest;

and check_statement stm =
  match stm with
(*  | Sexpr None -> ()*)
(*  | Sexpr Some exp -> ignore (getType exp)*)
  | Sexpr exp -> ignore (getType exp)
  | Slist stm-> check_statements stm
  | Sif (exp, stm1,maybe_stmt) -> (match maybe_stmt with
    | None -> (let _ = try equalType (getType exp) Tbool with Terror _ -> raise (Terror "") in(* prepei na dei ama einai typoy bool i exp *)
        check_statement stm1;)
    | Some stm2 ->
      let _ = try equalType (getType exp) Tbool with Terror _ ->  raise (Terror "") in
      check_statement stm1;
      check_statement stm2;)
  | Sfor (tag,e1,e2,e3,s) ->
     (match e1 with
        None -> ()
       |Some e -> ignore (getType e)
   );
   (match e2 with
      None -> ()
     |Some e -> ignore (equalType (getType e) Tbool)
   );
   (match e3 with
      None -> ()
     |Some e -> ignore (getType e)
   );
   for_loop:= !for_loop +1;
   check_statement s;
   for_loop:= !for_loop - 1;
| Scont i | Sbrk i ->
   (* check_loop s1; (\* checks if we are in a loop *\) *)
   if (!for_loop == 0) then Error.error "Break or continue not inside a loop" else ()
| Sreturn ex ->
   (match ex with
    | None ->
       ignore (
         let typos = !currentScope.sco_type in
     check_fun_type (typos) (Tvoid))
    | Some expr ->
       ignore (check_fun_type (!currentScope.sco_type) (getType expr)));
(* ignore(Symbtest.printSymbolTable());    *)

and check_fun_type scope_typ typ =
  if (equalType scope_typ typ) then
    find_return := true
  else
    ( Printf.printf("Return type and function type are not the same\nReturned: ");
      (printType scope_typ);
      (printType typ);
      raise Terminate )

and check_main () =
  let main = lookupEntry (id_make "main") LOOKUP_CURRENT_SCOPE true in  (*look for main_ if you want tou support functions with same name ;) *)
  match main.entry_info with
  | ENTRY_function _ -> ()
  | _ -> Error.error "Couldn't find main function :("

(* Or simply add new function main and try to catch an exception? *)

(*and add_suffix param_list =
  let suffix = List.map (fun x -> match x with | Param (t,_) -> convert_tto_char t | ParamByRef (t,_) -> convert_tto_char t) param_list in String.concat "" suffix
*)
and print_expr e =
Printf.printf "\n!!\n";
 Printf.printf  (  match e with
                    Eid _  -> "Eid"
                    | Ebool _  -> "Ebool"
                    | Enull _ -> "Enull"
                    | Eint _  -> "Eint"
                    | Echar _  -> "Echar"
                    | Edoub _  -> "Edoub"
                    | Estr _  -> "Estr"
                   | Eapp _  -> "Eapp"
                   | Eunop _ -> "Eunop"
                   | Eunas _ -> "Eunas"
                   | Eunas1 _ -> "Eunas1"
                   | Ebop _  -> "Ebop"
                   | Ebas _ -> "Ebas"
                   | Ecast _ -> "Ecast"
                   | Enew _  -> "Enew"
                   | Edel _ -> "Edel"
                   | Emat _ -> "Emat"
                   | Eif _  -> "Eif"

                   );
