open Llvm
open Ast
open Types
open Semantic
open Symbol
open Format
open ExpCodeGen

exception Error of string
let context = global_context ()
let the_module = ExpCodeGen.the_module
let builder =  ExpCodeGen.builder
let named_values:(string, llvalue) Hashtbl.t = ExpCodeGen.named_values
let integer_type  = i16_type context
let null_type = i1_type context
let bool_type = i8_type context
let char_type = i8_type context
let double_type = ExpCodeGen.double_type
let fun_names = ExpCodeGen.fun_names
let fun_bbs : llbasicblock list ref = ref []
let returns = ref true
let continue_tags : (string *llbasicblock) list ref = ref []
let break_tags : (string * llbasicblock ) list ref = ref []
let old_bindings : (string * llvalue) list ref = ref []
let global_decs : (Ast.ast_declaration) list ref = ref []

(* let context = global_context ()
let the_module = ExpCodeGen.the_module
let builder =  ExpCodeGen.builder
type binary_ops = Plus|Minus|Div|Mult|Mod|And|Or|Comma|Lt|Lte|Eq|Neq|Gt|Gte
let context = global_context ()
let named_values:(string, llvalue) Hashtbl.t = ExpCodeGen.named_values
let integer_type  = i16_type context
let null_type = i1_type context
let bool_type = i8_type context
let char_type = i8_type context
let fun_bbs : llbasicblock list ref = ref []
let returns = ref true
let continue_tags : (string *llbasicblock) list ref = ref []
let break_tags : (string * llbasicblock ) list ref = ref []
let old_bindings : (string * llvalue) list ref = ref []
let global_decs : (Ast.ast_declaration) list ref = ref []
type environment = Global of (string list)| Nested of (string list * environment)
module SS = Set.Make(String)
let context = global_context ()
let int_type = i16_type context
let double_type = ExpCodeGen.double_type
let fun_names = ExpCodeGen.fun_names
let char_type = i8_type context
let bool_type = i8_type context
let env:environment ref = ref (Global ([]))
let global_decs : (Ast.ast_declaration) list ref = ref [] *)


(* open Llvm
open Ast
open Types
open Semantic
open Symbol
open Format



(* let create_entry_block_alloca func var_name =
        let builder =builder_at (instr_begin (entry_block func)) in
        build_alloca (var_type ) var_name builder

        (* | Tproc -> ltype_of_type Tvoid *)
let default_val_type smth = match smth with
        | Tint ->  const_int (ltype_of_type smth) 0
        | Tbool -> cont_int (ltype_of_type smth) 0
        | Tchar -> cont_int (ltype_of_type smth) 0
        | Tdouble -> const_float (ltype_of_type smth) 0.0
        | Tvoid -> const_int (ltype_of_type smth) 0
let rec codegen_stmt stmt builder= match stmt with
        SExpr (Some a) ->  codegen_expr a
        (* |SNewblock a -> List.map (codegen_stmt builder) a *)
        |Sfor (a,b,c,d,e) -> codegen_for_loop a b c d e builder
        |Sif (a,b,c) -> let fanc = let lval =  codegen_expr a builder in
        let cond_val = build_fcmp Fcmp.One lval (const_float (ltype_of_type TYPE_double) 0.0) "ifcond" builder in
        let start_bb = insertion_block builder in
        let the_function =block_parent start_bb in
        let then_bb =append_block context "then" the_function in
        position_at_end then_bb builder;
        let then_val =codegen_stmt b in
        let new_then_bb =insertion_block builder in
        let else_bb = append_block context "else" the_function in
        position_at_end else_bb builder;
        let else_val1 = Option.map codegen_stmt c in
        let else_val = if Option.is_some else_val1 then Option.get else_val1 else codegen_expr (Enull) in
        let new_else_bb =insertion_block builder in
        let merge_bb= append_block context "ifcond" the_function in
        position_at_end merge_bb builder;
        let incoming = [(then_val,new_then_bb);(else_val,new_else_bb)] in
        let phi = build_phi incoming "iftmp" builder in
        position_at_end start_bb builder;
        ignore(build_cond_br cond_val then_bb else_bb builder);
        position_at_end new_then_bb bulder; ignore(build_br merge_bb builder);
        position_at_end new_else_bb bulder; ignore(build_br merge_bb builder);
        phi in fanc
        |Sreturn (Some a) -> build_ret (codegen_expr a builder) builder
        |Sreturn _ -> build_ret_void builder
        (* |SBreak (Some a) -> *)
        (* |SCont (Some a) -> *)
        (* |SBreak _ ->
        |Scont _ -> *)
        |_ -> codegen_expr (Enull) builder;; *)
(* and codegen_for_loop *)
(* and let rec codegen_expr builder= match expr with
        |Eid a ->let v= try Hashtbl.find named_values a with |Not_found -> raise (Error "uknown variable name") in build_load v name builder
        |Ebool a -> const_int (ltype_of_type Tbool) (if a then 1 else 0)
        |Enull -> (*NOP *)
        |Eint a -> const_int (ltype_of_type Tint) a
        |Echar a -> const_int (ltype_of_type Tchar) (Char.to_int a)
        |Edoub a -> const_float (ltype_of_type Tdouble) a
        |Estr a-> build_global_stringptr s "tmp" builder
and let rec codegen_expr builder= match expr with
        |Eid a ->let v= try Hashtbl.find named_values a with |Not_found -> raise (Error "uknown variable name") in build_load v name builder
        |Ebool a -> const_int (ltype_of_type Tbool) (if a then 1 else 0)
        |Enull -> (*NOP *)
        |Eint a -> const_int (ltype_of_type Tint) a
        |Echar a -> const_int (ltype_of_type Tchar) (Char.to_int a)
        |Edoub a -> const_float (ltype_of_type Tdouble) a
        |Estr a-> build_global_stringptr s "tmp" builder
        (* |Tuamp a -> *)
        (* |Tutim a->
         |Tupl a-> *)
        |Tumin a -> let lval = codegen_expr a builder in let type_is = (* type get*)
                                in let type_m m= match m  with
                                TYPE_int -> build_neg lval "int_unoptmp" builder
                                | TYPE_double -> build_fneg lval "flt_unotmp" builder
                                in type_m type_is
        |Tbtim (a,b) -> codegen_binary a b Mult builder
        |Tbdiv (a,b) ->codegen_binary a b Div builder
        |Tbmod (a,b) -> codegen_binary a b Mod builder
        |Tbpl (a,b) -> codegen_binary a b Plus builder
        |Tbmin (a,b) -> codegen_binary a b Minus builder
        |Tblss (a,b) -> codegen_expr a b Lt builder
        |Tbgrt (a,b) -> codegen_expr a b Gt builder
        |Tbleq (a,b) -> codegen_expr a b Lte builder
        |Tbgeq (a,b) -> codegen_expr a b Gte builder
        |Tbeq (a,b) -> codegen_expr a b Eq builder
        |Tbneq a -> let lval = codegen_expr a builder in build_not lval "nottmp" builder
        |Tband (a,b) -> codegen_binary a b And builder
        |Tbor (a,b) -> codegen_binary a b Or builder
        |Tbcom (a,b) -> codegen_binary a b Comma builder
        |Tppl (a,b)->
        |Tmmin (a,b)->
        |EAssignEq (a,b)-> codegen_assign (codegen_expr a builder) (codegen_expr b builder) builder
        |Tbapl (a,b) -> let value = codegen_expr Tbpl (a,b) builder in codegen_assign (codegen_expr a builder ) value builder
        |Tbamin (a,b) -> let value = codegen_expr Tbmin(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbadiv (a,b) -> let value = codegen_expr Tbdiv (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbatim (a,b) -> let value = codegen_expr Tbtim (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbamod (a,b) -> let value = codegen_expr Tbmod (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Enew (a,b) ->
        |Edel a ->
        |Ecast (a,b)->
        |Eapp
        |ECall
        |Tarray (a,b)
and let rec codegen_assign e1 e2 =


and let rec codegen_binary e1 e2 expr  builder=
        let type1 =  in
        let type2 =  in
        let e1n = codegen_expr e1 builder in
        let e2n = codegen_expr e2  builder in
        let int_fun expr = match expr with
                Plus -> build_add e1n e2n "addtmp" builder
                |Minus ->build_sub e1n e2n "subtmp" builder
                |Div ->build_sdiv e1n e2n "divtmp" builder
                |Mult ->build_mul e1n e2n "multmp" builder
                |Mod -> build_srem e1n e2n "sremtmp" builder
                |And -> build_and e1n e2n "andtmp" builder
                |Or -> build_or e1n e2n "ortmp" builder
                |Lt ->build_icmp Icmp.Slt e1n e2n "lttmp" builder
                |Lte ->build_icmp Icmp.Sle e1n e2n "ltetmp" builder
                |Gt -> build_icmp Icmp.Sgt e1n e2n "gttmp" builder
                |Gte -> build_icmp Icmp.Sge e1n e2n "gtetmp" builder
                |Eq -> build_icmp Icmp.Eq e1n e2n "equaltmp" builder
        in
        let float_fun expr = match expr with
                Plus -> build_fadd e1n e2n "addtmp" builder
                |Minus ->build_fsub e1n e2n "subtmp" builder
                |Div ->build_fsdiv e1n e2n "divtmp" builder
                |Mult ->build_fmul e1n e2n "multmp" builder
                |Mod -> build_fsrem e1n e2n "sremtmp" builder
                |Lt ->build_ficmp Icmp.Slt e1n e2n "lttmp" builder
                |Lte ->build_ficmp Icmp.Sle e1n e2n "ltetmp" builder
                |Gt -> build_ficmp Icmp.Sgt e1n e2n "gttmp" builder
                |Gte -> build_ficmp Icmp.Sge e1n e2n "gtetmp" builder
                |Eq -> build_ficmp Icmp.Eq e1n e2n "equaltmp" builder
        in
            if () int_fun expr else flaot_fun expr ;;
        (* |Tuamp a -> *)
        (* |Tutim a->
         |Tupl a-> *)
        |Tumin a -> let lval = codegen_expr a builder in let type_is = (* type get*)
                                in let type_m m= match m  with
                                TYPE_int -> build_neg lval "int_unoptmp" builder
                                | TYPE_double -> build_fneg lval "flt_unotmp" builder
                                in type_m type_is
        |Tbtim (a,b) -> codegen_binary a b Mult builder
        |Tbdiv (a,b) ->codegen_binary a b Div builder
        |Tbmod (a,b) -> codegen_binary a b Mod builder
        |Tbpl (a,b) -> codegen_binary a b Plus builder
        |Tbmin (a,b) -> codegen_binary a b Minus builder
        |Tblss (a,b) -> codegen_expr a b Lt builder
        |Tbgrt (a,b) -> codegen_expr a b Gt builder
        |Tbleq (a,b) -> codegen_expr a b Lte builder
        |Tbgeq (a,b) -> codegen_expr a b Gte builder
        |Tbeq (a,b) -> codegen_expr a b Eq builder
        |Tbneq a -> let lval = codegen_expr a builder in build_not lval "nottmp" builder
        |Tband (a,b) -> codegen_binary a b And builder
        |Tbor (a,b) -> codegen_binary a b Or builder
        |Tbcom (a,b) -> codegen_binary a b Comma builder
        |Tppl (a,b)->
        |Tmmin (a,b)->
        |EAssignEq (a,b)-> codegen_assign (codegen_expr a builder) (codegen_expr b builder) builder
        |Tbapl (a,b) -> let value = codegen_expr Tbpl (a,b) builder in codegen_assign (codegen_expr a builder ) value builder
        |Tbamin (a,b) -> let value = codegen_expr Tbmin(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbadiv (a,b) -> let value = codegen_expr Tbdiv (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbatim (a,b) -> let value = codegen_expr Tbtim (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Tbamod (a,b) -> let value = codegen_expr Tbmod (a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Enew (a,b) ->
        |Edel a ->
        |Ecast (a,b)->
        |Eapp
        |ECall
        |Tarray (a,b)
and let rec codegen_assign e1 e2 =


and let rec codegen_binary e1 e2 expr  builder=
        let type1 =  in
        let type2 =  in
        let e1n = codegen_expr e1 builder in
        let e2n = codegen_expr e2  builder in
        let int_fun expr = match expr with
                Plus -> build_add e1n e2n "addtmp" builder
                |Minus ->build_sub e1n e2n "subtmp" builder
                |Div ->build_sdiv e1n e2n "divtmp" builder
                |Mult ->build_mul e1n e2n "multmp" builder
                |Mod -> build_srem e1n e2n "sremtmp" builder
                |And -> build_and e1n e2n "andtmp" builder
                |Or -> build_or e1n e2n "ortmp" builder
                |Lt ->build_icmp Icmp.Slt e1n e2n "lttmp" builder
                |Lte ->build_icmp Icmp.Sle e1n e2n "ltetmp" builder
                |Gt -> build_icmp Icmp.Sgt e1n e2n "gttmp" builder
                |Gte -> build_icmp Icmp.Sge e1n e2n "gtetmp" builder
                |Eq -> build_icmp Icmp.Eq e1n e2n "equaltmp" builder
        in
        let float_fun expr = match expr with
                Plus -> build_fadd e1n e2n "addtmp" builder
                |Minus ->build_fsub e1n e2n "subtmp" builder
                |Div ->build_fsdiv e1n e2n "divtmp" builder
                |Mult ->build_fmul e1n e2n "multmp" builder
                |Mod -> build_fsrem e1n e2n "sremtmp" builder
                |Lt ->build_ficmp Icmp.Slt e1n e2n "lttmp" builder
                |Lte ->build_ficmp Icmp.Sle e1n e2n "ltetmp" builder
                |Gt -> build_ficmp Icmp.Sgt e1n e2n "gttmp" builder
                |Gte -> build_ficmp Icmp.Sge e1n e2n "gtetmp" builder
                |Eq -> build_ficmp Icmp.Eq e1n e2n "equaltmp" builder
        in
            if () int_fun expr else flaot_fun expr ;; *)



(* let make_function func1 = match func1 with FunDef (func,b,c) ->
        let name = func.entry_id in
        let f = Option.get (lookup_function name the_module) in
        let builder = builder_at_end context (entry_block f) in
        let params = ... in
        let _  = List.map codegen_stmt c builder in
        let last= match block_end f with After (block) -> block in
        let return= return_type (type_of f) in
        match (instr_end last) with
        After(ins)-> if ((instr_opcode ins) = Opcode.Ret) then ()
        else
                if return =(void_type context )  then ignore (build_ret_void); else
                        ignore(build_ret (default_val_type TYPE_int) builder)
       |At_start(_) ->
                if return =(void_type context )  then ignore (build_ret_void); else
                        ignore(build_ret (default_val_type TYPE_int) builder);; *)


(* let getAdreess expr builder =  match expr with
 Eid(x) ->  findinHash x
 |EAmber (x)->  let y = findinHash x in
        let dereference = build_struct_gep y 0 "tmp" in build_load dereference "tmp" builder
 |EPointer (x)-> let y = findinHash x in let load_ = build_load y "temp" builder in
        let dereference = build_struct_gep load_ 0 "tmp" in dereference
 |EArray(x,y) -> let index = codegen_expr y builder in  let tmp_val = findinHash x in
 let dereference = build_gep tmp_val  [|0;index|] "arrayval" builder in dereference *)

let rec ltype_of_type = function
       | Tint ->  i32_type context
       | Tchar -> i8_type context
       | Tbool -> i1_type context
       | Tdouble -> double_type context
       | Tptr t -> pointer_type (ltype_of_type t)
       | Tarray (a,b) -> array_type (ltype_of_type a) b
       | Tvoid -> void_type context

(*  check if there is main function*)
let rec codegen_main main =
  match main with
  | Some prog -> List.iter seperate prog
  | None -> Printf.printf "Codegen: No program found"

and seperate prog =
  match prog with
  | Vardecl (typ, decls) ->
  print_endline  "  Vardecl ";
  | Fundecl (typ, name, params) ->
    codegen_func typ name params ;
  | Fundefi (typ, name, params, decls, stmts) ->
  print_endline  "  Fundefi ";
(*
and codegen_func typ name params =
          let parametres = List.map (fun x-> ltype_of_type x.parameter_info.parameter_type) (func.function_info.function_paramlist) in
          let fuction_type = function_type (ltype_of_type func.parameter_info.function_result) (Array.of_list parametres) in
          define_function name function_type the_module ;; *)

  and codegen_func func =
        let name = String.concat "_" (func.entry_id::!fun_names)  in
        if (Hashtbl.mem functions name) then Hashtbl.find functions name else (
        let parametres = List.map (fun x-> let y = ltype_of_type (get_parameter_f x.parameter_info).parameter_type
        in
        match ((get_parameter_f x.parameter_info).parameter_mode ) with
        | PASS_BY_REFERENCE -> pointer_type y
        | _ -> y
        ) ((get_fuction_f func.parameter_info).function_paramlist) in
        let fuction_type = function_type (ltype_of_type (get_fuction_f func.parameter_info).function_result) (Array.of_list parametres) in
        let b=  declare_function name fuction_type the_module in
        let _ = Hashtbl.add functions name b in b)
        and param_type x = (fun y-> let z = ltype_of_type (get_parameter_f y.parameter_info).parameter_type in match ((get_parameter_f y.parameter_info).parameter_mode ) with
        | PASS_BY_REFERENCE -> pointer_type z
        | _ -> z) x

        and make_function func1 = match func1 with FunDef (func,b,c) ->
        let name = func.entry_id  in
    	let fn_name = String.concat "_" (name::!fun_names) in
    	let parameters = (get_fuction_f func.parameter_info).function_paramlist in
    	let parameters_old =  (get_fuction_f func.parameter_info).function_paramlist in
     	env:= Nested([],!env);
     	let env_params = difference_with_env !env parameters in
     	update_env_with_params parameters !env;
     (* let _ = print_env_pars !env in *)
        let _ = Hashtbl.add functions_params name (List.map (fun x-> Eid(x)) env_params) in
     	let env_params_types =get_env_params_types env_params  in
     (* let _ = print_hashtbl named_values in *)
        let llenv = Array.of_list env_params_types in
     	let llpars = Array.of_list (List.map param_type parameters) in
     	let llpars = if(name = "main") then llpars else  Array.append llpars llenv in
     	let env_params_to_passed = List.map (temp_var) env_params in
     	let parameters = if(name = "main") then parameters else parameters@env_params_to_passed in
	fun_names := name :: !fun_names ;
        let fun_typ= ltype_of_type (get_fuction_f func.parameter_info).function_result in
        let ft =function_type fun_typ llpars in
        let f = (if (Option.is_some (lookup_function fn_name the_module) ) then let v=( Option.get (lookup_function fn_name the_module)) in (delete_function v; declare_function fn_name ft the_module  ) else ( declare_function fn_name ft the_module (*codegen_func func*)) )in
        (*let builder = builder_at_end context (entry_block f) in*)
        let bbs =append_block context "smth" f in
        fun_bbs := bbs :: !fun_bbs;
        position_at_end bbs builder ;
        let params2 = Array.iteri ( fun i el -> let n = List.nth parameters i in let (n,(typea,by_ref)) = (n.entry_id,match n.parameter_info with
        |ENTRY_parameter asd-> (asd.parameter_type,asd.parameter_mode)) in
        (match by_ref with
        | PASS_BY_REFERENCE -> set_value_name n el;ignore(Hashtbl.add named_values n el)
        | _ ->
                        (set_value_name n el;let g = (build_alloca (ltype_of_type typea)  n builder) in (*let el = build_pointercast el (ltype_of_type typea) "cast" builder in *)  ignore(build_store el g builder) ; ignore(Hashtbl.add named_values n g))) ) (params f)
        in
        (*let _ = if (name="main") then List.iter (fun x-> ignore(codegen_decl x builder)) !global_decls else ()  in*)
        (*check*) let _ =List.map (fun x-> codegen_decl  x builder) (sort_d b) in
        let bb =List.hd !fun_bbs in
        position_at_end bb builder;
        let _  = List.map (fun x->codegen_stmt x builder) c in
        fun_bbs := List.tl !fun_bbs;
        let next_bb =try List.hd !fun_bbs
                     with Failure ("hd") -> bb in
        let last= match block_end f with After (block) -> block in
        let return= ltype_of_type (get_fuction_f func.parameter_info).function_result (*return_type (type_of f)*) in
        let _ =(match (instr_end last) with
                |After(ins)-> if ((instr_opcode ins) = Opcode.Ret) then ()
        else
                if (return = (ltype_of_type TYPE_void) )  then ignore (build_ret_void builder) else
                          ignore(build_ret (default_val_type TYPE_int) builder)
         |At_start(_) ->
                         if (return= (ltype_of_type TYPE_void) )  then( ignore (build_ret_void builder) )else
                                  ignore(build_ret (default_val_type TYPE_int) builder) ;) in
        let _ =ignore(  delete_from_hash b); in
		      fun_names := List.tl !fun_names;
                      let _ = Array.iteri (fun i a ->
                        let n = (List.nth parameters i) in
                        if(i>=(List.length parameters_old)) then () else(
                                let (n,(typea,by_ref))= (n.entry_id, match n.entry_info with
                                | ENTRY_parameter asd -> (asd.parameter_type,asd.parameter_mode)) in
                               match by_ref with
                               |PASS_BY_REFERENCE ->Hashtbl.remove named_values n
                                | _ -> Hashtbl.remove named_values n)) (params f) in
 		      clear_env env_params;
                      position_at_end next_bb builder;
                      ignore(env := remove_env !env); (* Go higher in env*)
                      (*ignore(  delete_from_hash_par func);*)

  (* let (variables,rest) = List.partition (fun x -> match x with Variable_dec _ -> true | _ -> false) dec_list in
  let (definitions,declarations) = List.partition (fun x -> match x with Fundefi _ -> true | _ -> false) rest in
  let dec_to_def defs dec =
    let def_eqs_dec  dec def =
      match def,dec with
      |Fundefi (_,f,_,_,_), Fundecl(_,c,_) -> f = c
      | _ ,_ -> false
    in try List.find (def_eqs_dec dec) defs
       with Not_found -> dec
  in
  let def_to_dec def = match def with
    |Fundefi (ty,name,args,_,_) -> Fundefi(ty,name,args,[],[]) (*Fundecl initialy*)
    | _ -> raise Terminate in
  let alldecs = List.map def_to_dec definitions in
  let ordered_defs_and_lib_decs = List.map (dec_to_def definitions) declarations in
  let (ordered_defs,lib_decs) = List.partition (fun x -> match x with Fundefi _ -> true | _ -> false) ordered_defs_and_lib_decs in
  (* let _ = Printf.printf "%d replacements\n" (List.length ordered_defs) in *)
  let rest_defs = List.filter (fun x -> let b = List.exists ((fun x y-> x = y) x) ordered_defs in not b ) definitions in
  let defs = sort_definitions(ordered_defs@rest_defs) in (* ordered_defs@rest_defs in *)
  lib_decs@variables@alldecs@defs *) *)

  (* this fun takes the type of the elem and returns the lltype *)


  let rec type_to_lltype ty = match ty with

    | Types.Tdouble -> double_type
    | Types.Tint -> integer_type
    | Types.Tbool -> bool_type
    | Types.Tchar -> i8_type context (* NOT SURE *)
    | Types.Tarray (t,n) -> let typ =type_to_lltype t in
                                array_type typ n
    | Types.Tptr x -> let t = type_to_lltype x in
                              pointer_type t
    | Types.Tvoid -> void_type context
    | _ -> null_type

  and print_decs decs =
    List.iter (fun x -> match x with
                        | Vardecl _ -> Printf.printf "Variable_list\n"
                        | Fundecl (_,name,_) -> Printf.printf "Declaration of %s\n" name
                        | Fundefi  (_,name,_,_,_) -> Printf.printf "Definition of %s\n" name) decs

  and sort_decls dec_list =
    let (variables,rest) = List.partition (fun x -> match x with Vardecl _ -> true | _ -> false) dec_list in
    let (definitions,declarations) = List.partition (fun x -> match x with Fundefi _ -> true | _ -> false) rest in
    let dec_to_def defs dec =
      let def_eqs_dec  dec def =
        match def,dec with
        |Fundefi (_,f,_,_,_), Fundecl(_,c,_) -> f = c
        | _ ,_ -> false
      in try List.find (def_eqs_dec dec) defs
         with Not_found -> dec
    in
    let def_to_dec def = match def with
      |Fundefi (ty,name,args,_,_) -> Fundefi(ty,name,args,[],[]) (*Fundecl initialy*)
      | _ -> raise Terminate in
    let alldecs = List.map def_to_dec definitions in
    let ordered_defs_and_lib_decs = List.map (dec_to_def definitions) declarations in
    let (ordered_defs,lib_decs) = List.partition (fun x -> match x with Fundefi _ -> true | _ -> false) ordered_defs_and_lib_decs in
    (* let _ = Printf.printf "%d replacements\n" (List.length ordered_defs) in *)
    let rest_defs = List.filter (fun x -> let b = List.exists ((fun x y-> x = y) x) ordered_defs in not b ) definitions in
    let defs = sort_definitions(ordered_defs@rest_defs) in (* ordered_defs@rest_defs in *)
    lib_decs@variables@alldecs@defs

  and dec_with_name name dec =
    match dec with Fundecl(_,n,_) -> n = name | _ -> false


  and sort_definitions defs =
    let compare d1 d2 =
      match d1, d2 with
      |Fundefi(_,n1,_,dec1,_), Fundefi(_,n2,_,dec2,_) ->
        if(n1 = n2) then 0 else(
          let (defs,decs) = List.partition (fun x -> match x with Fundefi _ -> true |_ -> false) dec2 in
          if(List.exists (dec_with_name n1) decs ) then -1
          else if(List.exists (fun x -> (compare d1 x) = -1) defs) then -1 (*a def is smaller than*)
          else (match d2, d1 with
                |Fundefi(_,n1,_,dec1,_), Fundefi(_,n2,_,dec2,_) ->
                  if(n1 = n2) then 0 else(
                    let (defs,decs) = List.partition (fun x -> match x with Fundefi _ -> true |_ -> false) dec2 in
                    if(List.exists (dec_with_name n1) decs ) then 1
                    else if(List.exists (fun x -> (compare d1 x) = -1) defs) then 1 else 0) (*a def is smaller than*)
                | _, _ -> 0)
        )

      (*used to be just 0*)
      |_,_ -> 1
    in List.sort compare defs



  and param_type par = match par with
    | Ast.Param(ty,name) -> type_to_lltype ty
    | Ast.ParamByRef(ty,name) -> let typ = type_to_lltype ty in
                                   pointer_type typ

  and find_block stag tuple = match tuple with
    | [] -> raise Not_found
    | (tag, tag_bb):: rest -> if stag = tag then tag_bb
                              else
                                find_block stag rest
  let rec print_list = function
      [] -> ()
    | (e,s)::l -> print_string e ; Printf.printf " " ; print_list l

  let create_entry_block_alloca the_function var_name ty =
    let typ = type_to_lltype ty in
    let builder = builder_at context (instr_begin (entry_block the_function)) in (* we make a builder which points at the first instruction of the block and allocates memory there *)
    build_alloca typ var_name builder

  let rec is_return_last_instuction stmts = match stmts with
    | [] -> false
    | [Ast.Sreturn _] -> true
    | _::tail -> is_return_last_instuction tail

  (* HAVE TO CHANGE IT TO UNIT *)
  let rec codegen_main prog =
    match prog with
    | Some decs -> let decs = sort_decls decs in codegen_declars decs
    | None -> codegen_declars []

  and codegen_declars x = match x with
    |  [] -> const_null null_type
    | x::rest ->
       ignore(codegen_declaration x);
       codegen_declars rest

  and remove_variable_delcarations x = match x with
      [] -> ()
    | x::rest ->
       match x with
       |Ast.Vardecl(ty,decs) ->
         ignore(
             List.map (fun dec -> match dec with
                                  | Ast.Decl(name,_) ->
                                    (* | Ast.Complex_declarator(name,_)->  *)
                                    (* let reg = Str.regexp "_env" in *)
                                     (* let _ =Printf.printf "Didn't delete %s\n" name in *)
                                     (* let _ = try ignore(Str.search_forward reg name 0);  *)
                                     (*         with Not_found -> Hashtbl.remove named_values name; Printf.printf "Deleted\n" in *)
                                     (* () *)
                                     Hashtbl.remove named_values name
                      ) decs
           )
       |_-> remove_variable_delcarations rest


  and codegen_declaration x = match x with
    (* maybe we dont need the fun dec but never mind *)

    | Ast.Fundecl(ty, name, parameters) ->
       if(match !env with Global _ -> true | _ ->   let fn_name_t = String.concat "_" (name::List.tl(!fun_names)) in
                                                    match lookup_function fn_name_t the_module with None -> true | _ -> false) then(

         (* if(match !env with Global _ -> true | _ -> true) then( *)
         (* Printf.printf("Fun dec\n"); *)
         let llpars = Array.of_list (List.map param_type parameters) in   (* llpars is an array of the params *)
         let fun_typ = type_to_lltype ty in                           (* THATS WRONG HAVE TO CHANGE WITH MATCH *)
         let ft = function_type fun_typ llpars in
         let fn_name = String.concat "_" (name::!fun_names) in
         let f = declare_function fn_name ft the_module in
         Array.iteri ( fun i a ->
                       let p = (List.nth parameters i) in
                       match p with
                       | Ast.Param(ty, name)->
                          (* HAVE TO SEE THE WAY WE TAKE IT *)
                          set_value_name name a;
                       (* Printf.printf "adding %s...\n" name; *)
                       (* Hashtbl.add named_values name a *)
                       | Ast.ParamByRef(ty, name)->
                          set_value_name name a;
                     (* Printf.printf "adding %s...\n" name; *)
                     (* Hashtbl.add named_values name a *)
                     )
                     (params f); f
       )else const_null null_type
    | Ast.Vardecl(ty, decs) ->
       (* Printf.printf("Var dec\n"); *)
       (*let _ = block_parent (insertion_block builder) in*)
       let typos = type_to_lltype ty in (*we want the type of the vars *)
       let value = init_value ty in (* NOT SURE IF WE WANT THE POINTER TO BE NULL AT FIRST *)
       let _ = match !env with
         | Global (_) -> let _ = List.iter (fun x -> match x with
                                                     | Ast.Decl(name,_) -> ignore(env := update_env name (!env))
                                                     (* | Ast.Complex_declarator(name, _) -> ignore(env := update_env name (!env)) *)
                                                     )
                                           decs
                         in
                         global_decs := Ast.Vardecl(ty,decs)::!global_decs;
         (* Printf.printf "New length:%d\n" (List.length !global_decs) *)
         | Nested _ ->ignore(
                          List.map (fun dec ->
                              match dec with
                              | Ast.Decl(name,_) ->
                                 (* Printf.printf "I'm here adding %s\n" name; *)
                                 let alloca = build_alloca typos name builder in
                                 ignore(build_store value alloca builder);
                                 Hashtbl.add named_values name alloca;
                                 env := update_env name (!env)
                              (* | Ast.Complex_declarator(name, exp) ->
                                 let leng = code_gen_exp exp in
                                 (* dump_value leng; *)(* we have the length of the array in llvalue *)
                                 let decl = build_alloca (pointer_type typos) name builder in
                                 let alloca = build_array_malloc (typos) leng "allocatmp" builder in (* or build array malloc/alloca *)
                                 let _ = build_store alloca decl builder in
                                 Hashtbl.add named_values name decl;
                                 env := update_env name !env *)
                            (* HAVE TO CHECK IT AGAIN *)
                            ) decs) in
       const_null null_type;

    | Ast.Fundefi(ty, name, parameters, decls, stms) ->
       (* Printf.printf "Fun def\n"; *)
       let parameters_old = parameters in
       env:= Nested([],!env);
       let env_params = difference_with_env !env parameters in
       update_env_with_params parameters !env; (*Should create side effect*)
       (* let _ = print_env_pars !env in *)
       let env_params_types = get_env_params_types env_params !global_decs in
       (* let _ = print_hashtbl named_values in *)
       let llenv = Array.of_list env_params_types in
       let llpars = Array.of_list (List.map param_type parameters) in
       let llpars = if(name = "main") then llpars else  Array.append llpars llenv in
       let env_params_to_passed = List.map (fun x -> Ast.ParamByRef (Tnone,x)) env_params in
       let parameters = if(name = "main") then parameters else parameters@env_params_to_passed in
       let fun_typ = type_to_lltype ty in (* THATS WRONG HAVE TO CHANGE WITH MATCH *)
       let ft = function_type fun_typ llpars in (* creates a function *)
       let fn_name = String.concat "_" (name::!fun_names) in
       let the_fun = (match lookup_function fn_name the_module with
                      | None -> fun_names:= name :: !fun_names;
                                declare_function fn_name ft the_module
                      (* | Some f -> fun_names := name::!fun_names; f in *)
                      | Some f -> fun_names := name :: !fun_names; delete_function f; declare_function fn_name ft the_module  ) in
       (* create a new basic block for the function *)
       let label = String.concat "_" [name;"entry"] in

       let bb= append_block context label the_fun in
       fun_bbs := bb :: !fun_bbs;
       position_at_end bb builder; (* point at the end of the new created block *)
       (* Printf.printf "%s will be called with %d params\n" name (Array.length (params the_fun)); *)
       (* we initialize the params and add them to Hashtable *)
       let _ = Array.iteri(fun i a ->
                   let n = (List.nth parameters i) in
                   match n with
                   | Ast.Param(ty, name) ->
                      (* Printf.printf "Adding by_val param %s\n" name; *)
                      let typ = type_to_lltype ty in
                      set_value_name name a;
                      let alloca = build_alloca typ name builder in
                      ignore(build_store a alloca builder);
                      Hashtbl.add named_values name alloca;
                   | Ast.ParamByRef(ty, name) ->
                      (* Printf.printf "Adding by_ref param %s\n" name; *)
                      let _ = set_value_name name a in
                      Hashtbl.add named_values name a
                 (*let _ = match ty with |TYPE_none -> ignore(update_env name !env) | _ ->() in *) (*Add the env_params*)
                 (* match ty with TYPE_none -> () | _ -> Hashtbl.add named_values name a) *)
                 (*TYPE_none == env_variable already added. We don't want dubplicates*)
                 )(params the_fun)in
       let _ = if(name = "main") then ignore(codegen_declars !global_decs) else ()in
       let decls = sort_decls decls in
       (* Printf.printf "decls length %d\n" (List.length decls); *)
       let _ = codegen_declars decls in
       (* let _ = print_hashtbl named_values in *)
       if (ty = Tvoid) then
         returns := false (* we have set a ret point yes *)
       else
         returns := true;
       let bb = List.hd !fun_bbs in
       position_at_end bb builder;
       let _ =  codegen_states stms  in

       fun_bbs := List.tl !fun_bbs;
       let next_bb = try List.hd !fun_bbs
                     with Failure ("hd") -> bb in
       fun_names := List.tl !fun_names;
       Array.iteri(fun i a ->
           let n = (List.nth parameters i) in (*used to be i*)
           if(i >= (List.length parameters_old)) then () else
             match n with
             | Ast.Param(ty, name) ->
                Hashtbl.remove named_values name
             | Ast.ParamByRef(ty, name) ->
                Hashtbl.remove named_values name )
                  (params the_fun);
       (*FREE DECLS*)
       remove_variable_delcarations decls;
       clear_env env_params;
       env := remove_env !env; (* Go higher in env*)
       (* Printf.printf ("Closing scope...\n"); *)
       (* print_env_pars !env; *)
       (* print_hashtbl named_values; *)
       if !returns = false then
         (ignore(build_ret_void builder); position_at_end next_bb builder; the_fun)
       else
         (
           let _ = if (is_return_last_instuction stms) then () else ignore(build_ret (init_value ty) builder) in
           position_at_end next_bb builder; the_fun );


  and codegen_states st = match st with
    | [] -> const_null null_type
    | x::rest -> ignore(codegen_statement x);
                 codegen_states rest

  and codegen_statement st = match st with
  (*  match Sexpr with some exp or none*)
    | Ast.Sexpr(exp) -> code_gen_exp exp
    | Ast.Snull -> const_null integer_type
    | Ast.Slist sts -> codegen_states sts
    | Ast.Sif(cond, stm,else_stm) ->(
       match else_stm with
       | None ->
           let condition = code_gen_exp cond in
         let zero = if (String.contains(string_of_lltype(type_of condition)) '1') then  const_int (i1_type context) 0
                    else const_int (bool_type) 0 in
         let cond_val = if (is_pointer cond) then build_load condition "loadcon" builder
                        else condition in
         let cond_val = build_icmp Icmp.Ne cond_val zero "ifcond" builder in


         let start_bb = insertion_block builder in
         let the_function = block_parent start_bb in

         (* to calculate the llvalue of current block *)
         let bef_bb = insertion_block builder in
         let _ = value_of_block bef_bb in

         let then_bb = append_block context "then" the_function in (* we create the then block *)
         position_at_end then_bb builder; (* we put builder at the end of blovk then_bb *)

         let _ = codegen_statement stm in  (* we create the code for the then statement *)
         let new_then_bb = insertion_block builder in (* we save the block in new_then_bb *)

         let merge_bb = append_block context "ifcont" the_function in (* we create the block after the if *)
         position_at_end merge_bb builder;

         (* let incoming = [(then_val, new_then_bb); (bef_bb_val,bef_bb)] in *)
         (* let phi = build_phi incoming "iftmp" builder in *)

         position_at_end start_bb builder; (* we return to the starting block *)
         ignore (build_cond_br cond_val then_bb merge_bb builder); (* we concat the two blocks *)

         position_at_end new_then_bb builder; ignore (build_br merge_bb builder); (* we set the then pointer to the endif block *)
         position_at_end merge_bb builder; (* we set the builder to the end of common block *)
         (* phi *)
         const_null null_type;



    | Some elsestm ->
      let condition = code_gen_exp cond in

    let zero = if (String.contains(string_of_lltype(type_of condition)) '1') then  const_int (i1_type context) 0
               else const_int (bool_type) 0 in

    let cond_val = if (is_pointer cond) then build_load condition "loadcon" builder
                   else condition in

    let cond_val = build_icmp Icmp.Ne cond_val zero "ifelsecond" builder in

    let start_bb = insertion_block builder in (* start_bb contains the basic block *)
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then" the_function in (* creates the then block *)
    position_at_end then_bb builder;

    let _ = codegen_statement stm in

    let new_then_bb = insertion_block builder in

    let else_bb = append_block context "else" the_function in
    position_at_end else_bb builder;

    let _ = codegen_statement elsestm in
    let new_else_bb = insertion_block builder in

    let merge_bb = append_block context "ifcont" the_function in
    position_at_end merge_bb builder;

    (* let incoming = [(then_val, new_then_bb); (else_val, new_else_bb)] in *)
    (* let phi = build_phi incoming "iftmp" builder in *)
    position_at_end start_bb builder;
    ignore (build_cond_br cond_val then_bb else_bb builder);

    position_at_end new_then_bb builder; ignore (build_br merge_bb builder);
    position_at_end new_else_bb builder; ignore (build_br merge_bb builder);

    (* Finally, set the builder to the end of the merge block. *)
    position_at_end merge_bb builder;

    (* phi *)
    const_null null_type;
    )
    | Ast.Sfor(tag, e1, e2, e3, s) ->

       (* 1 we calculate the first exp *)
       let _ = match e1 with
         | None -> () (* NOT SURE IF IGNORE WORKS *)
         | Some exp -> ignore ( code_gen_exp exp) in

       (* now we make a new block in order to have only the condition *)
       let preheader_bb = insertion_block builder in
       let the_function = block_parent preheader_bb in

       let loop_cond_bb = append_block context "loopcondition" the_function in
       position_at_end preheader_bb builder;

       (* now we make the branch *)
       ignore (build_br loop_cond_bb builder);

       position_at_end loop_cond_bb builder;
       (* 2 now we have to check the condition *)
       let loop_cond =  match e2 with
         | None -> const_null null_type
         | Some exp -> let tmp = code_gen_exp exp in if (is_pointer exp) then build_load tmp "loadcon" builder else
                                                       tmp

       in

       let zero = if (String.contains(string_of_lltype(type_of loop_cond)) '1') then  const_int (i1_type context) 0
                  else const_int (bool_type) 0 in

       let cond_val = build_icmp Icmp.Ne loop_cond zero "loopcond" builder in

       (* let cond_val = loop_cond (\* build_fcmp Fcmp.One loop_cond zero "loopcond" builder *\) in *)

       (* 3 now we point to the block in which we are *)
       let preheader_bb = insertion_block builder in
       let the_function = block_parent preheader_bb in

       (* we create the loop block *)
       let loop_bb = append_block context "loopbody" the_function in
       position_at_end loop_bb builder;

       let step_bb= append_block context "loopstepblock" the_function in
       position_at_end step_bb builder;
       let _ =(match tag with
               | None -> let tag_bb = insertion_block builder in
                         continue_tags := ("$$$", tag_bb) :: !continue_tags
               | Some str -> let tag_bb = insertion_block builder in
                             continue_tags := (str, tag_bb) :: !continue_tags;
                             continue_tags := ("$$$",tag_bb) :: !continue_tags) in

       let afterloop_bb = append_block context "afterloop" the_function in
       position_at_end afterloop_bb builder;
       (* we have to create the after loop block *)
       ignore ( match tag with
                | None -> let tag_bb = insertion_block builder in
                          break_tags := ("$$$", tag_bb) :: !break_tags
                | Some str -> let tag_bb = insertion_block builder in
                              break_tags := (str, tag_bb) :: !break_tags;
                              break_tags := ("$$$",tag_bb) :: !break_tags
              );

       position_at_end loop_bb builder;
       ignore (codegen_statement s);
       ignore(build_br step_bb builder);

       position_at_end step_bb builder;
       (* now we calculate the step *)
       let _ = match e3 with
         | None -> const_null null_type
         | Some exp -> code_gen_exp exp in


       position_at_end step_bb builder; (* we point to the afterloop block *)

       (* builder goes at the end of the loop block *)
       ignore(build_br loop_cond_bb builder);

       (* go again to check condition *)
       position_at_end loop_cond_bb builder;
       (* 4 now we again point at the end of the condition in order to check where to go *)
       position_at_end preheader_bb builder;
       ignore(build_cond_br cond_val loop_bb afterloop_bb builder);

       position_at_end afterloop_bb builder;
       continue_tags:= List.tl (!continue_tags);
       break_tags:= List.tl(!break_tags);
       const_null null_type
    | Ast.Scont(label) -> (match label with
                      | None -> ( try
                                    let con_bb = find_block "$$$" (!continue_tags) in
                                    ignore ( build_br con_bb builder); const_null null_type
                                  with Not_found->
                                    (
                                      Printf.printf "falseNotag"; const_null null_type))

                      | Some tag -> try
                                    let con_bb = find_block tag (!continue_tags) in
                                    ignore(build_br con_bb builder); const_null null_type
                                  with Not_found ->
                                    (Printf.printf "false"; const_null null_type)
                      (* | _ -> raise (Tnone "Something went wrong"); *)
                     )
    | Ast.Sbrk(label)-> (match label with

                  | None -> ( try
                                let br_bb = find_block "$$$" (!break_tags) in
                                ignore ( build_br br_bb builder); const_null null_type
                              with Not_found->
                                (
                                  Printf.printf "falseNotag"; const_null null_type))
                  | Some tag -> try
                                let br_bb = find_block tag (!break_tags) in
                                ignore(build_br br_bb builder); const_null null_type
                              with Not_found ->
                                (Printf.printf "false"; const_null null_type)

                  (* | _ -> raise (Tnone "Something went wrong"); *)
                 )
    (* in Return we have a variable name somehow and we save there the result *)
    | Ast.Sreturn(ex) -> match ex with
                        | Some exp ->
                           let ret_val = code_gen_exp exp in
                           let ret_val =
                             if(ExpCodeGen.is_pointer exp) then build_load ret_val "ret" builder
                             else ret_val
                           in
                           build_ret ret_val builder
                        | None -> returns := true;
                                  build_ret_void builder

  and init_value ty = (match ty with
                       | Tint  -> (const_int integer_type 0)
                       | Tdouble  -> const_float double_type 0.0
                       | Tbool  -> const_int bool_type 0
                       | Tchar  -> (const_int char_type 0)(* const_string context "" *)
                       | Tptr x  ->
                          ( let lltype = type_to_lltype (Tptr x) in
                            let lltype = const_pointer_null lltype in
                            (* dump_value lltype; *) lltype)
                       (* |_ -> raise (Tnone "problem with value allocation") *)
                       )
