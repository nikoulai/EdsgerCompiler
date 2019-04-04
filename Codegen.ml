open Llvm
open Ast
open Types
open Semantic
open Symbol
open Format
open Identifier
open Error
open Char

exception Type_error of string
exception No_value
exception Terrror of string*ast_expr
exception Error of string
let context = global_context ()
let the_module = create_module context "LLVM IR"
let builder = builder context
let named_values:(string, llvalue) Hashtbl.t = Hashtbl.create 10
let integer_type  = i16_type context
let null_type = i1_type context
let bool_type = i1_type context
let char_type = i8_type context
let double_type =  x86fp80_type context
let fun_names : string list ref = ref []
let fun_bbs : llbasicblock list ref = ref []
let returns = ref true
let continue_tags : (string *llbasicblock) list ref = ref []
let break_tags : (string * llbasicblock ) list ref = ref []
let old_bindings : (string * llvalue) list ref = ref []
let global_decs : (Ast.ast_declaration) list ref = ref []
type environment = Global of (string list)| Nested of (string list * environment)
module SS = Set.Make(String)
let env:environment ref = ref (Global ([]))

let rec findLltype ty =
  match ty with
  | Tint -> i16_type context
  | Tdouble -> double_type
  | Tarray (t,n) -> let t = findLltype t in
                        array_type t n
  | Tchar -> i8_type context
  | Tbool -> i1_type context
  | Tptr x -> let t = findLltype x in
                      pointer_type t
  | _ -> (Error.error "Unknown type"; i1_type context)

let print_hashtbl named_vales =
  Printf.printf ("Printing Hashtbl:\n");
  Hashtbl.iter (fun str llval -> Printf.printf ">%s\n" str) named_values

let contains s1 s2 =
  let re = Str.regexp_string s2
  in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let rec update_env_without_hashtbl name env =
  match env with
  | Global (names) -> Global(name::names)
  | Nested (names,e) -> Nested (name::names,e)

and clear_env env_list =
    List.iter (Hashtbl.remove named_values) env_list

and get_env_of_called env args params =
  let argscnt = List.length args in
  let paramscnt = Array.length params in
  let cnt = paramscnt - argscnt in
  let rec walk env =
    let l = List.length (env_to_list env) in
    if (l=cnt) then env else
      match env with
      | Global([])-> Global([])
      | Global(h::t)-> walk (Global(t))
      | Nested ([],e) -> walk e
      | Nested ((h::t),e) -> walk (Nested (t,e))
  in walk env

and update_env name env=
  let name_env = name in
  let name_to_env = match env with Global(_) -> name | _ -> name_env in
  match env with
  | Global (names) -> Global(name_to_env::names)
  | Nested (names,e) -> Nested (name_to_env::names,e)


and update_env_with_params params en =
  let names = get_param_names params
  in List.iter (fun x-> env:=update_env x en) names


and env_to_set env =
  let rec walk env acc =
    match env with
    | Global (names) -> let set_to_add = SS.of_list names in SS.union set_to_add acc
    | Nested (names,env) -> let set_to_add = SS.of_list names in

                            let new_acc = SS.union set_to_add acc in
                            walk env new_acc
  in walk env SS.empty


and difference_with_env env params =
  let param_set = SS.of_list (get_param_names params) in
  let env_set = env_to_set env in
  SS.elements (SS.diff env_set param_set )

and get_env_params_types env global_decs =
  let has_name_in_dec name dec =
    match dec with
    |Ast.Decl(n,_) -> (name = n)
  in
  let has_name_in_var_dec name element =
    match element with
    |Ast.Vardecl(ty,decl) -> (try ignore(List.find (has_name_in_dec name) decl); true
                                   with Not_found -> false)
    |_ -> raise Not_found
  in
  let find_type_from_global name gl =
    let dec = List.find (has_name_in_var_dec name) gl
    in match dec with
       | Ast.Vardecl(ty,l) -> (let wanted = List.find (has_name_in_dec name) l in
                                    let ty = findLltype ty in
                                    match wanted with
                                    | Ast.Decl(name,ex) -> (* Printf.printf "Decla!\n"; *)
                                    (match ex with
                                      | Some e -> (* Printf.printf "Pointer!\n"; *) pointer_type (pointer_type ty)
                                      | None -> (* Printf.printf "None!\n"; *) pointer_type ty
                                    )
                              )
       | _ -> Printf.printf "unexpected type"; integer_type
  in
  let find_type name =
    try
      let v =
        try Hashtbl.find named_values name
        with Not_found -> raise Not_found
      in (type_of v)
    with Not_found -> (* Printf.printf "Globals"; *)  find_type_from_global name global_decs
  in
  List.map find_type env

(* and get_env_params_types env =
  let find_type name =
      let v =
        try Hashtbl.find named_values name
        with Not_found -> print_string(name); raise Not_found
      in (type_of v)
  in List.map find_type env
 *)

and env_to_list env =
  SS.elements (env_to_set env)

and print_env_pars env =
  let l = env_to_list env in
  let _  = match env with Nested _ -> Printf.printf "Nested:\n" | Global _ -> Printf.printf "Global:\n" in
  List.iter (fun x -> Printf.printf "List:%s\n" x) l

and remove_env env =
  match env with
  | Global (names) -> Global([])
  | Nested (names,env) -> env

and env_to_id_list env =
  let env_list = env_to_list env in
  List.map (fun x -> Eid(x)) env_list

and get_args_diff_env args env=
  let args_set = SS.of_list args in
  let env_set = env_to_set env in
  let new_env_set = SS.diff env_set args_set in
  SS.elements new_env_set

and get_param_names params =
  let get_param_name p =
    match p with
    | Ast.Param(_,name) -> name
    | Ast.ParamByRef(_,name) -> name
  in List.map get_param_name params

let rec print_list = function
    [] -> ()
  | (e)::l -> print_string e ; Printf.printf " " ; print_list l

let rec find_function fun_name fun_name_list =
  match fun_name_list with
  | [] -> ( match lookup_function fun_name the_module with
            | Some calle -> calle
            | None -> raise (Type_error "unknown function refernced"))

  | x::rest -> ( let to_found = String.concat "_" (fun_name::fun_name_list) in
                 match lookup_function to_found the_module with
                 |Some callee -> callee
                 | None -> find_function fun_name (List.tl fun_name_list))

let rec code_gen_exp exp =
  match exp with
    Eid name ->  let v =
                  try
                    Hashtbl.find named_values name
                  with Not_found -> raise (Type_error "Variable not found") in
                v
  | Eint int -> let value = const_int integer_type int in
               value;
  | Edoub double -> const_float double_type double
  | Echar char -> const_int char_type (code char)
  | Estr str -> build_global_stringptr str "strtmp" builder
  | Ebool bool -> const_int bool_type (bool_to_int bool)
  | Eapp (called_fun, args) ->
   let create_param p = Param(Tnone,"dum") in
   let callee = find_function called_fun (!fun_names) in
   let params = params callee in
   let tmp = if(is_void callee) then "" else "calltmp" in
   let env_of_called = get_env_of_called !env args params in
   let env_args = env_to_id_list (env_of_called) in
   let args = args@env_args in
   let args = Array.of_list args in
   let args = Array.mapi
                ( fun i a -> let e = code_gen_exp args.(i) in
                             if(is_pointer args.(i)) then
                               (let typical_param = String.length(string_of_lltype (type_of(params.(i)))) in
                                let actual_param = String.length( string_of_lltype ( type_of(e))) in
                                if (typical_param = actual_param) then
                                  e
                                else
                                  build_load e "argtmp" builder
                               )
                             else e

                ) args
   in
   build_call callee args tmp builder
| Emat (e1, e2) -> (match e1 with
                   Estr str ->
                    let act_array = build_global_stringptr str "strtmp" builder in
                    let index = code_gen_exp e2 in
                    let index = if (is_pointer e2) then build_load index "tmpindex" builder
                                else index in
                    let index = Array.of_list [index] in
                    let ir = build_gep act_array index "arraytmp" builder in
                    ir
                  | Emat _ ->
                    let act_array = code_gen_exp e1 in
                    let index = code_gen_exp e2 in
                    let index = if (is_pointer e2) then build_load index "tmpindex" builder
                                else index in
                    let index = Array.of_list [index] in
                    let ir = build_gep act_array index "arraytmp" builder in
                    ir
                  | _ ->
                    let pointer = code_gen_exp e1 in
                    let act_array = build_load pointer "act_ar" builder in
                    let index = code_gen_exp e2 in
                    let index = if (is_pointer e2) then build_load index "tmpindex" builder
                                else index in
                    let index = Array.of_list [index] in
                    let ir = build_gep act_array index "arraytmp" builder in
                    ir)
| Eunop (e,op) -> (match op with
                      |  Tuamp->
                        (* Printf.printf"Ampersand\n"; code_gen_exp e *)
                        (* Printf.printf"Ampersand\n";  *)
                        (get_identifier e)
                      | Tutim ->
                       (* Printf.printf"Dereferencing\n"; *)
(*                        let tmp =  if(need_def e) then build_load ( code_gen_exp e) "tmp" builder else ( code_gen_exp e) in
                       let load_ = (build_load tmp "tmp" builder) in
                       load_ *)
                       (let exp_ir = code_gen_exp e in
                            let tmp_ir = build_load exp_ir "loadtmp" builder in
                            tmp_ir)
                      | Tumin -> let expr = Ebop(Eint 0, e ,Tbmin) in
                               code_gen_exp expr
                      | Tupl -> code_gen_exp e
                      | Tunot -> let exp = code_gen_exp e in
                               build_not exp "nottmp" builder
                      | _ -> raise (Type_error "Wrong operator")
                     )

|Ebop (e1,e2,op) ->  let ir1 = code_gen_exp e1 in
                            let ir2 = code_gen_exp e2 in
                            (
                              let ir1 = if (is_pointer e1) then build_load ir1 "loadtmp" builder
                                        else ir1 in
                              let ir2 = if (is_pointer e2) then build_load ir2 "loadtmp" builder
                                        else ir2 in
(*                               let ir1 = if( (need_def e1)) then build_load ir1 "tmp" builder else ir1 in
                              let ir2 = if(need_def e2) then build_load ir2 "tmp" builder else ir2 in
 *)     
                              (match op with
                               | Tbpl ->  if(is_double ir1) then build_fadd ir1 ir2 "faddtmp" builder
                                         else if (is_op_with_pointer ir1) then code_gen_exp (Emat(e1,e2))
                                         else if (is_op_with_pointer ir2) then code_gen_exp (Emat(e2,e1))
                                         else build_add ir1 ir2 "addtmp" builder
                               | Tbmin ->  if(is_double ir1) then build_fsub ir1 ir2 "fsubtmp" builder
                                         else if (is_op_with_pointer ir1) then code_gen_exp (Emat(e1,Eunop (e2, Tumin)))
                                         else if (is_op_with_pointer ir2) then code_gen_exp (Emat(e2,Eunop (e1, Tumin)))
                                         else build_sub ir1 ir2 "subtmp" builder
                               | Tbtim ->  if(is_double ir1) then build_fmul ir1 ir2 "fmultmp" builder
                                         else build_mul ir1 ir2 "multmp" builder
                               | Tbdiv ->  if(is_double ir1) then build_fdiv ir1 ir2 "fdivtmp" builder
                                         else build_sdiv ir1 ir2 "sdivtmp" builder
                               | Tbmod -> build_srem ir1 ir2 "sremtmp" builder
                               | Tbeq -> if (e1 = Enull) then build_is_null ir2 "is_null" builder
                                         else if (e2 = Enull) then build_is_null ir1 "is_null" builder
                                         else if ((e1 = Enull) && (e2 = Enull)) then code_gen_exp (Ebool true)
                                         else
                                           if(is_double ir1) then build_fcmp Llvm.Fcmp.One ir1 ir2 "icmpeqtmp" builder
                                           else
                                             let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Eq ir1 ir2 "icmpeqtmp" builder
                                   (* build_icmp Llvm.Icmp.Eq ir1 ir2 "icmpeqtmp" builder *)
                               | Tbneq -> if (e1 = Enull) then build_is_null ir2 "is_null" builder
                                         else if (e2 = Enull) then build_is_null ir1 "is_null" builder
                                         else if ((e1 = Enull) && (e2 = Enull)) then code_gen_exp (Ebool false)
                                         else
                                           if(is_double ir1) then build_fcmp Llvm.Fcmp.One ir1 ir2 "icmpeqtmp" builder
                                           else
                                             let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Ne ir1 ir2 "icmpeqtmp" builder
                               | Tblss ->  if(is_double ir1) then build_fcmp Llvm.Fcmp.Olt ir1 ir2 "icmpslttmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                        else ir2 in
                                              build_icmp Llvm.Icmp.Slt ir1 ir2 "icmpslttmp" builder
                               | Tbgrt -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Ogt ir1 ir2 "icmpsgttmp" builder
                                        else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Sgt ir1 ir2 "icmpsgttmp" builder
                               | Tbleq -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Ole ir1 ir2 "icmpsletmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                        else ir2 in
                                              build_icmp Llvm.Icmp.Sle ir1 ir2 "icmpsletmp" builder
                               | Tbgeq -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Oge ir1 ir2 "icmpsgetmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (integer_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (integer_type) "ptrtoint" builder
                                                        else ir2 in
                                              build_icmp Llvm.Icmp.Sge ir1 ir2 "icmpsgetmp" builder
                               | Tband ->let ir1_i1 = build_trunc_or_bitcast ir1 (i1_type context) "first_cast" builder in
                                         let ir2_i1 = build_trunc_or_bitcast ir2 (i1_type context) "second_cast" builder in
                                         build_and ir1_i1 ir2_i1 "andtmp" builder
                               | Tbor ->
                                        (* let ir1_i1 = build_trunc_or_bitcast ir1 (i1_type context) "first_cast" builder in
                                         let ir2_i1 = build_trunc_or_bitcast ir2 (i1_type context)"second_cast" builder in *)
                                         build_or ir1 ir2 "ortmp" builder
                               | Tbcom ->
                                  ir2
                               | _ -> (Error.error "%s: Unkown binary operator while producing IR" ("") ;const_null integer_type)
                              )
                            )
|Eunas (e,op) ->
  let ir = code_gen_exp e in
  (match op with
   | Tppl ->
      let expr = if (is_double_pointer ir) then Ebop(e, Edoub 1.0,Tbpl)
                 else Ebop(e,Eint 1,Tbpl) in
      let exp = code_gen_exp expr in
      let _ = build_store exp ir builder in
      exp
   | Tmmin ->
      let expr = if (is_double_pointer ir) then Ebop(e, Edoub 1.0,Tbpl)
                 else Ebop(e,Eint 1,Tbmin) in
      let exp = code_gen_exp expr in
      let _ = build_store exp ir builder in
      exp
   | _ -> Error.error "%s: Invalid prefix operator:" ""; const_null integer_type
  )
|Eunas1 (e, op) ->
  let ir = code_gen_exp e in
  (match op with
   | Tppl -> let expr = if (is_double_pointer ir) then Ebop(e, Edoub 1.0,Tbpl)
                        else Ebop(e,Eint 1,Tbpl) in
             let exp = code_gen_exp expr in
             let _ = build_store exp ir builder in
             let sube = if (is_double_pointer exp) then Ebop(e, Edoub 1.0,Tbmin)
                        else Ebop(e,Eint 1,Tbmin) in
             let sub = code_gen_exp sube in
             sub
   | Tmmin -> let expr = if (is_double_pointer ir) then Ebop(e, Edoub 1.0,Tbmin)
                        else Ebop(e,Eint 1,Tbmin) in
             let exp = code_gen_exp expr in
             let _ = build_store exp ir builder in
             let adde = if (is_double_pointer exp) then Ebop(e, Edoub 1.0,Tbpl)
                        else Ebop(e,Eint 1,Tbpl) in
             let add = code_gen_exp adde in
             add

   | _ -> Error.error "%s: Invalid postfix operator:" ""; const_null integer_type
  )

|Ebas (e1,e2, op) ->
  (match op with
   | Tba ->
      (match e2 with
       | Eunas1 (e, op) ->
          let rhs' = code_gen_exp e in
          let rhs = if(is_pointer e) then( build_load rhs' "loadtmp" builder)
                    else rhs' in
          let lhs = code_gen_exp e1 in
          let _ = build_store rhs lhs builder in
          let oper =( match op with
                      | Tppl -> Tbpl
                      | _ -> Tbmin )in
          let adde = if(is_double_pointer rhs') then( Ebop(e,Edoub 1.0,oper))
                     else (  Ebop(e,Eint 1, oper)) in
          let add = code_gen_exp adde in


          let _ = build_store add rhs' builder in
          lhs
       | Eunas(op, e) ->
          let ret_val = code_gen_exp e2 in
          let rhs =  ret_val in
          let lhs = code_gen_exp e1 in
          let _ = build_store rhs lhs builder in
          lhs
       | Enull-> let lhs = code_gen_exp e1 in
                         let lhs4del = build_load lhs "loadforNull" builder in
                         let ty = type_of lhs4del in
                         delete_instruction lhs4del;
                         let null = const_null ty in
                         build_store null lhs builder
      |  Ebas (a,b,c) ->

          (* let _ = code_gen_exp (Ebas(a,b,c)) in *)
          let rhs = code_gen_exp (returnExpr e2) in
          let _ = codegen_multiple_assign e2 rhs in
          let rhs = if(need_def e2) then build_load rhs "tmp" builder else rhs in
          let lhs = getAddress e1 in
          let _ = build_store rhs lhs builder in
          lhs
      | Eunop (expr, Tutim) ->
          let rhs = code_gen_exp e2 in
          let rhs =  build_load rhs "tmp" builder in
          let lhs = getAddress e1 in
          let _ = build_store rhs lhs builder in
          lhs

      | _ -> (* Printf.printf "wx..\n"; *)
          let rhs = code_gen_exp e2 in
          let rhs = if(need_def e2) then build_load rhs "tmp" builder else rhs in
          let lhs = getAddress e1 in
          (* build_pointercast arra (pointer_type t) "tmp" builder *)
          (* let lhs = if(is_op_with_pointer lhs) then (Printf.printf "opwp..\n"; build_inttoptr lhs (pointer_type (type_of lhs)) "inttoptr" builder) else lhs in *)
          let _ = build_store rhs lhs builder in
          lhs
      )
   | _ ->
      let op = (match op with
                | Tbapl -> Tbpl
                | Tbamin -> Tbmin
                | Tbatim -> Tbtim
                | Tbadiv -> Tbdiv
                | Tbamod -> Tbmod
                )
                in
      let expr = Ebop (e1,e2,op) in
      let rhs = code_gen_exp expr in
      let lhs = code_gen_exp e1 in
      build_store  rhs lhs builder
  )

|Ecast (t1, e1) ->let exp =  code_gen_exp e1 in
                    let ty_exp = string_of_lltype(type_of exp) in
                    let exp = try
                        (ignore(String.index ty_exp '*');
                         build_load exp "loadcastingtmp" builder)
                      with Not_found -> ( exp) in
                    if (contains ty_exp "x86_fp80") then (
                      let ty = findLltype t1 in
                      build_fptosi exp ty "castingtmp" builder)
                    else if (contains ty_exp  "i16") then
                      (
                        match t1 with
                        | Tdouble -> let ty = findLltype t1 in
                                         build_sitofp exp ty "castingtmp" builder
                        | _ -> let ty = findLltype t1 in
                               build_trunc_or_bitcast exp ty "castingtmp" builder )
                    else if (contains ty_exp "i8") then
                      (
                       match t1 with
                       | Tint -> let ty = findLltype t1 in
                                     build_sext_or_bitcast exp ty "castingtmp" builder
                       | Tdouble -> let ty = findLltype t1 in
                                        build_sitofp exp ty "castingtmp" builder
                       | _ -> let ty = findLltype t1 in
                              build_trunc_or_bitcast exp ty "castingtmp" builder )
                    else
                      (
                       match t1 with
                       | Tdouble -> let ty = findLltype t1 in
                                        build_sitofp exp ty "castingtmp" builder
                       | _ -> let ty = findLltype  t1 in
                              build_sext_or_bitcast exp ty "castingtmp" builder)

|Eif (e1,e2,e3) ->  let condition = code_gen_exp e1 in
                         let zero = if (String.contains(string_of_lltype(type_of condition)) '1') then  const_int (i1_type context) 0
                                    else const_int (bool_type) 0 in
                         let cond_val = if (is_pointer e1) then build_load condition "loadcon" builder
                                        else condition in
                         let cond_val = build_icmp Icmp.Ne cond_val zero "ifcond" builder in
                         let start_bb = insertion_block builder in
                         let the_function = block_parent start_bb in
                         let then_bb = append_block context "then" the_function in
                         position_at_end then_bb builder;

                         let then_val =  code_gen_exp e2 in
                         let then_val = if (is_pointer e2) then build_load then_val "loadtmp" builder else then_val in
                         let new_then_bb = insertion_block builder in

                         let else_bb = append_block context "else" the_function in
                         position_at_end else_bb builder;
                         let else_val = code_gen_exp e3 in
                         let else_val = if (is_pointer e3) then build_load else_val "loadtmp" builder else else_val in
                         let new_else_bb = insertion_block builder in
                         let merge_bb = append_block context "ifcont" the_function in
                         position_at_end merge_bb builder;
                         let incoming = [(then_val, new_then_bb); (else_val, new_else_bb)] in
                         let phi = build_phi incoming "iftmp" builder in
                         position_at_end start_bb builder;
  ignore (build_cond_br cond_val then_bb else_bb builder);
  position_at_end new_then_bb builder; ignore (build_br merge_bb builder);
  position_at_end new_else_bb builder; ignore (build_br merge_bb builder);
  position_at_end merge_bb builder;
  phi


|Enew (t, None) -> let ty = findLltype t in
                     build_malloc (ty) "malloctmp" builder

|Enew (t, Some e) ->
        let y = code_gen_exp e in
        let y = if(need_def e) then build_load y "tmp" builder else y in
        let t = (ltype_of_type t) in
        let arra = build_array_malloc  t y "tmp" builder in
         build_pointercast arra (pointer_type t) "tmp" builder


|Edel e ->
(* const_null ( i1_type context) *)
 build_free (build_load ( (get_identifier e )) "tmp" builder) builder

  (* let ir = code_gen_exp e in
  let _ = Printf.printf("del\n") in
  build_free ir builder *)

| Enull -> const_pointer_null (pointer_type char_type)

(* | e ->raise (Terrror ("uknow", e)) *)

and convert_to_typical_types t =
  match t with
  | Tarray (t,_) -> Tptr t
  | _ -> t

and convert_type_to_char t =
  match t with
  | Tint -> "i"
  | Tdouble -> "d"
  | Tarray (t,_) -> String.concat "" ["a"; (convert_type_to_char t)]
  | Tchar -> "c"
  | Tbool -> "b"
  | Tptr x -> String.concat "" ["p" ;(convert_type_to_char x)]
  | _ -> ""

and create_suffix type_list =
  let suffix = List.map (fun x -> convert_type_to_char x) type_list in
  String.concat "" suffix


and bool_to_int n =
  match n with
  | false -> 0
  | true -> 1

and is_pointer ex =
(* let _ = Printf.printf("is_pointer\n") in
  let _=Printf.printf  (  match ex with
                    Eid   _-> "Eid"
                   | Ebool  _-> "Ebool"
                   | Enull _-> "Enull"
                   | Eint  _-> "Eint"
                   | Echar  _-> "Echar"
                   | Edoub  _-> "Edoub"
                   | Estr  _-> "Estr"
                   | Eapp  _-> "Eapp"
                   | Eunop _-> "Eunop"
                   | Eunas _-> "Eunas"
                   | Eunas1 _-> "Eunas1"
                   | Ebop  _-> "Ebop"
                   | Ebas _-> "Ebas"
                   | Ecast _-> "Ecast"
                   | Enew  _-> "Enew"
                   | Edel _-> "Edel"
                   | Emat _-> "Emat"
                   | Eif  _-> "Eif"
                   )in *)
  match ex with
  | Eid _ -> true
  | Emat _ -> true
  | Eunop(e,Tutim) ->true
(*   | Eunas (a,_) -> is_pointer a
  | Eunas1 (a,_) -> is_pointer a
 *) (*   | Ebop(e,_,_) -> is_pointer e*)
  (* | Ast.Paren_expression(e) -> is_pointer e *)
  | _ ->  false

and returnExpr a =
  match a with
  Ebas(a,b,c) -> returnExpr b
  | b -> b
and codegen_multiple_assign a rhs =
  match a with
  Ebas(a,b,c) -> (
              codegen_multiple_assign b rhs;
              let lhs = getAddress a in
              let _ = build_store rhs lhs builder in
              lhs

    )
  | _ ->  const_null ( i1_type context);



and is_binary_as ex =
  match ex with
  | Ebop(_,_,_) -> true
  | _ -> false

and is_double ir =
  let ty = string_of_lltype (type_of ir) in
  if((String.compare ty "x86_fp80") == 0) then true
  else false

and is_op_with_pointer ir =
  let ty = string_of_lltype (type_of ir) in
  (* if ((contains ty "*")) then (Printf.printf "heeeeeeereee"; true) *)
  if ((contains ty "*")) then ( true)
  else false

and is_void callee =
  let ty = string_of_lltype (type_of callee) in
  let re = Str.regexp_string "void" in
  try ignore (Str.search_forward re ty 0); true
  with Not_found -> false

and is_double_pointer ir =
  let ty = string_of_lltype (type_of ir) in
  if (contains ty "x86") then true
  else false
and need_def = function
        | Eid _ -> true
        | Emat _ ->true
(*         | Estr _ ->true
 *)        (* |(* Eplus (e1,_) | Ediv (e1,_) | Eminus (e1,_) | Emod (e1,_) | Emod (e1,_) | Emult (e1,_) | Eand (e1,_) | Eor (e1,_) | *)(*| EUnAdd e1 |EUnMinus e1 *) EPlusPlus (e1,_) | EMinusMinus (e1,_)  -> false *)
        |  _->false
and default_val_type smth =
        match smth with
        | Tint ->  const_int (ltype_of_type smth) 0
        | Tbool -> const_int (ltype_of_type smth) 0
        | Tchar -> const_int (ltype_of_type smth) 0
        | Tdouble -> const_float (ltype_of_type smth) 0.0
        | Tvoid -> const_int (ltype_of_type smth) 0
and  ltype_of_type = function
        | Tint ->  i16_type context
        | Tbool -> i1_type context
        | Tchar -> i8_type context
        | Tdouble ->x86fp80_type context
        | Tvoid -> void_type context
        | Tptr t -> pointer_type (ltype_of_type t)
        | Tarray (a,b) ->array_type (ltype_of_type a) b
        | Tnone -> ltype_of_type Tvoid
and getAddress expr =
 (* Printf.printf "getAddress\n"; *)
 match expr with
 Eid(x) ->  Hashtbl.find named_values  x
 (* | Ebas(a,b,c) ->Printf.printf "d---f";code_gen_exp(Ebas(a,b,c)); code_gen_exp b *)
 | Emat(x,y) ->
          let index = code_gen_exp y in let index =  if(need_def y) then build_load index "tmp" builder else index in
          let tmp_val = (match x with
           | Emat (Eid(a), y) -> build_load (get_identifier x ) "tmp" builder
           | Emat _ -> (* Printf.printf "Double array!\n"; *) (getAddress x)
           | _ -> build_load (get_identifier x ) "tmp" builder) in
         let dereference = build_gep tmp_val  [|index|] "arrayval" builder in dereference
 | Eunop (x, Tuamp) -> Printf.printf "SOS!\n"; let y =  (get_identifier x) in
        let dereference = build_struct_gep y 0 "tmp" builder in build_load dereference "tmp" builder
 | Eunop (x, Tutim) ->
(*         Printf.printf "shit...\n";
 *)        (match x with
                | Eid(a) -> (let y = Hashtbl.find named_values  a in
                             let load_ = build_load y "temp" builder in 
                             load_ ) 
                | _ -> code_gen_exp x)
(*         let y =  (get_identifier x) in
        let load_ = build_load y "temp" builder in 
        load_
 *) 
  | e -> 
  Printf.printf "getAddress problem!\n";
  (* print_expr e;  *)
  code_gen_exp e

and get_identifier s = match s with
       Eid(a) ->Hashtbl.find named_values  a
       |_ -> code_gen_exp s


        and print_expr e =
        Printf.printf "get_identifier\n";
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

and may f = function

  | None -> ()

  | Some v -> f v



and map f = function

  | None -> None

  | Some v -> Some (f v)



and default v = function

  | None -> v

  | Some v -> v



and is_some = function

  | None -> false

  | _ -> true



and is_none = function

  | None -> true

  | _ -> false



and get = function

  | None -> raise No_value

  | Some v -> v



and map_default f v = function

  | None -> v

  | Some v2 -> f v2

let get_some = get;;
let get_some1 = get;;



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
          else if(List.exists (fun x -> (Pervasives.compare d1 x) = -1) defs) then -1 (*a def is smaller than*)
          else (match d2, d1 with
                |Fundefi(_,n1,_,dec1,_), Fundefi(_,n2,_,dec2,_) ->
                  if(n1 = n2) then 0 else(
                    let (defs,decs) = List.partition (fun x -> match x with Fundefi _ -> true |_ -> false) dec2 in
                    if(List.exists (dec_with_name n1) decs ) then 1
                    else if(List.exists (fun x -> (Pervasives.compare d1 x) = -1) defs) then 1 else 0) (*a def is smaller than*)
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

  let rec codegen_main prog =
    let _ = codegen_lib() in
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

       (* print_ast_type ty; *)
       let typos = type_to_lltype ty in (*we want the type of the vars *)
       let value = init_value ty in (* NOT SURE IF WE WANT THE POINTER TO BE NULL AT FIRST *)
       let _ = match !env with
         | Global (_) -> let _ = List.iter (fun x -> match x with
                                                     | Ast.Decl(name,e) ->
                                                     ignore(env := update_env name (!env))
                                                     (* | Ast.Complex_declarator(name, _) -> ignore(env := update_env name (!env)) *)
                                                     )
                                           decs
                         in
                         global_decs := Ast.Vardecl(ty,decs)::!global_decs;
         (* Printf.printf "New length:%d\n" (List.length !global_decs) *)
         | Nested _ ->ignore(
                          List.map (fun dec ->
                              match dec with
                              | Ast.Decl(name,ex) ->(
                                  match ex with
                                  | Some e->(
                                     (* print_expr e; *)
                                  let leng = code_gen_exp e in
                                  let decl = build_alloca (pointer_type typos) name builder in
                                  let alloca = build_array_malloc (typos) leng "allocatmp" builder in
                                  let _ = build_store alloca decl builder in 
                                  Hashtbl.add named_values name decl;
                                  env := update_env name !env
                                  (* let malloc = build_alloca ( pointer_type typos ) name builder in *)
                                  (* let _ = Hashtbl.add named_values name malloc in *)
                                  (* let arr = build_array_malloc typos (code_gen_exp (e) ) "mallocttmp" builder in let arr = build_bitcast arr (pointer_type typos) "tmp" builder  in let _ = build_store arr malloc builder in malloc *)
                                  (* ;() *)
                                  )
                                  | _ -> (
                                  let alloca = build_alloca typos name builder in
                                 ignore(build_store value alloca builder);
                                 Hashtbl.add named_values name alloca;
                                 env := update_env name (!env)
                                 )

                            )
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
                 (*let _ = match ty with |Tnone -> ignore(update_env name !env) | _ ->() in *) (*Add the env_params*)
                 (* match ty with Tnone -> () | _ -> Hashtbl.add named_values name a) *)
                 (*Tnone == env_variable already added. We don't want dubplicates*)
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
       (* match else_stm with *)
       (* | None -> *)
         let y = code_gen_exp cond in
         let lval = if(need_def cond) then build_load y "tmp" builder else y in
         let cond_val = build_icmp Icmp.Ne lval (const_int (i1_type context) 0) "ifcond" builder in
         let start_bb = insertion_block builder in
         let the_function =block_parent start_bb in
         let then_bb =append_block context "then" the_function in
         position_at_end then_bb builder;
         let then_val =codegen_statement stm in
         let new_then_bb =insertion_block builder in
         let else_bb = append_block context "else" the_function in
         position_at_end else_bb builder;
         let else_val = if is_some else_stm then codegen_statement (get else_stm) else code_gen_exp (Enull) in
         let new_else_bb =insertion_block builder in
         let merge_bb= append_block context "ifcond" the_function in
         position_at_end merge_bb builder;
         let else_bb_v=value_of_block new_else_bb in
         position_at_end start_bb builder;

         ignore(build_cond_br cond_val then_bb else_bb builder);
         position_at_end new_then_bb builder; ignore(build_br merge_bb builder);
         position_at_end new_else_bb builder; ignore(build_br merge_bb builder);
         position_at_end merge_bb builder ;
                  else_bb_v)

    (*| Some elsestm ->
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
    *)
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
         | Some exp ->(
           match exp with
           | Eid a -> code_gen_exp (Ebop(((Eid a),Ebool(true),Tbeq)))
           | _ -> code_gen_exp exp
           )
          (* let tmp = code_gen_exp exp in if (is_pointer exp) then build_load tmp "loadcon" builder else
                                                       tmp *)

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
                             if(is_pointer exp) then build_load ret_val "ret" builder
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
and print_expr e =
(* Printf.printf "!!!"; *)
 Printf.printf  (  match e with
                    Eid _  -> "Eid"
                    | Ebool _  -> "Ebool"
                    | Enull -> "Enull"
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
(*   Printf.printf "!!!"
 *)  and print_opt_expr e =(
    match e with
    | Some ex-> ()
    | _ -> ()
    )
    and print_ast_type ast =
      match ast with
      | Tint -> Printf.printf "int ";
      | Tchar -> Printf.printf "char ";
      | Tbool -> Printf.printf "bool ";
      | Tdouble -> Printf.printf "double ";
      | Tptr (typ1) -> print_ast_type typ1; Printf.printf "*";
      | Tarray (typ1,i) -> print_ast_type typ1; Printf.printf "["; Printf.printf "%d" i; Printf.printf "]";
      (* | Tvoid -> fprintf "void ";
      | Tnone -> fprintf "None type, probably an error "; *)

 and codegen_lib () =
                 let _ = Hashtbl.add named_values ("writeString")  (declare_function "writeString" (function_type (type_to_lltype Tvoid) [|type_to_lltype(Tptr Tchar)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("writeInteger")  (declare_function "writeInteger" (function_type (type_to_lltype Tvoid) [|type_to_lltype(Tint)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("writeBoolean")  (declare_function "writeBoolean" (function_type (type_to_lltype Tvoid) [|type_to_lltype(Tbool)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("writeChar")  (declare_function "writeChar" (function_type (type_to_lltype Tvoid) [|type_to_lltype(Tchar)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("writeReal")  (declare_function "writeReal" (function_type (type_to_lltype Tvoid) [|x86fp80_type context|]) the_module ) in
                 let _ = Hashtbl.add named_values ("readInteger")  (declare_function "readInteger" (function_type (type_to_lltype Tint) [||]) the_module ) in
                 let _ = Hashtbl.add named_values ("readBoolean")  (declare_function "readBoolean" (function_type (type_to_lltype Tbool) [||]) the_module ) in
                 let _ = Hashtbl.add named_values ("readChar")  (declare_function "readChar" (function_type (type_to_lltype Tchar) [||]) the_module ) in
                 let _ = Hashtbl.add named_values ("readReal")  (declare_function "readReal" (function_type (type_to_lltype Tdouble) [||]) the_module ) in
                 let _ = Hashtbl.add named_values ("readString")  (declare_function "readString" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tint ; type_to_lltype (Tptr Tchar)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("abs")  (declare_function "abs" (function_type (type_to_lltype Tint) [|type_to_lltype Tint |]) the_module ) in
                 let _ = Hashtbl.add named_values ("fabs")  (declare_function "fabs" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("sqrt")  (declare_function "sqrt" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("sin")  (declare_function "sin" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("cos")  (declare_function "cos" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("tan")  (declare_function "tan" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("atan")  (declare_function "atan" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("exp")  (declare_function "exp" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("ln")  (declare_function "ln" (function_type (type_to_lltype Tdouble) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("pi")  (declare_function "pi" (function_type (type_to_lltype Tdouble) [| |]) the_module ) in
                 let _ = Hashtbl.add named_values ("trunc")  (declare_function "trunc" (function_type (type_to_lltype Tint) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("round")  (declare_function "round" (function_type (type_to_lltype Tint) [|type_to_lltype Tdouble |]) the_module ) in
                 let _ = Hashtbl.add named_values ("ord")  (declare_function "ord" (function_type (type_to_lltype Tint) [|type_to_lltype Tchar |]) the_module ) in
                 let _ = Hashtbl.add named_values ("chr")  (declare_function "chr" (function_type (type_to_lltype Tchar) [|type_to_lltype Tint |]) the_module ) in
                 let _ = Hashtbl.add named_values ("strlen")  (declare_function "strlen" (function_type (type_to_lltype Tint) [|type_to_lltype (Tptr Tchar) |]) the_module ) in
                 let _ = Hashtbl.add named_values ("strcmp")  (declare_function "strcmp" (function_type (type_to_lltype Tint) [|type_to_lltype (Tptr Tchar) ; type_to_lltype (Tptr Tchar)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("strcpy")  (declare_function "strcpy" (function_type (type_to_lltype Tvoid) [|type_to_lltype (Tptr Tchar) ; type_to_lltype (Tptr Tchar)|]) the_module ) in
                 let _ = Hashtbl.add named_values ("strcat")  (declare_function "strcat" (function_type (type_to_lltype Tvoid) [|type_to_lltype (Tptr Tchar) ; type_to_lltype (Tptr Tchar)|]) the_module ) in
                 ();;

