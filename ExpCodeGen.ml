open Types
open Symbol
open Ast
open Identifier
open Llvm
open Error
open Char

exception Type_error of string
exception No_value
exception Terrror of string*ast_expr

type environment = Global of (string list)| Nested of (string list * environment)
module SS = Set.Make(String)
let context = global_context ()
let the_module = create_module context "LLVM IR"
let builder = builder context
let named_values:(string, llvalue) Hashtbl.t = Hashtbl.create 10
let int_type = i16_type context
let double_type =  x86fp80_type context
let char_type = i8_type context
let bool_type = i1_type context
let fun_names : string list ref = ref []
let env:environment ref = ref (Global ([]))
let global_decs : (Ast.ast_declaration) list ref = ref []

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
                                    |Ast.Decl _ -> pointer_type ty

                                    )
       | _ -> Printf.printf "unexpected type"; int_type
  in
  let find_type name =
    try
      let v =
        try Hashtbl.find named_values name
        with Not_found -> raise Not_found
      in (type_of v)
    with Not_found ->Printf.printf "ONLY LOOKING IN G";  find_type_from_global name global_decs
  in
  List.map find_type env



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
  | Eint int -> let value = const_int int_type int in
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
| Emat (e1, e2) -> Printf.printf"Emat\n";
                    let pointer = code_gen_exp e1 in
                    let act_array = build_load pointer "act_ar" builder in
                    let index = code_gen_exp e2 in
                    let index = if (is_pointer e2) then build_load index "tmpindex" builder
                                else index in
                    let index = Array.of_list [index] in
                    let ir = build_gep act_array index "arraytmp" builder in
                    ir
| Eunop (e,op) -> (match op with
                      |  Tuamp->
                        Printf.printf"Ampersand\n"; code_gen_exp e
                      | Tutim -> 
                       Printf.printf"Dereferencing\n";
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
                              (match op with
                               | Tbpl ->  if(is_double ir1) then build_fadd ir1 ir2 "faddtmp" builder
                                         else if (is_op_with_pointer ir1) then code_gen_exp (Emat(e1,e2))
                                         else if (is_op_with_pointer ir2) then code_gen_exp (Emat(e2,e1))
                                         else build_add ir1 ir2 "addtmp" builder
                               | Tbmin ->  if(is_double ir1) then build_fsub ir1 ir2 "fsubtmp" builder
                                         else if (is_op_with_pointer ir1) then code_gen_exp (Emat(e1,e2))
                                         else if (is_op_with_pointer ir2) then code_gen_exp (Emat(e2,e1))
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
                                             let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Eq ir1 ir2 "icmpeqtmp" builder
                                   (* build_icmp Llvm.Icmp.Eq ir1 ir2 "icmpeqtmp" builder *)
                               | Tbneq -> if (e1 = Enull) then build_is_null ir2 "is_null" builder
                                         else if (e2 = Enull) then build_is_null ir1 "is_null" builder
                                         else if ((e1 = Enull) && (e2 = Enull)) then code_gen_exp (Ebool false)
                                         else
                                           if(is_double ir1) then build_fcmp Llvm.Fcmp.One ir1 ir2 "icmpeqtmp" builder
                                           else
                                             let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Ne ir1 ir2 "icmpeqtmp" builder
                               | Tblss ->  if(is_double ir1) then build_fcmp Llvm.Fcmp.Olt ir1 ir2 "icmpslttmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
                                                        else ir2 in
                                              build_icmp Llvm.Icmp.Slt ir1 ir2 "icmpslttmp" builder
                               | Tbgrt -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Ogt ir1 ir2 "icmpsgttmp" builder
                                        else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                       else ir1 in
                                             let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
                                                       else ir2 in
                                             build_icmp Llvm.Icmp.Sgt ir1 ir2 "icmpsgttmp" builder
                               | Tbleq -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Ole ir1 ir2 "icmpsletmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
                                                        else ir2 in
                                              build_icmp Llvm.Icmp.Sle ir1 ir2 "icmpsletmp" builder
                               | Tbgeq -> if(is_double ir1) then build_fcmp Llvm.Fcmp.Oge ir1 ir2 "icmpsgetmp" builder
                                         else let ir1 = if(is_op_with_pointer ir1) then build_ptrtoint ir1 (int_type) "ptrtoint" builder
                                                        else ir1 in
                                              let ir2 = if (is_op_with_pointer ir2) then build_ptrtoint ir2 (int_type) "ptrtoint" builder
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
                               | _ -> (Error.error "%s: Unkown binary operator while producing IR" ("") ;const_null int_type)
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
   | _ -> Error.error "%s: Invalid prefix operator:" ""; const_null int_type
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

   | _ -> Error.error "%s: Invalid postfix operator:" ""; const_null int_type
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

          | _ ->
          let rhs = code_gen_exp e2 in 
          let rhs = if(need_def e2) then build_load rhs "tmp" builder else rhs in
          let lhs = getAddress e1 in
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

|Enew (t, Some e) -> let ty = findLltype t in
                       let ir = code_gen_exp e in
                       let ir = if is_pointer e then build_load ir "loadtmp" builder else ir in
                       build_array_alloca (ty) ir "mallocarraytmp" builder

|Edel e ->
  let ir = code_gen_exp e in
  let _ = Printf.printf("del\n") in
  build_free ir builder

| Enull ->build_add (default_val_type Tint) (default_val_type Tint) "tmp" builder

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

and is_pointer ex =let _ = Printf.printf("is_pointer\n") in
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
                   )in
  match ex with
  | Eid _ -> true
  | Emat _ -> true
  | Eunop(e,Tutim)->true
 (*   | Ebop(e,_,_) -> is_pointer e
 *)  (* | Ast.Paren_expression(e) -> is_pointer e *)
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
        (* |(* Eplus (e1,_) | Ediv (e1,_) | Eminus (e1,_) | Emod (e1,_) | Emod (e1,_) | Emult (e1,_) | Eand (e1,_) | Eor (e1,_) | *)(*| EUnAdd e1 |EUnMinus e1 *) EPlusPlus (e1,_) | EMinusMinus (e1,_)  -> false *)
        |  _->false
and default_val_type smth =
        match smth with
        | Tint ->  const_int (ltype_of_type smth) 0
        | Tbool -> const_int (ltype_of_type smth) 0
        | Tchar -> const_int (ltype_of_type smth) 0
        | Tdouble -> const_float (ltype_of_type smth) 0.0
        | Tvoid -> const_int (ltype_of_type smth) 0
and  ltype_of_type = function
        | Tint ->  i32_type context
        | Tbool -> i1_type context
        | Tchar -> i8_type context
        | Tdouble ->x86fp80_type context
        | Tvoid -> void_type context
        | Tptr t -> pointer_type (ltype_of_type t)
        | Tarray (a,b) ->array_type (ltype_of_type a) b
        | Tnone -> ltype_of_type Tvoid
and getAddress expr =  Printf.printf "getAddress\n"; match expr with
 Eid(x) ->  Hashtbl.find named_values  x
 (* | Ebas(a,b,c) ->Printf.printf "d---f";code_gen_exp(Ebas(a,b,c)); code_gen_exp b *)
 | Emat(x,y) -> let index = code_gen_exp y in let index =  if(need_def y) then build_load index "tmp" builder else index in
         let tmp_val =  build_load (get_identifier x ) "tmp" builder in
         let dereference = build_gep tmp_val  [|index|] "arrayval" builder in dereference
 | e -> Printf.printf "getAddress!\n"; print_expr e; code_gen_exp e
 (* const_null ( i1_type context) *)
 (* | e -> (
   match e with
   |Tuamp(x)->  let y =  (get_identifier x ) in
          let dereference = build_struct_gep y 0 "tmp" builder in build_load dereference "tmp" builder
   | v  ->
    match v with
   |Tptr(x)-> let y =  (get_identifier x ) in let load_ = build_load y "temp" builder in load_
   )
 *)

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
