open Llvm
(*open Ast 
open Types 
exception Error of string

let context = global_contect ()
let the_module = create_module context "My cmp "
let builder = builder context
let named_values:(string, llvalue) Hashtbl.t =Hashtbl.create 10
type binary_ops = Plus|Minus|Div|Mult|Mod|And|Or|Comma|Lt|Lte|Eq|Neq|Gt|Gte
let create_entry_block_alloca func var_name = 
        let builder =builder_at (instr_begin (entry_block func)) in
        build_alloca (var_type ) var_name builder
let rec ltype_of_type = function 
        | TYPE_int ->  i32_type context 
        | TYPE_bool -> i1_type context
        | TYPE_char -> i8_type context 
        | TYPE_double -> double_type context 
        | TYPE_void -> void_type context
        | TYPE_pointer t -> pointer_type (ltype_of_type t)
        | TYPE_array (a,b) -> array_type (ltype_of_type a) b
        | TYPE_proc -> ltype_of_type TYPE_void
let default_val_type smth = match smth with 
        | TYPE_int ->  const_int (ltype_of_type smth) 0
        | TYPE_bool -> cont_int (ltype_of_type smth) 0
        | TYPE_char -> cont_int (ltype_of_type smth) 0
        | TYPE_double -> const_float (ltype_of_type smth) 0.0
        | TYPE_void -> const_int (ltype_of_type smth) 0
let rec codegen_stmt stmt builder= match stmt with 
        SExpr (Some a) ->  codegen_expr a
        |SNewblock a -> List.map (codegen_stmt builder) a
        |Sfor (a,b,c,d,e,f) -> codegen_for_loop a b c d e f
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
        |SBreak (Some a) ->
        |SCont (Some a) ->
        |SBreak _ ->
        |Scont _ ->
        |_ -> codegen_expr (Enull) builder;;
and codegen_for_loop 
and let rec codegen_expr builder= match expr with
        |Eint a -> const_int (ltype_of_type TYPE_int) a
        |Ereal a -> const_float (ltype_of_type TYPE_double) a
        |Echar a -> const_int (ltype_of_type TYPE_char) (Char.to_int a)
        |Eid a ->let v= try Hashtbl.find named_values a with |Not_found -> raise (Error "uknown variable name") in build_load v name builder
        |Estring a-> build_global_stringptr s "tmp" builder
        |Ebool a -> const_int (ltype_of_type TYPE_bool) (if a then 1 else 0)
        |Enull -> (*NOP *)
        |EAmber a ->
        |EPointer a->
        |EUnAdd a->
        |EUnMinus a -> let lval = codegen_expr a builder in let type_is = (* type get*)
                                in let type_m m= match m  with 
                                TYPE_int -> build_neg lval "int_unoptmp" builder
                                | TYPE_double -> build_fneg lval "flt_unotmp" builder
                                in type_m type_is
        |Eplus (a,b) -> codegen_binary a b Plus builder
        |Eminus (a,b) -> codegen_binary a b Minus builder
        |Ediv (a,b) ->codegen_binary a b Div builder
        |Emult (a,b) -> codegen_binary a b Mult builder 
        |Emod (a,b) -> codegen_binary a b Mod builder 
        |Eand (a,b) -> codegen_binary a b And builder 
        |EOr (a,b) -> codegen_binary a b Or builder
        |Ecomma (a,b) -> codegen_binary a b Comma builder 
        |Elt (a,b) -> codegen_expr a b Lt builder 
        |Elte (a,b) -> codegen_expr a b Lte builder 
        |Egt (a,b) -> codegen_expr a b Gt builder 
        |Egte (a,b) -> codegen_expr a b Gte builder 
        |Eeq (a,b) -> codegen_expr a b Eq builder 
        |Enot a -> let lval = codegen_expr a builder in build_not lval "nottmp" builder 
        |EplusPlus (a,b)-> 
        |EMinusMinus (a,b)-> 
        |EAssignEq (a,b)-> codegen_assign (codegen_expr a builder) (codegen_expr b builder) builder 
        |EplusEq (a,b) -> let value = codegen_expr Eplus(a,b) builder in codegen_assign (codegen_expr a builder ) value builder
        |EMinusEq (a,b) -> let value = codegen_expr EMinus(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |EDivEq (a,b) -> let value = codegen_expr Ediv(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |EDotEq (a,b) -> let value = codegen_expr Emult(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |EModEq (a,b) -> let value = codegen_expr Emod(a,b) builder in codegen_assign (codegen_expr a builder) value builder
        |Enew (a,b) ->
        |EDel a ->
        |Ecast (a,b)->
        |Eapp
        |ECall
        |EArray (a,b)
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

let codegen_func func =
        let name = func.entry_name in
        let parametres = List.map (fun x-> ltype_of_type x.entry_info.parameter_type) (func.entry_info.function_paramlist) in
        let fuction_type = function_type (ltype_of_type func.entry_info.function_result) (Array.of_list parametres) in
        define_function name function_type the_module ;;

let make_function func1 = match func1 with FunDef (func,b,c) -> 
        let name = func.entry_name in
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
                        ignore(build_ret (default_val_type TYPE_int) builder);;


let getAdreess expr builder =  match expr with 
 Eid(x) ->  findinHash x
 |EAmber (x)->  let y = findinHash x in
        let dereference = build_struct_gep y 0 "tmp" in build_load dereference "tmp" builder
 |EPointer (x)-> let y = findinHash x in let load_ = build_load y "temp" builder in
        let dereference = build_struct_gep load_ 0 "tmp" in dereference 
 |EArray(x,y) -> let index = codegen_expr y builder in  let tmp_val = findinHash x in
 let dereference = build_gep tmp_val  [|0;index|] "arrayval" builder in dereference 

let codegen_main main = 



*)