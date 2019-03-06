open Ast
open Format
open List

exception Terminate of string

let rec check ast =
  match ast with
  | None      -> raise (Terminate "AST is empty")
  | Some tree -> check_program tree

and check_program defs =
  let _ = List.fold_left (fun funs def -> check_fun_def def funs) [] defs in
  ()

and check_fun_def def funs =
  match def with
  | Fundef (name, params, vars, stmts) ->
    let funs' = (name, List.length params) :: funs in
    let env = (List.map param_name params) @ vars in
    List.iter (fun stmt -> check_stmt stmt funs env) stmts;
    funs'

and param_name param =
  match param with
  | Param name -> name
  | ParamByRef name -> name

and check_stmt tree funs env =
  match tree with
  | Sprint expr -> check_expr expr funs env
  | Slet (var, expr) -> (try let _ = List.find (fun elem -> elem = var) env in ()
                         with Not_found -> raise (Terminate ("Unbound variable " ^ var)));
                        check_expr expr funs env
  | Sbegin stmts     -> List.iter (fun stmt -> check_stmt stmt funs env) stmts
  | Sfor (var, expr1, expr2, stmt) -> check_expr expr1 funs env;
                                      check_expr expr2 funs env;
                                      check_stmt stmt funs env
  | Swhile (expr, stmt)            -> check_expr expr funs env;
                                      check_stmt stmt funs env
  | Sif (expr, stmt, maybe_stmt)   -> check_expr expr funs env;
                                      check_stmt stmt funs env;
                                      (match maybe_stmt with
                                       | None -> ()
                                       | Some else_stmt -> check_stmt else_stmt funs env)
  | Sreturn expr -> check_expr expr funs env

and check_expr tree funs env =
  match tree with
  | Enum i   -> ()
  | Eid name -> (try let _ = List.find (fun elem -> elem = name) env in ()
                 with Not_found -> raise (Terminate ("Unbound variable " ^ name)));
  | Ebool b  -> ()
  | Eplus (expr1, expr2)  -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Eminus (expr1, expr2) -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Ediv (expr1, expr2)   -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Emult (expr1, expr2)  -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Eand (expr1, expr2)   -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Eor (expr1, expr2)    -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Elt (expr1, expr2)    -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Egt (expr1, expr2)    -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Eeq (expr1, expr2)    -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Eneq (expr1, expr2)   -> check_expr expr1 funs env;
                             check_expr expr2 funs env
  | Enot expr             -> check_expr expr funs env
  | Eunary expr           -> check_expr expr funs env
  | Eapp (name, exprs)    -> List.iter (fun e -> check_expr e funs env) exprs;
                             try let actual = List.length exprs in
                                 let expected = List.assoc name funs in
                                 if actual <> expected
                                 then raise (Terminate ("Calling function " ^ name ^ 
                                                        ". Expected " ^ (string_of_int expected) ^ 
                                                        " arguments. Found " ^ string_of_int actual))
                                 else ()
                             with Not_found -> raise (Terminate ("Unknown function " ^ name))

(* Type Inference *)

type typ =
  | Tvar of int
  | Tint
  | Tbool
  | Tunit

let cnt = ref 0
let fresh () =
  incr cnt;
  Tvar !cnt

let rec infer ast =
  match ast with
   | None      -> raise (Terminate "AST is empty")
   | Some tree -> let cs = gen tree in
                  print_constraints cs;
                  let _ = unify cs in
                  ()

and gen defs =
  let (cs', _) = List.fold_left (fun (cs, funs) def -> gen_fun_def def funs cs) ([], []) defs in
  cs'

and gen_fun_def def funs cs =
  let tvar = fresh() in
  match def with
  | Fundef (name, params, vars, stmts) ->
    let ps = List.map gen_param params in
    let funs' = (name, (tvar, ps)) :: funs in
    let env = (List.map (fun v -> (v, fresh())) vars) @ ps in
    let (ret, cs') = gen_stmts stmts funs env in
    let cs'' = [(tvar, ret)] @ cs @ cs' in
    (cs'', funs')

and gen_param p =
  match p with
  | Param name -> (name, fresh())
  | ParamByRef name -> (name, fresh())

and gen_stmts stmts funs env =
  match stmts with
  | [] -> (Tunit, [])
  | h::t -> (match gen_stmt h funs env with
             | (Tunit, cs) -> let (tp, cs') = gen_stmts t funs env in
                              (tp, cs @ cs')
             | (tp, cs') as ret -> ret)

and gen_stmt tree funs env =
  match tree with
  | Sprint expr      -> let (_, cs) = gen_expr expr funs env in 
                        (Tunit, cs)
  | Slet (var, expr) -> let (tp1, cs) = gen_expr expr funs env in
                        let tp2 = List.assoc var env in
                        let cs' = (tp1, tp2) :: cs in
                        (Tunit, cs')
  | Sbegin stmts     -> gen_stmts stmts funs env
  | Sfor (var, expr1, expr2, stmt) -> let (tp1, cs1) = gen_expr expr1 funs env in
                                      let (tp2, cs2) = gen_expr expr2 funs env in
                                      let (tp, cs) = gen_stmt stmt funs env in
                                      let cs' = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 @ cs in
                                      (tp, cs')
  | Swhile (expr, stmt) -> let (tp1, cs1) = gen_expr expr funs env in
                           let (tp2, cs2) = gen_stmt stmt funs env in
                           let cs'' = [(tp1, Tbool)] @ cs1 @ cs2 in
                           (tp2, cs'')
  | Sif (expr, stmt, maybe_stmt) -> let (tp1, cs1) = gen_expr expr funs env in
                                    let (tp2, cs2) = gen_stmt stmt funs env in
                                    (match maybe_stmt with
                                     | None           -> let cs' = [(tp1, Tbool)] @ cs1 @ cs2 in
                                                         (tp2, cs')
                                     | Some else_stmt -> let (tp3, cs3) = gen_stmt else_stmt funs env in
                                                         let cs' = [(tp1, Tbool); (tp2, tp3)] @ cs1 @ cs2 @ cs3 in
                                                         (tp3, cs'))
  | Sreturn expr -> gen_expr expr funs env

and gen_expr tree funs env =
  match tree with
  | Enum i   -> (Tint, [])
  | Eid name -> (List.assoc name env, [])
  | Ebool b  -> (Tbool, [])
  | Eplus (expr1, expr2)  -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tint, cs)
  | Eminus (expr1, expr2) -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tint, cs)
  | Ediv (expr1, expr2)   -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tint, cs)
  | Emult (expr1, expr2)  -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tint, cs)
  | Eand (expr1, expr2)   -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tbool); (tp2, Tbool)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Eor (expr1, expr2)    -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tbool); (tp2, Tbool)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Elt (expr1, expr2)    -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Egt (expr1, expr2)    -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, Tint); (tp2, Tint)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Eeq (expr1, expr2)    -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, tp2)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Eneq (expr1, expr2)   -> let (tp1, cs1) = gen_expr expr1 funs env in
                             let (tp2, cs2) = gen_expr expr2 funs env in
                             let cs = [(tp1, tp2)] @ cs1 @ cs2 in
                             (Tbool, cs)
  | Enot expr   -> let (tp, cs) = gen_expr expr funs env in
                   let cs' = (tp, Tbool) :: cs in
                   (Tbool, cs')
  | Eunary expr -> let (tp, cs) = gen_expr expr funs env in
                   let cs' = (tp, Tint) :: cs in
                   (Tint, cs')
  | Eapp (name, exprs) -> let l = List.map (fun e -> gen_expr e funs env) exprs in
                          let (ts, cs) = unzip l [] [] in
                          let (ret, ps) = List.assoc name funs in
                          let tp = fresh() in
                          let cs' = (ret, tp) :: cs in
                          let cs'' = bind_actual_params ps ts cs' in
                          (tp, cs'')

and bind_actual_params ps ts cs =
  match (ps, ts) with
  | ([], []) -> cs
  | ((_, tp1)::r1, tp2::r2) -> bind_actual_params r1 r2 ((tp1, tp2) :: cs)
  | _ -> cs

and unzip l l1 l2 =
  match l with
  | []        -> (l1, l2)
  | (x, y)::r -> unzip r (x :: l1) (y @ l2)

(* Pretty print constraints *)

and print_constraints cs =
  printf "%a" pp_csts cs

and pp_csts ppf cs =
  force_newline ();
  printf "*** Pretty Printing Type Constraints ***";
  force_newline ();
  printf "****************************************";
  force_newline ();
  List.iter (fun c -> pp_cst ppf c) cs

and pp_cst ppf cst =
  match cst with
  | (t1, t2) ->
    pp_typ ppf t1;
    fprintf ppf " = ";
    pp_typ ppf t2;
    force_newline ()

and pp_typ ppf typ =
  match typ with
  | Tvar i -> fprintf ppf "#%d" i
  | Tint -> fprintf ppf "int"
  | Tbool -> fprintf ppf "bool"
  | Tunit -> fprintf ppf "unit"

(* W Algorithm *)

and notfree alpha tau = match tau with
  | Tvar n -> n <> alpha
  | _ -> true

and sub s tau = match tau with
  | Tvar n -> (try List.assoc n s with Not_found -> tau)
  | typ    -> typ

and subc alpha tau c =
  let s = [(alpha, tau)] in
  let walk (tau1, tau2) = (sub s tau1, sub s tau2) in
  List.map walk c

and unify c = match c with
  | [] -> []
  | (tau1, tau2) :: c when tau1 = tau2 -> unify c
  | (Tvar alpha, tau2) :: c when notfree alpha tau2 ->
    (alpha, tau2) :: unify (subc alpha tau2 c)
  | (tau1, Tvar alpha) :: c when notfree alpha tau1 ->
    (alpha, tau1) :: unify (subc alpha tau1 c)
  | _ -> raise (Terminate  "Type Error")
