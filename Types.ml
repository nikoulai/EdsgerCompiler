type typ = Tnone
         | Tint
         | Tchar
         | Tbool
         | Tdouble
         | Tptr of typ
         | Tarray of typ * int (*immutable pointer*)
         | Tvoid

let rec sizeOfType t =
   match t with
   | Tint            -> 2
   | Tchar           -> 8
   | Tbool           -> 1
   | Tdouble         -> 10
   | Tptr et          -> 1
   | Tarray (et, sz) -> sz * sizeOfType et (*immutable pointer has fixed size*)
   | _                   -> 0

let rec equalType t1 t2 =
   (* Printf.printf "comparetypes";print_expr t1;print_expr t2; *)
   match t1, t2 with
   | Tarray (et1, sz1), Tarray (et2, sz2) -> equalType et1 et2
   | Tptr et1, Tarray (et2, _)            -> equalType et1 et2
   | Tarray (et2, _), Tptr et1            -> equalType et1 et2
   | Tptr Tnone, Tptr et2                 -> true
   | Tptr et1, Tptr Tnone                 -> true
   | Tptr et1, Tptr et2                   -> equalType et1 et2
   | _                                    -> t1 = t2

 and print_expr e =
    Printf.printf  (  match e with
                | Tnone  _ -> "Tnone"
               | Tint _ -> "Tint"
               | Tchar _  -> "Tchar"
               | Tbool _  -> "Tbool"
               | Tdouble  _ -> "Tdouble"
               | Tptr  _ -> "Tptr"
               | Tarray  _  -> "Tarray"
               | Tvoid  _ -> "Tvoid"

                      );
