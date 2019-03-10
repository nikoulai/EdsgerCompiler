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
   | Tchar           -> 1
   | Tbool           -> 1
   | Tdouble         -> 10
   | Tptr et          -> 2
   | Tarray (et, sz) -> sz * sizeOfType et (*immutable pointer has fixed size*)
   | _                   -> 0

let rec equalType t1 t2 =
   match t1, t2 with
   | Tarray (et1, sz1), Tarray (et2, sz2) -> equalType et1 et2
   | Tptr et1, Tptr et2                   -> equalType et1 et2
   | _                                            -> t1 = t2
