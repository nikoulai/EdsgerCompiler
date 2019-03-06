type typ = TYPE_none
         | TYPE_int
         | TYPE_char
         | TYPE_bool
         | TYPE_double
         | TYPE_ptr of typ
         | TYPE_array of typ * int (*immutable pointer*)
         | TYPE_proc

let rec sizeOfType t =
   match t with
   | TYPE_int            -> 2
   | TYPE_char           -> 1
   | TYPE_bool           -> 1
   | TYPE_double         -> 10
   | TYPE_ptr et          -> 2
   | TYPE_array (et, sz) -> sz * sizeOfType et (*immutable pointer has fixed size*)
   | _                   -> 0

let rec equalType t1 t2 =
   match t1, t2 with
   | TYPE_array (et1, sz1), TYPE_array (et2, sz2) -> equalType et1 et2
   | TYPE_ptr et1, TYPE_ptr et2                   -> equalType et1 et2
   | _                                            -> t1 = t2
