type typ = TYPE_none        (* no type (should not be used)       *)
         | TYPE_int         (* int                                *)
         | TYPE_char
         | TYPE_bool
         | TYPE_double
         | TYPE_ptr of typ
         | TYPE_array of typ * int (*immutable pointer*)
         | TYPE_proc

val sizeOfType : typ -> int
val equalType : typ -> typ -> bool
