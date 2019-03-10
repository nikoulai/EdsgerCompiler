type typ = Tnone        (* no type (should not be used)       *)
         | Tint         (* int                                *)
         | Tchar
         | Tbool
         | Tdouble
         | Tptr of typ
         | Tarray of typ * int (*immutable pointer*)
         | Tvoid

val sizeOfType : typ -> int
val equalType : typ -> typ -> bool
