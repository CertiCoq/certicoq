open Ctypes

val tvoid : coq_type

val tschar : coq_type

val tint : coq_type

val tptr : coq_type -> coq_type

val tarray : coq_type -> int -> coq_type
