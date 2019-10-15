open BinInt
open BinPos
open Binary
open Zaux

val coq_Beq_dec : int -> int -> binary_float -> binary_float -> bool

val coq_BofZ : int -> int -> int -> binary_float

val coq_ZofB : int -> int -> binary_float -> int option

val coq_ZofB_range : int -> int -> binary_float -> int -> int -> int option

val coq_Bconv :
  int -> int -> int -> int -> (binary_float -> binary_float) -> mode ->
  binary_float -> binary_float
