open BinInt
open BinPos
open Datatypes

type radix = int
  (* singleton inductive, whose constructor was Build_radix *)

val radix_val : radix -> int

val radix2 : radix

val cond_Zopp : bool -> int -> int

val coq_Zpos_div_eucl_aux1 : int -> int -> int * int

val coq_Zpos_div_eucl_aux : int -> int -> int * int

val coq_Zfast_div_eucl : int -> int -> int * int

val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1

val iter_pos : ('a1 -> 'a1) -> int -> 'a1 -> 'a1
