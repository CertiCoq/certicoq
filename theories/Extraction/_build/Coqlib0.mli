open BinInt
open BinPos
open Datatypes
open ZArith_dec

val peq : int -> int -> bool

val zeq : int -> int -> bool

val zlt : int -> int -> bool

val zle : int -> int -> bool

val coq_Zdivide_dec : int -> int -> bool

val nat_of_Z : int -> nat

val align : int -> int -> int

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val list_repeat : nat -> 'a1 -> 'a1 list


