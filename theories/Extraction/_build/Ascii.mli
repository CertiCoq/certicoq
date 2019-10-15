open BinNat
open Datatypes

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : nat -> char

val coq_N_of_digits : bool list -> int

val coq_N_of_ascii : char -> int

val nat_of_ascii : char -> nat
