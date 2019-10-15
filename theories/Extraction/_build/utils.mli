open Datatypes

val on_snd : ('a2 -> 'a3) -> ('a1 * 'a2) -> 'a1 * 'a3

type coq_Fuel = nat

val fuel : coq_Fuel -> nat

val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val bool_compare : bool -> bool -> comparison

val ascii_compare : char -> char -> comparison

val string_compare : char list -> char list -> comparison
