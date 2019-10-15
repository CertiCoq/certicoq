open BinPos
open Datatypes
open DecidableClass
open List0
open Nat0
open UsefulTypes

val listPad : 'a1 -> 'a1 list -> nat -> 'a1 list

val ball : bool list -> bool

val remove : 'a1 coq_Deq -> 'a1 -> 'a1 list -> 'a1 list

val diff : 'a1 coq_Deq -> 'a1 list -> 'a1 list -> 'a1 list

val seq : ('a1 -> 'a1) -> 'a1 -> nat -> 'a1 list

val maxlp : int list -> int -> int
