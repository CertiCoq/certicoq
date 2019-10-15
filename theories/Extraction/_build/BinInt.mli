open BinNat
open BinPos
open Datatypes

module Z :
 sig
  val one : int

  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val pred : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int

  val to_nat : int -> nat

  val of_nat : nat -> int

  val of_N : int -> int

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val quotrem : int -> int -> int * int

  val quot : int -> int -> int

  val rem : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val div2 : int -> int

  val testbit : int -> int -> bool

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val eq_dec : int -> int -> bool
 end
