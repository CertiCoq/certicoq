open BinPos
open Datatypes

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val succ : int -> int

  val succ_pos : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val max : int -> int -> int

  val pos_div_eucl : int -> int -> int * int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl : int -> int -> int

  val testbit : int -> int -> bool

  val to_nat : int -> nat

  val of_nat : nat -> int

  val eq_dec : int -> int -> bool
 end
