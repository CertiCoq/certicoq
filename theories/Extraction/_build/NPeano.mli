open Bool
open Datatypes
open Decimal
open PeanoNat

type __ = Obj.t

module Nat :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : unit -> nat option

  val to_int : nat -> unit

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> bool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> bool

    val min_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> bool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> bool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end
