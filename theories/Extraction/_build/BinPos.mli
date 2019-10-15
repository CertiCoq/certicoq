open BinPosDef
open Bool
open Datatypes
open Decimal
open Nat0

type __ = Obj.t

module Pos :
 sig
  type t = int

  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred : int -> int

  val pred_N : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val pred_mask : mask -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val sub : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val pow : int -> int -> int

  val square : int -> int

  val div2 : int -> int

  val div2_up : int -> int

  val size_nat : int -> nat

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val min : int -> int -> int

  val max : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask

  val sqrtrem : int -> int * mask

  val sqrt : int -> int

  val gcdn : nat -> int -> int -> int

  val gcd : int -> int -> int

  val ggcdn : nat -> int -> int -> int * (int * int)

  val ggcd : int -> int -> int * (int * int)

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl_nat : int -> nat -> int

  val shiftr_nat : int -> nat -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val testbit_nat : int -> nat -> bool

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> nat

  val of_nat : nat -> int

  val of_succ_nat : nat -> int

  val of_uint_acc : uint -> int -> int

  val of_uint : uint -> int

  val of_int : unit -> int option

  val to_little_uint : int -> uint

  val to_uint : int -> uint

  val to_int : int -> unit

  val eq_dec : int -> int -> bool

  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView

  val coq_PeanoView_rect :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView

  val peanoView : int -> coq_PeanoView

  val coq_PeanoView_iter :
    'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val eqb_spec : int -> int -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool
 end
