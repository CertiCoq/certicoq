open BinInt
open BinPos
open Datatypes
open ZArith_dec

(** val peq : int -> int -> bool **)

let peq =
  Pos.eq_dec

(** val zeq : int -> int -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : int -> int -> bool **)

let zlt =
  coq_Z_lt_dec

(** val zle : int -> int -> bool **)

let zle =
  coq_Z_le_gt_dec

(** val coq_Zdivide_dec : int -> int -> bool **)

let coq_Zdivide_dec p q =
  zeq (Z.modulo q p) 0

(** val nat_of_Z : int -> nat **)

let nat_of_Z =
  Z.to_nat

(** val align : int -> int -> int **)

let align n amount =
  Z.mul (Z.div (Z.sub (Z.add n amount) 1) amount) amount

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

(** val list_repeat : nat -> 'a1 -> 'a1 list **)

let rec list_repeat n x =
  match n with
  | O -> []
  | S m -> x :: (list_repeat m x)


