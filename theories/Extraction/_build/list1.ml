open BinPos
open Datatypes
open DecidableClass
open List0
open Nat0
open UsefulTypes

(** val listPad : 'a1 -> 'a1 list -> nat -> 'a1 list **)

let listPad def l n =
  app l (repeat def (sub n (length l)))

(** val ball : bool list -> bool **)

let rec ball = function
| [] -> true
| x :: xs -> (&&) x (ball xs)

(** val remove : 'a1 coq_Deq -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove h x = function
| [] -> []
| y :: tl ->
  if decide (deceq h x y) then remove h x tl else y :: (remove h x tl)

(** val diff : 'a1 coq_Deq -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec diff eqd lr l =
  match lr with
  | [] -> l
  | h :: t -> diff eqd t (remove eqd h l)

(** val seq : ('a1 -> 'a1) -> 'a1 -> nat -> 'a1 list **)

let rec seq next start = function
| O -> []
| S len0 -> start :: (seq next (next start) len0)

(** val maxlp : int list -> int -> int **)

let maxlp =
  fold_left Pos.max
