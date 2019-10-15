open BinNat
open BinPos
open Datatypes

(** val fromN : int -> nat -> int list **)

let rec fromN n = function
| O -> []
| S m' -> n :: (fromN (N.succ n) m')

(** val nthN : 'a1 list -> int -> 'a1 option **)

let rec nthN al n =
  match al with
  | [] -> None
  | a :: al' ->
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> Some a)
       (fun _ -> nthN al' (N.sub n 1))
       n)

(** val max_list : int list -> int -> int **)

let rec max_list ls acc =
  match ls with
  | [] -> acc
  | x :: xs -> max_list xs (Pos.max x acc)
