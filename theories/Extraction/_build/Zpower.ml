open BinPos
open Datatypes

(** val shift_nat : nat -> int -> int **)

let rec shift_nat n z =
  match n with
  | O -> z
  | S n0 -> (fun p->2*p) (shift_nat n0 z)

(** val shift_pos : int -> int -> int **)

let shift_pos n z =
  Pos.iter (fun x -> (fun p->2*p) x) z n

(** val two_power_nat : nat -> int **)

let two_power_nat n =
  (shift_nat n 1)

(** val two_power_pos : int -> int **)

let two_power_pos x =
  (shift_pos x 1)

(** val two_p : int -> int **)

let two_p x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 1)
    (fun y -> two_power_pos y)
    (fun _ -> 0)
    x
