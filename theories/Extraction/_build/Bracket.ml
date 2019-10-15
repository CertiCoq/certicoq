open BinInt
open Datatypes
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

(** val new_location_even : int -> int -> location -> location **)

let new_location_even nb_steps k l =
  if coq_Zeq_bool k 0
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact _ -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare (Z.mul ((fun p->2*p) 1) k) nb_steps with
          | Eq -> (match l with
                   | Coq_loc_Exact -> Eq
                   | Coq_loc_Inexact _ -> Gt)
          | x -> x)

(** val new_location_odd : int -> int -> location -> location **)

let new_location_odd nb_steps k l =
  if coq_Zeq_bool k 0
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact _ -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare (Z.add (Z.mul ((fun p->2*p) 1) k) 1) nb_steps with
          | Eq ->
            (match l with
             | Coq_loc_Exact -> Lt
             | Coq_loc_Inexact l0 -> l0)
          | x -> x)

(** val new_location : int -> int -> location -> location **)

let new_location nb_steps =
  if Z.even nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps
