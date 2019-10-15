open BinInt
open Datatypes

(** val coq_Zeq_bool : int -> int -> bool **)

let coq_Zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false
