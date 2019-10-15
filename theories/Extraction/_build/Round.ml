open BinInt
open Bracket
open Datatypes

(** val cond_incr : bool -> int -> int **)

let cond_incr b m =
  if b then Z.add m 1 else m

(** val round_sign_DN : bool -> location -> bool **)

let round_sign_DN s = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact _ -> s

(** val round_sign_UP : bool -> location -> bool **)

let round_sign_UP s = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact _ -> negb s

(** val round_N : bool -> location -> bool **)

let round_N p = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact c -> (match c with
                        | Eq -> p
                        | Lt -> false
                        | Gt -> true)
