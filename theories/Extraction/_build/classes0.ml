
type 'a coq_Eq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Eq *)

(** val eq_dec : 'a1 coq_Eq -> 'a1 -> 'a1 -> bool **)

let eq_dec eq =
  eq
