open BinInt

(** val coq_FLT_exp : int -> int -> int -> int **)

let coq_FLT_exp emin prec e =
  Z.max (Z.sub e prec) emin
