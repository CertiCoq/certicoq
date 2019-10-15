open Ctypes

(** val tvoid : coq_type **)

let tvoid =
  Tvoid

(** val tschar : coq_type **)

let tschar =
  Tint (I8, Signed, noattr)

(** val tint : coq_type **)

let tint =
  Tint (I32, Signed, noattr)

(** val tptr : coq_type -> coq_type **)

let tptr t =
  Tpointer (t, noattr)

(** val tarray : coq_type -> int -> coq_type **)

let tarray t sz =
  Tarray (t, sz, noattr)
