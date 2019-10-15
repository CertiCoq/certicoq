open Binary
open Bits
open Datatypes

(** val ptr64 : bool **)

let ptr64 =
  true

(** val big_endian : bool **)

let big_endian =
  false

(** val align_int64 : int **)

let align_int64 =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val align_float64 : int **)

let align_float64 =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val default_nan_64 : binary64 **)

let default_nan_64 =
  B754_nan (true,
    (let rec f = function
     | O -> 1
     | S n0 -> (fun p->2*p) (f n0)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val choose_binop_pl_64 : int -> int -> bool **)

let choose_binop_pl_64 _ _ =
  false

(** val default_nan_32 : binary32 **)

let default_nan_32 =
  B754_nan (true,
    (let rec f = function
     | O -> 1
     | S n0 -> (fun p->2*p) (f n0)
     in f (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))

(** val choose_binop_pl_32 : int -> int -> bool **)

let choose_binop_pl_32 _ _ =
  false

(** val fpu_returns_default_qNaN : bool **)

let fpu_returns_default_qNaN =
  false

(** val float_of_single_preserves_sNaN : bool **)

let float_of_single_preserves_sNaN =
  false
