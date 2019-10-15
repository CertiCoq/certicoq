open BinInt
open Binary
open Zbool

(** val join_bits : int -> int -> bool -> int -> int -> int **)

let join_bits mw ew s m e =
  Z.add (Z.shiftl (Z.add (if s then Z.pow ((fun p->2*p) 1) ew else 0) e) mw) m

(** val split_bits : int -> int -> int -> (bool * int) * int **)

let split_bits mw ew x =
  let mm = Z.pow ((fun p->2*p) 1) mw in
  let em = Z.pow ((fun p->2*p) 1) ew in
  (((Z.leb (Z.mul mm em) x), (Z.modulo x mm)), (Z.modulo (Z.div x mm) em))

(** val bits_of_binary_float : int -> int -> binary_float -> int **)

let bits_of_binary_float mw ew =
  let emax = Z.pow ((fun p->2*p) 1) (Z.sub ew 1) in
  let prec = Z.add mw 1 in
  let emin = Z.sub (Z.sub ((fun p->1+2*p) 1) emax) prec in
  (fun x ->
  match x with
  | B754_zero sx -> join_bits mw ew sx 0 0
  | B754_infinity sx ->
    join_bits mw ew sx 0 (Z.sub (Z.pow ((fun p->2*p) 1) ew) 1)
  | B754_nan (sx, plx) ->
    join_bits mw ew sx plx (Z.sub (Z.pow ((fun p->2*p) 1) ew) 1)
  | B754_finite (sx, mx, ex) ->
    let m = Z.sub mx (Z.pow ((fun p->2*p) 1) mw) in
    if Z.leb 0 m
    then join_bits mw ew sx m (Z.add (Z.sub ex emin) 1)
    else join_bits mw ew sx mx 0)

(** val binary_float_of_bits_aux : int -> int -> int -> full_float **)

let binary_float_of_bits_aux mw ew =
  let emax = Z.pow ((fun p->2*p) 1) (Z.sub ew 1) in
  let prec = Z.add mw 1 in
  let emin = Z.sub (Z.sub ((fun p->1+2*p) 1) emax) prec in
  (fun x ->
  let (p, ex) = split_bits mw ew x in
  let (sx, mx) = p in
  if coq_Zeq_bool ex 0
  then ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
          (fun _ -> F754_zero sx)
          (fun px -> F754_finite (sx, px, emin))
          (fun _ -> F754_nan (false, 1))
          mx)
  else if coq_Zeq_bool ex (Z.sub (Z.pow ((fun p->2*p) 1) ew) 1)
       then ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
               (fun _ -> F754_infinity sx)
               (fun plx -> F754_nan (sx, plx))
               (fun _ -> F754_nan (false, 1))
               mx)
       else ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
               (fun _ -> F754_nan (false, 1))
               (fun px -> F754_finite (sx, px,
               (Z.sub (Z.add ex emin) 1)))
               (fun _ -> F754_nan (false,
               1))
               (Z.add mx (Z.pow ((fun p->2*p) 1) mw))))

(** val binary_float_of_bits : int -> int -> int -> binary_float **)

let binary_float_of_bits mw ew x =
  let emax = Z.pow ((fun p->2*p) 1) (Z.sub ew 1) in
  let prec = Z.add mw 1 in
  coq_FF2B prec emax (binary_float_of_bits_aux mw ew x)

type binary32 = binary_float

(** val b32_of_bits : int -> binary32 **)

let b32_of_bits =
  binary_float_of_bits ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val bits_of_b32 : binary32 -> int **)

let bits_of_b32 =
  bits_of_binary_float ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

type binary64 = binary_float

(** val b64_of_bits : int -> binary64 **)

let b64_of_bits =
  binary_float_of_bits ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))

(** val bits_of_b64 : binary64 -> int **)

let bits_of_b64 =
  bits_of_binary_float ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))
