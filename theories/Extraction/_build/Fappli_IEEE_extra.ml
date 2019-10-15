open BinInt
open BinPos
open Binary
open Zaux

(** val coq_Beq_dec : int -> int -> binary_float -> binary_float -> bool **)

let coq_Beq_dec _ _ f1 f2 =
  match f1 with
  | B754_zero s1 ->
    (match f2 with
     | B754_zero s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | B754_infinity s1 ->
    (match f2 with
     | B754_infinity s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | B754_nan (s1, p1) ->
    (match f2 with
     | B754_nan (s2, p2) ->
       if s1
       then if s2 then Pos.eq_dec p1 p2 else false
       else if s2 then false else Pos.eq_dec p1 p2
     | _ -> false)
  | B754_finite (s1, m1, e1) ->
    (match f2 with
     | B754_finite (s2, m2, e2) ->
       if s1
       then if s2
            then let s = Pos.eq_dec m1 m2 in
                 if s then Z.eq_dec e1 e2 else false
            else false
       else if s2
            then false
            else let s = Pos.eq_dec m1 m2 in
                 if s then Z.eq_dec e1 e2 else false
     | _ -> false)

(** val coq_BofZ : int -> int -> int -> binary_float **)

let coq_BofZ prec emax n =
  binary_normalize prec emax Coq_mode_NE n 0 false

(** val coq_ZofB : int -> int -> binary_float -> int option **)

let coq_ZofB _ _ = function
| B754_zero _ -> Some 0
| B754_finite (s, m, e0) ->
  ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
     (fun _ -> Some (cond_Zopp s m))
     (fun e -> Some
     (Z.mul (cond_Zopp s m) (Z.pow_pos (radix_val radix2) e)))
     (fun e -> Some
     (cond_Zopp s (Z.div m (Z.pow_pos (radix_val radix2) e))))
     e0)
| _ -> None

(** val coq_ZofB_range :
    int -> int -> binary_float -> int -> int -> int option **)

let coq_ZofB_range prec emax f zmin zmax =
  match coq_ZofB prec emax f with
  | Some z -> if (&&) (Z.leb zmin z) (Z.leb z zmax) then Some z else None
  | None -> None

(** val coq_Bconv :
    int -> int -> int -> int -> (binary_float -> binary_float) -> mode ->
    binary_float -> binary_float **)

let coq_Bconv _ _ prec2 emax2 conv_nan md f = match f with
| B754_nan (_, _) -> build_nan prec2 emax2 (conv_nan f)
| B754_finite (s, m, e) -> binary_normalize prec2 emax2 md (cond_Zopp s m) e s
| x -> x
