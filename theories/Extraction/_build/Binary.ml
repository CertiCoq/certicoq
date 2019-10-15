open BinInt
open BinPos
open Bool
open Bracket
open Datatypes
open Digits
open FLT
open Round
open Zaux
open Zpower

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * int
| F754_finite of bool * int * int

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * int
| B754_finite of bool * int * int

(** val coq_FF2B : int -> int -> full_float -> binary_float **)

let coq_FF2B _ _ = function
| F754_zero s -> B754_zero s
| F754_infinity s -> B754_infinity s
| F754_nan (b, pl) -> B754_nan (b, pl)
| F754_finite (s, m, e) -> B754_finite (s, m, e)

(** val coq_Bsign : int -> int -> binary_float -> bool **)

let coq_Bsign _ _ = function
| B754_zero s -> s
| B754_infinity s -> s
| B754_nan (s, _) -> s
| B754_finite (s, _, _) -> s

(** val get_nan_pl : int -> int -> binary_float -> int **)

let get_nan_pl _ _ = function
| B754_nan (_, pl) -> pl
| _ -> 1

(** val build_nan : int -> int -> binary_float -> binary_float **)

let build_nan prec emax x =
  B754_nan ((coq_Bsign prec emax x), (get_nan_pl prec emax x))

(** val coq_Bopp :
    int -> int -> (binary_float -> binary_float) -> binary_float ->
    binary_float **)

let coq_Bopp prec emax opp_nan x = match x with
| B754_zero sx -> B754_zero (negb sx)
| B754_infinity sx -> B754_infinity (negb sx)
| B754_nan (_, _) -> build_nan prec emax (opp_nan x)
| B754_finite (sx, mx, ex) -> B754_finite ((negb sx), mx, ex)

(** val coq_Babs :
    int -> int -> (binary_float -> binary_float) -> binary_float ->
    binary_float **)

let coq_Babs prec emax abs_nan x = match x with
| B754_zero _ -> B754_zero false
| B754_infinity _ -> B754_infinity false
| B754_nan (_, _) -> build_nan prec emax (abs_nan x)
| B754_finite (_, mx, ex) -> B754_finite (false, mx, ex)

(** val coq_Bcompare :
    int -> int -> binary_float -> binary_float -> comparison option **)

let coq_Bcompare _ _ f1 f2 =
  match f1 with
  | B754_zero _ ->
    (match f2 with
     | B754_zero _ -> Some Eq
     | B754_infinity s -> Some (if s then Gt else Lt)
     | B754_nan (_, _) -> None
     | B754_finite (s, _, _) -> Some (if s then Gt else Lt))
  | B754_infinity s ->
    (match f2 with
     | B754_infinity s0 ->
       Some (if s then if s0 then Eq else Lt else if s0 then Gt else Eq)
     | B754_nan (_, _) -> None
     | _ -> Some (if s then Lt else Gt))
  | B754_nan (_, _) -> None
  | B754_finite (s1, m1, e1) ->
    (match f2 with
     | B754_zero _ -> Some (if s1 then Lt else Gt)
     | B754_infinity s -> Some (if s then Gt else Lt)
     | B754_nan (_, _) -> None
     | B754_finite (s2, m2, e2) ->
       Some
         (if s1
          then if s2
               then (match Z.compare e1 e2 with
                     | Eq -> coq_CompOpp (Pos.compare_cont Eq m1 m2)
                     | Lt -> Gt
                     | Gt -> Lt)
               else Lt
          else if s2
               then Gt
               else (match Z.compare e1 e2 with
                     | Eq -> Pos.compare_cont Eq m1 m2
                     | x -> x)))

type shr_record = { shr_m : int; shr_r : bool; shr_s : bool }

(** val shr_m : shr_record -> int **)

let shr_m x = x.shr_m

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
     (fun _ -> { shr_m = 0; shr_r = false; shr_s = s0 })
     (fun p0 ->
     (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun p -> { shr_m = p; shr_r = true; shr_s = s0 })
       (fun p -> { shr_m = p; shr_r = false; shr_s = s0 })
       (fun _ -> { shr_m = 0; shr_r = true; shr_s = s0 })
       p0)
     (fun p0 ->
     (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun p -> { shr_m = ((~-) p); shr_r = true; shr_s = s0 })
       (fun p -> { shr_m = ((~-) p); shr_r = false; shr_s = s0 })
       (fun _ -> { shr_m = 0; shr_r = true; shr_s = s0 })
       p0)
     m)

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Coq_loc_Inexact Gt else Coq_loc_Inexact Eq
  else if shr_s0 then Coq_loc_Inexact Lt else Coq_loc_Exact

(** val shr_record_of_loc : int -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> int -> int -> shr_record * int **)

let shr mrs e n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (mrs, e))
    (fun p -> ((iter_pos shr_1 p mrs), (Z.add e n)))
    (fun _ -> (mrs, e))
    n

(** val shr_fexp :
    int -> int -> int -> int -> location -> shr_record * int **)

let shr_fexp prec emax =
  let emin = Z.sub (Z.sub ((fun p->1+2*p) 1) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m e l ->
  shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (coq_Zdigits2 m) e)) e))

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

(** val choice_mode : mode -> bool -> int -> location -> int **)

let choice_mode m sx mx lx =
  match m with
  | Coq_mode_NE -> cond_incr (round_N (negb (Z.even mx)) lx) mx
  | Coq_mode_ZR -> mx
  | Coq_mode_DN -> cond_incr (round_sign_DN sx lx) mx
  | Coq_mode_UP -> cond_incr (round_sign_UP sx lx) mx
  | Coq_mode_NA -> cond_incr (round_N true lx) mx

(** val overflow_to_inf : mode -> bool -> bool **)

let overflow_to_inf m s =
  match m with
  | Coq_mode_ZR -> false
  | Coq_mode_DN -> s
  | Coq_mode_UP -> negb s
  | _ -> true

(** val binary_overflow : int -> int -> mode -> bool -> full_float **)

let binary_overflow prec emax m s =
  if overflow_to_inf m s
  then F754_infinity s
  else F754_finite (s,
         ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
            (fun _ -> 1)
            (fun p -> p)
            (fun _ -> 1)
            (Z.sub (Z.pow ((fun p->2*p) 1) prec) 1)), (Z.sub emax prec))

(** val binary_round_aux :
    int -> int -> mode -> bool -> int -> int -> location -> full_float **)

let binary_round_aux prec emax mode0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec emax mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec emax
      (choice_mode mode0 sx mrs'.shr_m (loc_of_shr_record mrs')) e'
      Coq_loc_Exact
  in
  ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
     (fun _ -> F754_zero sx)
     (fun m ->
     if Z.leb e'' (Z.sub emax prec)
     then F754_finite (sx, m, e'')
     else binary_overflow prec emax mode0 sx)
     (fun _ -> F754_nan (false, 1))
     mrs''.shr_m)

(** val coq_Bmult :
    int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
    binary_float -> binary_float -> binary_float **)

let coq_Bmult prec emax mult_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> build_nan prec emax (mult_nan x y))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> build_nan prec emax (mult_nan x y))
  | B754_nan (_, _) -> build_nan prec emax (mult_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_zero (xorb sx sy)
     | B754_infinity sy -> B754_infinity (xorb sx sy)
     | B754_nan (_, _) -> build_nan prec emax (mult_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (binary_round_aux prec emax m (xorb sx sy) (Pos.mul mx my)
           (Z.add ex ey) Coq_loc_Exact))

(** val shl_align : int -> int -> int -> int * int **)

let shl_align mx ex ex' =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (mx, ex))
    (fun _ -> (mx, ex))
    (fun d -> ((shift_pos d mx), ex'))
    (Z.sub ex' ex)

(** val shl_align_fexp : int -> int -> int -> int -> int * int **)

let shl_align_fexp prec emax =
  let emin = Z.sub (Z.sub ((fun p->1+2*p) 1) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun mx ex -> shl_align mx ex (fexp (Z.add (digits2_pos mx) ex)))

(** val binary_round :
    int -> int -> mode -> bool -> int -> int -> full_float **)

let binary_round prec emax m sx mx ex =
  let (mz, ez) = shl_align_fexp prec emax mx ex in
  binary_round_aux prec emax m sx mz ez Coq_loc_Exact

(** val binary_normalize :
    int -> int -> mode -> int -> int -> bool -> binary_float **)

let binary_normalize prec emax mode0 m e szero =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> B754_zero szero)
    (fun m0 ->
    coq_FF2B prec emax (binary_round prec emax mode0 false m0 e))
    (fun m0 -> coq_FF2B prec emax (binary_round prec emax mode0 true m0 e))
    m

(** val coq_Bplus :
    int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
    binary_float -> binary_float -> binary_float **)

let coq_Bplus prec emax plus_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx sy
       then x
       else (match m with
             | Coq_mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | _ -> y)
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy ->
       if eqb sx sy then x else build_nan prec emax (plus_nan x y)
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | _ -> x)
  | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity _ -> y
     | B754_nan (_, _) -> build_nan prec emax (plus_nan x y)
     | B754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax m
         (Z.add (cond_Zopp sx (fst (shl_align mx ex ez)))
           (cond_Zopp sy (fst (shl_align my ey ez)))) ez
         (match m with
          | Coq_mode_DN -> true
          | _ -> false))

(** val coq_Bminus :
    int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
    binary_float -> binary_float -> binary_float **)

let coq_Bminus prec emax minus_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_zero sy ->
       if eqb sx (negb sy)
       then x
       else (match m with
             | Coq_mode_DN -> B754_zero true
             | _ -> B754_zero false)
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | B754_finite (sy, my, ey) -> B754_finite ((negb sy), my, ey))
  | B754_infinity sx ->
    (match y with
     | B754_infinity sy ->
       if eqb sx (negb sy) then x else build_nan prec emax (minus_nan x y)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | _ -> x)
  | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero _ -> x
     | B754_infinity sy -> B754_infinity (negb sy)
     | B754_nan (_, _) -> build_nan prec emax (minus_nan x y)
     | B754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax m
         (Z.sub (cond_Zopp sx (fst (shl_align mx ex ez)))
           (cond_Zopp sy (fst (shl_align my ey ez)))) ez
         (match m with
          | Coq_mode_DN -> true
          | _ -> false))

(** val coq_Fdiv_core_binary :
    int -> int -> int -> int -> int -> int -> (int * int) * location **)

let coq_Fdiv_core_binary prec emax =
  let emin = Z.sub (Z.sub ((fun p->1+2*p) 1) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m1 e1 m2 e2 ->
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e' = Z.min (fexp (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2) in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> m1)
      (fun _ -> Z.shiftl m1 s)
      (fun _ -> 0)
      s
  in
  let (q, r) = coq_Zfast_div_eucl m' m2 in
  ((q, e'), (new_location m2 r Coq_loc_Exact)))

(** val coq_Bdiv :
    int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
    binary_float -> binary_float -> binary_float **)

let coq_Bdiv prec emax div_nan m x y =
  match x with
  | B754_zero sx ->
    (match y with
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
     | _ -> build_nan prec emax (div_nan x y))
  | B754_infinity sx ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
     | _ -> build_nan prec emax (div_nan x y))
  | B754_nan (_, _) -> build_nan prec emax (div_nan x y)
  | B754_finite (sx, mx, ex) ->
    (match y with
     | B754_zero sy -> B754_infinity (xorb sx sy)
     | B754_infinity sy -> B754_zero (xorb sx sy)
     | B754_nan (_, _) -> build_nan prec emax (div_nan x y)
     | B754_finite (sy, my, ey) ->
       coq_FF2B prec emax
         (let (p, lz) = coq_Fdiv_core_binary prec emax mx ex my ey in
          let (mz, ez) = p in
          binary_round_aux prec emax m (xorb sx sy) mz ez lz))
