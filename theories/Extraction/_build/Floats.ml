open Archi
open BinPos
open Binary
open Bits
open Coqlib0
open Datatypes
open Fappli_IEEE_extra
open Integers
open Zaux

type float = binary64

type float32 = binary32

(** val cmp_of_comparison :
    comparison -> Datatypes.comparison option -> bool **)

let cmp_of_comparison c x =
  match c with
  | Ceq ->
    (match x with
     | Some c0 -> (match c0 with
                   | Eq -> true
                   | _ -> false)
     | None -> false)
  | Cne ->
    (match x with
     | Some c0 -> (match c0 with
                   | Eq -> false
                   | _ -> true)
     | None -> true)
  | Clt ->
    (match x with
     | Some c0 -> (match c0 with
                   | Lt -> true
                   | _ -> false)
     | None -> false)
  | Cle ->
    (match x with
     | Some c0 -> (match c0 with
                   | Gt -> false
                   | _ -> true)
     | None -> false)
  | Cgt ->
    (match x with
     | Some c0 -> (match c0 with
                   | Gt -> true
                   | _ -> false)
     | None -> false)
  | Cge ->
    (match x with
     | Some c0 -> (match c0 with
                   | Lt -> false
                   | _ -> true)
     | None -> false)

module Float =
 struct
  (** val transform_quiet_nan : bool -> int -> float **)

  let transform_quiet_nan s p =
    B754_nan (s,
      (Pos.coq_lor p
        (iter_nat (fun x -> (fun p->2*p) x) (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))) 1)))

  (** val expand_nan : bool -> int -> binary_float **)

  let expand_nan s p =
    B754_nan (s,
      (Pos.shiftl_nat p (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

  (** val of_single_nan : float32 -> float **)

  let of_single_nan = function
  | B754_nan (s, p) ->
    if float_of_single_preserves_sNaN
    then expand_nan s p
    else transform_quiet_nan s
           (Pos.shiftl_nat p (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))
  | _ -> default_nan_64

  (** val reduce_nan : bool -> int -> float32 **)

  let reduce_nan s p =
    B754_nan (s,
      (Pos.shiftr_nat p (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

  (** val to_single_nan : float -> float32 **)

  let to_single_nan = function
  | B754_nan (s, p) ->
    reduce_nan s
      (Pos.coq_lor p
        (iter_nat (fun x -> (fun p->2*p) x) (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))) 1))
  | _ -> default_nan_32

  (** val neg_nan : float -> float **)

  let neg_nan = function
  | B754_nan (s, p) -> B754_nan ((negb s), p)
  | _ -> default_nan_64

  (** val abs_nan : float -> float **)

  let abs_nan = function
  | B754_nan (_, p) -> B754_nan (false, p)
  | _ -> default_nan_64

  (** val binop_nan : float -> float -> float **)

  let binop_nan x y =
    if fpu_returns_default_qNaN
    then default_nan_64
    else (match x with
          | B754_nan (s1, pl1) ->
            (match y with
             | B754_nan (s2, pl2) ->
               if choose_binop_pl_64 pl1 pl2
               then transform_quiet_nan s2 pl2
               else transform_quiet_nan s1 pl1
             | _ -> transform_quiet_nan s1 pl1)
          | _ ->
            (match y with
             | B754_nan (s2, pl2) -> transform_quiet_nan s2 pl2
             | _ -> default_nan_64))

  (** val zero : float **)

  let zero =
    B754_zero false

  (** val eq_dec : float -> float -> bool **)

  let eq_dec =
    coq_Beq_dec ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))))))

  (** val neg : float -> float **)

  let neg =
    coq_Bopp ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) neg_nan

  (** val abs : float -> float **)

  let abs =
    coq_Babs ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) abs_nan

  (** val add : float -> float -> float **)

  let add =
    coq_Bplus ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) binop_nan Coq_mode_NE

  (** val sub : float -> float -> float **)

  let sub =
    coq_Bminus ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) binop_nan Coq_mode_NE

  (** val mul : float -> float -> float **)

  let mul =
    coq_Bmult ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) binop_nan Coq_mode_NE

  (** val div : float -> float -> float **)

  let div =
    coq_Bdiv ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) binop_nan Coq_mode_NE

  (** val compare : float -> float -> Datatypes.comparison option **)

  let compare f1 f2 =
    coq_Bcompare ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) f1 f2

  (** val cmp : comparison -> float -> float -> bool **)

  let cmp c f1 f2 =
    cmp_of_comparison c (compare f1 f2)

  (** val of_single : float32 -> float **)

  let of_single =
    coq_Bconv ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))))
      of_single_nan Coq_mode_NE

  (** val to_single : float -> float32 **)

  let to_single =
    coq_Bconv ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1)))) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      1))))))) to_single_nan Coq_mode_NE

  (** val to_int : float -> Int.int option **)

  let to_int f =
    Coqlib0.option_map Int.repr
      (coq_ZofB_range ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))) f
        Int.min_signed Int.max_signed)

  (** val to_intu : float -> Int.int option **)

  let to_intu f =
    Coqlib0.option_map Int.repr
      (coq_ZofB_range ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))) f 0
        Int.max_unsigned)

  (** val to_long : float -> Int64.int option **)

  let to_long f =
    Coqlib0.option_map Int64.repr
      (coq_ZofB_range ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))) f
        Int64.min_signed Int64.max_signed)

  (** val to_longu : float -> Int64.int option **)

  let to_longu f =
    Coqlib0.option_map Int64.repr
      (coq_ZofB_range ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))) f 0
        Int64.max_unsigned)

  (** val of_int : Int.int -> float **)

  let of_int n =
    coq_BofZ ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) (Int.signed n)

  (** val of_intu : Int.int -> float **)

  let of_intu n =
    coq_BofZ ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) (Int.unsigned n)

  (** val of_long : Int64.int -> float **)

  let of_long n =
    coq_BofZ ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) (Int64.signed n)

  (** val of_longu : Int64.int -> float **)

  let of_longu n =
    coq_BofZ ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))))))) (Int64.unsigned n)

  (** val to_bits : float -> Int64.int **)

  let to_bits f =
    Int64.repr (bits_of_b64 f)

  (** val of_bits : Int64.int -> float **)

  let of_bits b =
    b64_of_bits (Int64.unsigned b)
 end

module Float32 =
 struct
  (** val transform_quiet_nan : bool -> int -> float32 **)

  let transform_quiet_nan s p =
    B754_nan (s,
      (Pos.coq_lor p
        (iter_nat (fun x -> (fun p->2*p) x) (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))) 1)))

  (** val neg_nan : float32 -> float32 **)

  let neg_nan = function
  | B754_nan (s, p) -> B754_nan ((negb s), p)
  | _ -> default_nan_32

  (** val binop_nan : float32 -> float32 -> float32 **)

  let binop_nan x y =
    if fpu_returns_default_qNaN
    then default_nan_32
    else (match x with
          | B754_nan (s1, pl1) ->
            (match y with
             | B754_nan (s2, pl2) ->
               if choose_binop_pl_32 pl1 pl2
               then transform_quiet_nan s2 pl2
               else transform_quiet_nan s1 pl1
             | _ -> transform_quiet_nan s1 pl1)
          | _ ->
            (match y with
             | B754_nan (s2, pl2) -> transform_quiet_nan s2 pl2
             | _ -> default_nan_32))

  (** val zero : float32 **)

  let zero =
    B754_zero false

  (** val eq_dec : float32 -> float32 -> bool **)

  let eq_dec =
    coq_Beq_dec ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))

  (** val neg : float32 -> float32 **)

  let neg =
    coq_Bopp ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) neg_nan

  (** val add : float32 -> float32 -> float32 **)

  let add =
    coq_Bplus ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) binop_nan Coq_mode_NE

  (** val sub : float32 -> float32 -> float32 **)

  let sub =
    coq_Bminus ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) binop_nan Coq_mode_NE

  (** val mul : float32 -> float32 -> float32 **)

  let mul =
    coq_Bmult ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) binop_nan Coq_mode_NE

  (** val div : float32 -> float32 -> float32 **)

  let div =
    coq_Bdiv ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) binop_nan Coq_mode_NE

  (** val compare : float32 -> float32 -> Datatypes.comparison option **)

  let compare f1 f2 =
    coq_Bcompare ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) f1 f2

  (** val cmp : comparison -> float32 -> float32 -> bool **)

  let cmp c f1 f2 =
    cmp_of_comparison c (compare f1 f2)

  (** val to_int : float32 -> Int.int option **)

  let to_int f =
    Coqlib0.option_map Int.repr
      (coq_ZofB_range ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->1+2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) f
        Int.min_signed Int.max_signed)

  (** val to_intu : float32 -> Int.int option **)

  let to_intu f =
    Coqlib0.option_map Int.repr
      (coq_ZofB_range ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->1+2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) f 0
        Int.max_unsigned)

  (** val to_long : float32 -> Int64.int option **)

  let to_long f =
    Coqlib0.option_map Int64.repr
      (coq_ZofB_range ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->1+2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) f
        Int64.min_signed Int64.max_signed)

  (** val to_longu : float32 -> Int64.int option **)

  let to_longu f =
    Coqlib0.option_map Int64.repr
      (coq_ZofB_range ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->1+2*p) 1)))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) f 0
        Int64.max_unsigned)

  (** val of_int : Int.int -> float32 **)

  let of_int n =
    coq_BofZ ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) (Int.signed n)

  (** val of_intu : Int.int -> float32 **)

  let of_intu n =
    coq_BofZ ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) (Int.unsigned n)

  (** val of_long : Int64.int -> float32 **)

  let of_long n =
    coq_BofZ ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) (Int64.signed n)

  (** val of_longu : Int64.int -> float32 **)

  let of_longu n =
    coq_BofZ ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))) (Int64.unsigned n)

  (** val to_bits : float32 -> Int.int **)

  let to_bits f =
    Int.repr (bits_of_b32 f)

  (** val of_bits : Int.int -> float32 **)

  let of_bits b =
    b32_of_bits (Int.unsigned b)
 end
