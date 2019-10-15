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

val coq_FF2B : int -> int -> full_float -> binary_float

val coq_Bsign : int -> int -> binary_float -> bool

val get_nan_pl : int -> int -> binary_float -> int

val build_nan : int -> int -> binary_float -> binary_float

val coq_Bopp :
  int -> int -> (binary_float -> binary_float) -> binary_float -> binary_float

val coq_Babs :
  int -> int -> (binary_float -> binary_float) -> binary_float -> binary_float

val coq_Bcompare :
  int -> int -> binary_float -> binary_float -> comparison option

type shr_record = { shr_m : int; shr_r : bool; shr_s : bool }

val shr_m : shr_record -> int

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : int -> location -> shr_record

val shr : shr_record -> int -> int -> shr_record * int

val shr_fexp : int -> int -> int -> int -> location -> shr_record * int

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

val choice_mode : mode -> bool -> int -> location -> int

val overflow_to_inf : mode -> bool -> bool

val binary_overflow : int -> int -> mode -> bool -> full_float

val binary_round_aux :
  int -> int -> mode -> bool -> int -> int -> location -> full_float

val coq_Bmult :
  int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
  binary_float -> binary_float -> binary_float

val shl_align : int -> int -> int -> int * int

val shl_align_fexp : int -> int -> int -> int -> int * int

val binary_round : int -> int -> mode -> bool -> int -> int -> full_float

val binary_normalize :
  int -> int -> mode -> int -> int -> bool -> binary_float

val coq_Bplus :
  int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
  binary_float -> binary_float -> binary_float

val coq_Bminus :
  int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
  binary_float -> binary_float -> binary_float

val coq_Fdiv_core_binary :
  int -> int -> int -> int -> int -> int -> (int * int) * location

val coq_Bdiv :
  int -> int -> (binary_float -> binary_float -> binary_float) -> mode ->
  binary_float -> binary_float -> binary_float
