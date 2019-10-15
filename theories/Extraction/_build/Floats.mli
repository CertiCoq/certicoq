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

val cmp_of_comparison : comparison -> Datatypes.comparison option -> bool

module Float :
 sig
  val transform_quiet_nan : bool -> int -> float

  val expand_nan : bool -> int -> binary_float

  val of_single_nan : float32 -> float

  val reduce_nan : bool -> int -> float32

  val to_single_nan : float -> float32

  val neg_nan : float -> float

  val abs_nan : float -> float

  val binop_nan : float -> float -> float

  val zero : float

  val eq_dec : float -> float -> bool

  val neg : float -> float

  val abs : float -> float

  val add : float -> float -> float

  val sub : float -> float -> float

  val mul : float -> float -> float

  val div : float -> float -> float

  val compare : float -> float -> Datatypes.comparison option

  val cmp : comparison -> float -> float -> bool

  val of_single : float32 -> float

  val to_single : float -> float32

  val to_int : float -> Int.int option

  val to_intu : float -> Int.int option

  val to_long : float -> Int64.int option

  val to_longu : float -> Int64.int option

  val of_int : Int.int -> float

  val of_intu : Int.int -> float

  val of_long : Int64.int -> float

  val of_longu : Int64.int -> float

  val to_bits : float -> Int64.int

  val of_bits : Int64.int -> float
 end

module Float32 :
 sig
  val transform_quiet_nan : bool -> int -> float32

  val neg_nan : float32 -> float32

  val binop_nan : float32 -> float32 -> float32

  val zero : float32

  val eq_dec : float32 -> float32 -> bool

  val neg : float32 -> float32

  val add : float32 -> float32 -> float32

  val sub : float32 -> float32 -> float32

  val mul : float32 -> float32 -> float32

  val div : float32 -> float32 -> float32

  val compare : float32 -> float32 -> Datatypes.comparison option

  val cmp : comparison -> float32 -> float32 -> bool

  val to_int : float32 -> Int.int option

  val to_intu : float32 -> Int.int option

  val to_long : float32 -> Int64.int option

  val to_longu : float32 -> Int64.int option

  val of_int : Int.int -> float32

  val of_intu : Int.int -> float32

  val of_long : Int64.int -> float32

  val of_longu : Int64.int -> float32

  val to_bits : float32 -> Int.int

  val of_bits : Int.int -> float32
 end
