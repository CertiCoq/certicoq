open Binary
open Bits
open Datatypes

val ptr64 : bool

val big_endian : bool

val align_int64 : int

val align_float64 : int

val default_nan_64 : binary64

val choose_binop_pl_64 : int -> int -> bool

val default_nan_32 : binary32

val choose_binop_pl_32 : int -> int -> bool

val fpu_returns_default_qNaN : bool

val float_of_single_preserves_sNaN : bool
