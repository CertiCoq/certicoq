open BinInt
open Binary
open Zbool

val join_bits : int -> int -> bool -> int -> int -> int

val split_bits : int -> int -> int -> (bool * int) * int

val bits_of_binary_float : int -> int -> binary_float -> int

val binary_float_of_bits_aux : int -> int -> int -> full_float

val binary_float_of_bits : int -> int -> int -> binary_float

type binary32 = binary_float

val b32_of_bits : int -> binary32

val bits_of_b32 : binary32 -> int

type binary64 = binary_float

val b64_of_bits : int -> binary64

val bits_of_b64 : binary64 -> int
