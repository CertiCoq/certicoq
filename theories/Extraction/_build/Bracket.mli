open BinInt
open Datatypes
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

val new_location_even : int -> int -> location -> location

val new_location_odd : int -> int -> location -> location

val new_location : int -> int -> location -> location
