open Datatypes
open List0
open Cps

val erase_fundefs :
  exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) -> exp * fundefs

val erase_nested_fundefs :
  fundefs -> exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) ->
  exp * fundefs

val exp_hoist : exp -> exp
