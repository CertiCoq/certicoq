open BinPos
open Datatypes
open List0
open List_util
open Cps
open Set_util

type coq_FVSet = PS.t

val add_list : coq_FVSet -> coq_FVSet -> PS.elt list -> coq_FVSet

val exp_fv_aux : exp -> coq_FVSet -> coq_FVSet -> coq_FVSet

val fundefs_fv_aux :
  fundefs -> coq_FVSet -> coq_FVSet -> coq_FVSet * coq_FVSet

val fundefs_fv : fundefs -> coq_FVSet

val max_var : exp -> int -> int

val max_var_fundefs : fundefs -> int -> int
