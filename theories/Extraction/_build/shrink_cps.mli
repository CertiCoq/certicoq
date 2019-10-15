open BinPos
open Datatypes
open List0
open List_util
open Nat0
open Specif
open Cps

type __ = Obj.t

val var_dec : int -> int -> bool

type svalue =
| SVconstr of cTag * var list
| SVfun of fTag * var list * exp

type ctx_map = svalue M.t

type r_map = var M.t

type c_map = nat M.t

type b_map = bool M.t

val getd : 'a1 -> int -> 'a1 M.t -> 'a1

val set_list : (M.elt * 'a1) list -> 'a1 M.t -> 'a1 M.t

val apply_r : M.elt M.t -> int -> M.elt

val apply_r_list : M.elt M.t -> int list -> M.elt list

type tag = int

val all_fun_name : fundefs -> var list

val update_census_list :
  r_map -> var list -> (var -> c_map -> nat) -> c_map -> c_map

val update_census : r_map -> exp -> (var -> c_map -> nat) -> c_map -> c_map

val update_census_f :
  r_map -> fundefs -> (var -> c_map -> nat) -> c_map -> c_map

val init_census : exp -> c_map

val dec_census : r_map -> exp -> c_map -> c_map

val dec_census_list : r_map -> var list -> c_map -> c_map

val dec_census_all_case : r_map -> (var * exp) list -> c_map -> c_map

val dec_census_case : r_map -> (var * exp) list -> var -> c_map -> c_map

val update_count_inlined : var list -> var list -> c_map -> c_map

val precontractfun :
  r_map -> c_map -> ctx_map -> fundefs -> (fundefs * c_map) * ctx_map

val contractcases :
  ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
  -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
  ctx_map -> (var * exp) list -> (((var * exp) list * c_map) * b_map, __) sigT

val postcontractfun :
  ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
  -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
  ctx_map -> fundefs -> ((fundefs * c_map) * b_map, __) sigT

val contract_func :
  (r_map, (c_map, (exp, (ctx_map, b_map) sigT) sigT) sigT) sigT ->
  ((exp * c_map) * b_map, __) sigT

val contract :
  r_map -> c_map -> exp -> ctx_map -> b_map -> ((exp * c_map) * b_map, __)
  sigT

val shrink_top : exp -> exp
