open BinNat
open Datatypes
open List0
open Maps
open Monad0
open StateMonad
open String0
open Cps
open Hoisting
open Identifiers
open Set_util
open State

type coq_VarInfo =
| FVar of int
| MRFun of var
| BoundVar

type coq_VarInfoMap = coq_VarInfo M.t

type coq_GFunInfo = var
  (* singleton inductive, whose constructor was GFun *)

type coq_GFunMap = coq_GFunInfo M.t

type 't ccstate = (unit, 't) compM

val clo_env_suffix : char list

val clo_suffix : char list

val code_suffix : char list

val proj_suffix : char list

val get_var :
  cTag -> var -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var -> (var * (exp
  -> exp)) ccstate

val get_vars :
  cTag -> var list -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var -> (var
  list * (exp -> exp)) ccstate

val add_params : int list -> coq_VarInfoMap -> coq_VarInfoMap

val make_env :
  cTag -> var list -> coq_VarInfoMap -> coq_VarInfoMap -> cTag -> var -> var
  -> coq_GFunMap -> ((cTag * coq_VarInfoMap) * (exp -> exp)) ccstate

val make_full_closure :
  cTag -> fundefs -> coq_VarInfoMap -> coq_VarInfoMap -> coq_GFunMap -> var
  -> bool -> (((coq_VarInfoMap * coq_VarInfoMap) * coq_GFunMap) * (exp ->
  exp)) ccstate

val bool_to_string : bool -> char list

val exp_closure_conv :
  cTag -> exp -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var -> (exp * (exp
  -> exp)) ccstate

val closure_conversion_hoist :
  cTag -> iTag -> exp -> comp_data -> exp * comp_data
