open Datatypes
open List0
open Monad0
open StateMonad
open String0
open Alpha_fresh
open Cps
open Cps_show
open Shrink_cps
open State

type 'st coq_InlineHeuristic = { update_funDef : (fundefs -> r_map -> 'st ->
                                                 'st * 'st);
                                 update_inFun : (var -> tag -> var list ->
                                                exp -> r_map -> 'st -> 'st);
                                 update_App : (var -> tag -> var list -> 'st
                                              -> 'st * bool) }

val update_funDef :
  'a1 coq_InlineHeuristic -> fundefs -> r_map -> 'a1 -> 'a1 * 'a1

val update_inFun :
  'a1 coq_InlineHeuristic -> var -> tag -> var list -> exp -> r_map -> 'a1 ->
  'a1

val update_App :
  'a1 coq_InlineHeuristic -> var -> tag -> var list -> 'a1 -> 'a1 * bool

type fun_map = ((tag * var list) * exp) M.t

val freshen_exp : exp -> exp freshM

val add_fundefs : fundefs -> fun_map -> fun_map

val debug_st : ('a1 -> nEnv -> char list) -> 'a1 -> unit freshM

val beta_contract :
  ('a1 -> nEnv -> char list) -> 'a1 coq_InlineHeuristic -> nat -> exp ->
  M.elt M.t -> fun_map -> 'a1 -> exp freshM

val beta_contract_top :
  ('a1 -> nEnv -> char list) -> 'a1 coq_InlineHeuristic -> exp -> nat -> 'a1
  -> comp_data -> exp * comp_data

val show_map : 'a1 M.t -> nEnv -> ('a1 -> char list) -> char list

val show_map_bool : bool M.t -> nEnv -> char list

val find_uncurried : fundefs -> bool M.t -> bool M.t

val coq_InineUncurried : bool M.t coq_InlineHeuristic

val inline_uncurry :
  exp -> nat M.t -> nat -> nat -> comp_data -> exp * comp_data
