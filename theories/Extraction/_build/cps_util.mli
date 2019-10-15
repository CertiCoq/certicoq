open BasicAst
open String0
open Cps
open Map_util

type nEnv = name M.t

val n_empty : nEnv

val add_entry : nEnv -> var -> var -> char list -> nEnv

val add_entry_str : nEnv -> var -> char list -> nEnv
