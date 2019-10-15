open BasicAst
open BinNat
open BinPos
open Datatypes
open List_util
open Monad0
open MonadState
open StateMonad
open Cps
open Cps_show
open Cps_util

type comp_data = { next_var : var; nect_cTag : cTag; next_iTag : iTag;
                   next_fTag : fTag; cenv : cEnv; fenv : fEnv;
                   name_env : Cps_show.nEnv; log : char list list }

val cenv : comp_data -> cEnv

val fenv : comp_data -> fEnv

val name_env : comp_data -> Cps_show.nEnv

type ('s, 't) compM = (comp_data * 's, 't) state

val get_name_env : unit -> ('a1, Cps_show.nEnv) compM

val get_name : var -> char list -> ('a1, var) compM

val get_names_lst : var list -> char list -> ('a1, var list) compM

val get_name_no_suff : char list -> ('a1, var) compM

val make_record_cTag : int -> ('a1, cTag) compM

val register_record_cTag : cTag -> iTag -> int -> ('a1, unit) compM

val get_pp_name : var -> ('a1, char list) compM

val get_pp_names_list : var list -> ('a1, char list list) compM

val log_msg : char list -> ('a1, unit) compM

val chr_newline : char

val newline : char list

val get_state : unit -> ('a1, 'a1) compM

val put_state : 'a1 -> ('a1, unit) compM

val get_ftag : int -> ('a1, fTag) compM

val run_compM :
  ('a1, 'a2) compM -> comp_data -> 'a1 -> 'a2 * (comp_data * 'a1)

val pack_data :
  var -> cTag -> iTag -> fTag -> cEnv -> fEnv -> Cps_show.nEnv -> char list
  list -> comp_data
