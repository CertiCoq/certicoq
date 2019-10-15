open AstCommon
open BasicAst
open BinNat
open BinPos
open Datatypes
open L4_5_to_L5
open List0
open Monad0
open Nat0
open OptionMonad
open Classes0
open Cps
open Cps_util
open Ctx
open PolyEval
open Terms
open VarInterface
open Variables

type coq_L5_conId = dcon

val coq_L5_conId_dec : coq_L5_conId -> coq_L5_conId -> bool

type conId_map = (coq_L5_conId * cTag) list

val dcon_to_info : cTag -> coq_L5_conId -> conId_map -> cTag

val dcon_to_tag : cTag -> coq_L5_conId -> conId_map -> cTag

val fromN : int -> nat -> int list * int

val ctx_bind_proj : cTag -> int -> nat -> var -> nat -> exp_ctx * var

type t_info = fTag

type t_map = t_info M.t

val t_empty : t_map

val get_f : fTag -> var -> t_map -> fTag

type s_map = var M.t

val s_empty : var M.t

val get_s : coq_NVar -> s_map -> var

val set_s_list : coq_NVar list -> var list -> s_map -> s_map

type conv_env = (conId_map * t_map) * nEnv

val set_nt : var -> (name * t_info) -> conv_env -> conv_env

val set_t : var -> t_info -> conv_env -> conv_env

val set_n : var -> name -> conv_env -> conv_env

val set_t_f_list : fTag -> var list -> coq_NVar list -> conv_env -> conv_env

val convert :
  cTag -> fTag -> fTag -> (coq_NVar, coq_L5Opid) coq_NTerm -> s_map -> s_map
  -> conv_env -> var -> ((exp * var) * conv_env) option

type ienv = (char list * itypPack) list

val convert_cnstrs :
  char list -> cTag list -> coq_Cnstr list -> inductive -> int -> iTag ->
  cEnv -> conId_map -> cEnv * conId_map

val convert_typack :
  ityp list -> char list -> nat ->
  ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
  (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_env' :
  ienv -> ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
  (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_env :
  cTag -> iTag -> ienv -> (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_top :
  cTag -> iTag -> fTag -> fTag -> (ienv * (coq_NVar, coq_L5Opid) coq_NTerm)
  -> (((((cEnv * nEnv) * fEnv) * cTag) * iTag) * exp) option
