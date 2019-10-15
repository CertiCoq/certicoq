open BinPos
open Datatypes
open L3_to_L4
open L5_to_L6
open Beta_contraction
open CertiClasses
open CertiClasses2
open Closure_conversion2
open Cps
open Cps_util
open Dead_param_elim
open Eval
open ExceptionMonad
open Identifiers
open Instances2
open Lambda_lifting
open Shrink_cps
open State
open Uncurry

type coq_L6env = ((prims * cEnv) * nEnv) * fEnv

type coq_L6term = env * exp

type coq_L6val = coq_val

val default_cTag : int

val default_iTag : int

val bogus_cloTag : int

val bogus_cloiTag : int

val fun_fTag : int

val kon_fTag : int

val coq_L6_pipeline :
  (L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm ->
  (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception

val coq_L6_pipeline_opt :
  (L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm ->
  (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception

val certiL5_t0_L6 :
  ((L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm,
  (coq_L6env * coq_L6term, coq_L6val) cTerm) coq_CerticoqTranslation
