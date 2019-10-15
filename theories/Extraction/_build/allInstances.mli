open Ast0
open BasicAst
open Clight
open Datatypes
open L6_to_Clight
open CertiClasses
open CertiClasses2
open Cps
open Cps_util
open ExceptionMonad
open Instances0
open Instances1
open Instances2
open Instances3
open Utils

val argsIdent : int

val allocIdent : int

val limitIdent : int

val gcIdent : int

val mainIdent : int

val bodyIdent : int

val threadInfIdent : int

val tinfIdent : int

val heapInfIdent : int

val numArgsIdent : int

val isptrIdent : int

val caseIdent : int

val compile_L7 :
  (coq_L6env * coq_L6term, coq_L6val) cTerm -> (nEnv * program) * program

val compile_opt_L7 :
  (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception ->
  ((nEnv * program) * program) coq_exception

val compile_template_L7 :
  coq_Fuel -> nat -> Ast0.program -> ((nEnv * program) * program)
  coq_exception

val printProg : (name M.t * program) -> char list -> unit
