open Ast0
open AstCommon
open CertiClasses
open Compile0
open ExceptionMonad
open Utils

val translateTo :
  coq_Fuel -> (coq_Term coq_Program, 'a1) coq_CerticoqTranslation -> coq_Opt
  -> program -> 'a1 coq_exception
