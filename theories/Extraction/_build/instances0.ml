open Ast0
open AstCommon
open CertiClasses
open Compile0
open ExceptionMonad
open Utils

(** val translateTo :
    coq_Fuel -> (coq_Term coq_Program, 'a1) coq_CerticoqTranslation ->
    coq_Opt -> program -> 'a1 coq_exception **)

let translateTo f h o p =
  let l1g = program_Program f p in translate h o l1g
