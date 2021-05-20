Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wcbvEval.
Require Import Common.Common Common.classes Common.Pipeline_utils Common.compM.
From ExtLib Require Import Monads.

Import MonadNotation.

Definition erase_PCUIC : CertiCoqTrans Ast.program (global_context * term) :=
  fun src =>
    debug_msg "Translating from Template to Lbox" ;;
    (LiftErrorCertiCoqTrans "Lbox" L1g.compile.erase src).

(* Expose the top-level transformation function *)
Definition compile_L1g : CertiCoqTrans (global_context * term) (Program Term) :=
  fun src =>
    debug_msg "Translating from Lbox to L1" ;;
    (LiftCertiCoqTrans "L1g" L1g.compile.program_Program src).

(* NOTE: AFAICT we don't have these definitions *)
(* Instance Template_Lang : Lang Ast.program := *)
(*   { Value := Ast.term; *)
(*     TermWf := _ ; *)
(*     BigStep := _ }. *)

Instance L1g_Lang : Lang (Program Term) :=
  { Value := Term;
    TermWf := fun P => match P with
                      mkPgm trm env => WFapp trm /\ program.WFaEnv env
                    end;
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.
