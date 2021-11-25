Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wcbvEval.
Require Import Common.Common Common.classes Common.Pipeline_utils Common.compM.
From ExtLib Require Import Monads.
From MetaCoq.Template Require Import utils Typing.
Import MonadNotation.

Definition erase_PCUIC : CertiCoqTrans Ast.Env.program (global_context * term) :=
  fun src =>
    debug_msg "Translating from Template to Lbox" ;;
    (LiftErrorCertiCoqTrans "Lbox" L1g.compile.erase src).

(* Expose the top-level transformation function *)
Definition compile_L1g : CertiCoqTrans (global_context * term) (Program Term) :=
  fun src =>
    debug_msg "Translating from Lbox to L1" ;;
    (LiftCertiCoqTrans "L1g" L1g.compile.program_Program src).

Definition wf_program (p : Ast.Env.program) := 
  ∥ ∑ T, @Typing.typing 
    config.extraction_checker_flags
    (Ast.Env.empty_ext p.1)
    [] p.2 T ∥.

Definition template_bigstep (p : Ast.Env.program) (v : Ast.term) : Prop :=
  ∥ Template.WcbvEval.eval p.1 [] p.2 v ∥.

#[export] Instance Template_Lang : Lang Ast.Env.program :=
  { Value := Ast.term;
    TermWf := wf_program ;
    BigStep := template_bigstep }.

#[global] Instance L1g_Lang : Lang (Program Term) :=
  { Value := Term;
    TermWf := fun P => match P with
                      mkPgm trm env => WFapp trm /\ program.WFaEnv env
                    end;
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.
