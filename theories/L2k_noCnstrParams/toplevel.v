Require Import L2k.compile.
Require Import L2k.wcbvEval.
Require Import L2k.term.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From ExtLib Require Import Monads.

Require Import Common.Common Common.classes Common.Pipeline_utils Common.compM.
From ExtLib Require Import Monads.
From MetaCoq.Template Require Import utils Typing.
Import MonadNotation.

(* 
Definition erase_PCUIC : CertiCoqTrans Ast.Env.program (global_context * term) :=
  fun src =>
    debug_msg "Translating from Template to Lbox" ;;
    (LiftErrorCertiCoqTrans "Lbox" L1g.compile.erase src).

(* Expose the top-level transformation function *)
Definition compile_L1g : CertiCoqTrans (global_context * term) (Program Term) :=
  fun src =>
    debug_msg "Translating from Lbox to L1" ;;
    (LiftCertiCoqTrans "L1g" L1g.compile.program_Program src).




#[global] Instance L1g_Lang : Lang (Program Term) :=
  { Value := Term;
    TermWf := fun P => match P with
                      mkPgm trm env => WFapp trm /\ program.WFaEnv env
                    end;
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.
 *)

 Definition wf_program (p : Ast.Env.program) := 
  ∥ ∑ T, @Typing.typing config.extraction_checker_flags (Ast.Env.empty_ext p.1) [] p.2 T ∥.

Definition template_bigstep (p : Ast.Env.program) (v : Ast.term) : Prop :=
  ∥ Template.WcbvEval.eval p.1 p.2 v ∥.
 
 #[export] Instance Template_Lang : Lang Ast.Env.program :=
  { Value := Ast.term;
    TermWf := wf_program ;
    BigStep := template_bigstep }. 

Import MonadNotation.

#[export] Instance L2k_Lang : Lang (Program L2k.compile.Term) :=
  { Value := Term;
    TermWf := fun P => L2k.program.crctTerm (AstCommon.env P) 0 (main P);
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.

Definition compile_L2k
  : CertiCoqTrans (Ast.Env.program) (Program L2k.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiCoqTrans "L2k" compile_program src).
