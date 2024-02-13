Require Import LambdaBoxMut.compile.
Require Import LambdaBoxMut.wcbvEval.
Require Import LambdaBoxMut.term.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From ExtLib Require Import Monads.

Require Import Common.Common Common.classes Common.Pipeline_utils Common.compM.
From ExtLib Require Import Monads.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Typing.
Import MonadNotation.

 Definition wf_program (p : Ast.Env.program) := 
  ∥ ∑ T, @Typing.typing config.extraction_checker_flags (Ast.Env.empty_ext p.1) [] p.2 T ∥.

Definition template_bigstep (p : Ast.Env.program) (v : Ast.term) : Prop :=
  ∥ Template.WcbvEval.eval p.1 p.2 v ∥.
 
 #[export] Instance Template_Lang : Lang Ast.Env.program :=
  { Value := Ast.term;
    TermWf := wf_program ;
    BigStep := template_bigstep }. 

Import MonadNotation.

#[export] Instance LambdaBoxMut_Lang : Lang (Program LambdaBoxMut.compile.Term) :=
  { Value := Term;
    TermWf := fun P => LambdaBoxMut.program.crctTerm (AstCommon.env P) 0 (main P);
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.

Definition compile_LambdaBoxMut econf
  : CertiCoqTrans (Ast.Env.program) (Program LambdaBoxMut.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiCoqTrans "LambdaBoxMut" (compile_program econf) src).
