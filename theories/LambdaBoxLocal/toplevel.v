Require Import LambdaBoxLocal.expression.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import LambdaBoxMut.compile.
Require Import LambdaBoxLocal.LambdaBoxMut_to_LambdaBoxLocal.
Require Import LambdaBoxLocal.LambdaBoxMut_to_LambdaBoxLocal_correct.
Require LambdaBoxMut.
Require Import BinNat.

Import Monads.

Import MonadNotation.

Definition LambdaBoxLocalTerm := prod ienv LambdaBoxLocal.expression.exp.

#[global] Instance LambdaBoxLocal_Lang : Lang LambdaBoxLocalTerm :=
  { Value := LambdaBoxLocal.expression.exp ;
    TermWf := fun P => LambdaBoxLocal.expression.exp_wf (0%N) (snd P);
    BigStep := fun P Res => exists n, LambdaBoxLocal.expression.eval_n n (snd P) = Some Res
  }.

Definition compile_LambdaBoxLocal (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans (Program LambdaBoxMut.compile.Term) LambdaBoxLocalTerm :=
  fun src =>
    debug_msg "Translating from LambdaBoxMut to LambdaBoxLocal"%bs ;;
    LiftCertiCoqTrans "LambdaBoxLocal" (fun p =>  
                              (LambdaBoxMut_to_LambdaBoxLocal.inductive_env (AstCommon.env p),
                               LambdaBoxMut_to_LambdaBoxLocal.translate_program prims (AstCommon.env p)(main p))) src.
