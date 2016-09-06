Require Import L4.expression.
Require Import certiClasses.
Require Import Common.Common.
Require Import L3.compile.
Require Import L4.L3_to_L4.
Require Import L3.instances.

Require Import BinNat.

Program Instance : BigStepOpSem L4.expression.exp := eval.

Program Instance : WellFormed L4.expression.exp :=
 L4.expression.exp_wf (0%N).

Instance certiL4: CerticoqLanguage L4.expression.exp := {}.

Instance certiL3_to_L4: 
  CerticoqTranslation (Program L3.compile.Term) L4.expression.exp  :=
fun p => Ret (L3_to_L4.translate_program (AstCommon.env p) (main p)).

Instance failed: 
  CerticoqTranslationCorrect (Program L3.compile.Term) L4.expression.exp.
constructor.
- admit.
- intros ? ? Hwf He.
  destruct Hwf.
  unfold certiClasses.translate,
    certiL3_to_L4, liftBigStepException, bigStepEval, BigStepOpSem_instance_0.
  unfold translate_program.
(*  Fail eapply L3_to_L4_correct.translate_correct.  *)
(* not applicable!! do we need to change the end to end correctness property?, 
  or can the L3_to_L4 translation syntactically preserve big step eval? *)
Abort.

Require Import L4_to_L4a.
Require Import L4a_to_L5.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.

Definition L4aTerm :Type := (@NTerm cps.var L4Opid).

Program Instance : BigStepOpSem L4aTerm := eval.

(** all variables must be user variables *)
Program Instance : WellFormed L4aTerm :=
  fun e  => varsOfClass (all_vars e) true /\ isprogram e.

Instance certiL4a: CerticoqLanguage L4aTerm := {}.


Instance certiL4_to_L4a: 
  CerticoqTotalTranslation L4.expression.exp L4aTerm :=
  (L4_to_L4a (0)%N).


Definition L5Term :Type := (@NTerm cps.var L5Opid).

Program Instance : BigStepOpSem L5Term := eval_c.

Program Instance : WellFormed L5Term := isprogram.

Instance certiL5: CerticoqLanguage L5Term := {}.

Instance certiL4a_to_L5:
  CerticoqTranslation L4aTerm L5Term:=
  fun x => Ret (cps_cvt x).


Require Import L4.L5a.

(* Fix. Define subst and evaluation on L5a by going to L5 via a bijection? *)
Program Instance : BigStepOpSem L4.L5a.val_c := fun _ _ => True.

(** Fix *)
Program Instance : WellFormed L4.L5a.val_c := fun x => False.

Instance certiL5a: CerticoqLanguage L4.L5a.val_c := {}.

Instance certiL5_to_L5a: 
  CerticoqTranslation  L5Term L4.L5a.val_c :=
  fun e =>
   match L4.L5a.translateVal e with
  | None => exceptionMonad.Exc "error in L5a.translateVal"
  | Some e => exceptionMonad.Ret e
  end.

Require Import Template.Template.
Quote Recursively Definition p0L1 := 0.

Require Import L2.instances.

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Eval compute in (translateTo (cTerm certiL5a) p0L1).
(*
     = Ret
         (Cont_c 5%positive
            (Ret_c (KVar_c 5%positive) (Con_c (mkInd "Coq.Init.Datatypes.nat" 0, 0%N) nil)))
     : exception val_c
*)


  









