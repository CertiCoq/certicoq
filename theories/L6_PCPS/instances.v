
Require Import cps.
Require Import cps_util.


Require Import certiClasses.
Require Import Common.Common.

(* Fix. L6 bigstep eval (L6.eval.bigstep_e) is strange it is a hetergenous relation of type
  [env -> cps.exp -> val -> nat].
  Perhaps the L6 term type should be (env * (cps.exp + cps.val)) 
  bigstep_e counts costs, which is not a problem because we can existentially quantify 
  over the count.
*)
Instance bigStepOpSemL3Term : BigStepOpSem cps.exp :=
  fun _ _ => True.

(* Fix *)
Instance WfL3Term : WellFormed cps.exp :=
  fun p  => True .

Instance certiL6 : CerticoqLanguage cps.exp := {}.

Require Import L4.instances.
Require Import L5_to_L6.

Instance certiL5a_t0_L6: 
  CerticoqTranslation L5a.cps cps.exp :=
fun x => Ret (convert_top x).






