Require Import L2_5.compile.
(* Require Import L2.wcbvEval. *)
Require Import certiClasses.
Require Import Common.Common.

(** FIX!! *)
Instance bigStepOpSemL2_5_Term : BigStepOpSem (Program L2_5.compile.Term) :=
  fun _ _ => True.

(** FIX!! *)
Instance WfL2_5_Term : GoodTerm (Program L2_5.compile.Term) :=
  fun _  => True.

Require Import certiClasses2.
(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead (Program L2_5.compile.Term) :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermTermL : ObserveNthSubterm (Program L2_5.compile.Term) :=
fun n t => None.


Instance certiL2_5 : CerticoqLanguage (Program L2_5.compile.Term) := {}.


Instance certiL2_to_L2_5: 
  CerticoqTotalTranslation (Program L2.compile.Term) (Program L2_5.compile.Term) :=
L2_5.compile.L2Pgm_Program.






