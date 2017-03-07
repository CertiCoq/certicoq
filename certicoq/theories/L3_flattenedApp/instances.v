Require Import L3.compile.
Require Import L3.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.


(* Do we need to use [L4.L3_to_L4_correct.eval_env]? on the environment*)
Instance bigStepOpSemL3Term : BigStepOpSem (Program L3.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(* Move [wf_environ] to L3? 
Require Import L4.L3_to_L4_correct.

Instance WfL3Term : GoodTerm (Program L3.compile.Term) :=
  fun p  => L3.program.Crct (env p) 0 (main p) /\ (wf_environ (env p)).
*)

(* Fix -- use the one above when L4.L3_to_L4_correct.v compiles *)
Instance WfL3Term : GoodTerm (Program L3.compile.Term) :=
  fun p  => True.

Require Import certiClasses2.
(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead (Program L3.compile.Term) :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermL : ObserveNthSubterm (Program L3.compile.Term) :=
fun n t => None.

Instance certiL3 : CerticoqLanguage (Program L3.compile.Term) := {}.

Instance certiL2_to_L3: 
  CerticoqTranslation (Program L2_5.compile.Term) (Program L3.compile.Term) :=
fun x => Ret (L3.compile.stripProgram x).
