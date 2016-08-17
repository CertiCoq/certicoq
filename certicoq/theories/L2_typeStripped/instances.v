Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.

Instance bigStepOpSemL2Term : BigStepOpSem (Program L2.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** FIX!! *)
Instance WfL2Term : WellFormed (Program L2.compile.Term) :=
  fun _  => True.

Instance certiL2 : CerticoqLanguage (Program L2.compile.Term) := {}.

Local Generalizable Variable Lj.

(** TODO : when the dust settles in L1, move this there *)
Definition translateTo `{CerticoqTranslation (Program L2.compile.Term) Lj}
  (p:program) : exception Lj :=
  let l2:= L2.compile.program_Program p in
  translate (Program L2.compile.Term) Lj l2.


Arguments translateTo Lj {H} p.



