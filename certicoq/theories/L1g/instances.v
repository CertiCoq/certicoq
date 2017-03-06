Require Import L1g.compile.
Require Import L1g.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.

Instance bigStepOpSemL1gTerm : BigStepOpSem (Program L1g.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** FIX!! *)
Instance WfL1gTerm : GoodTerm (Program L1g.compile.Term) :=
  fun _  => True.

Instance certiL1g : CerticoqLanguage (Program L1g.compile.Term) := {}.

Local Generalizable Variable Lj.

Definition translateTo `{CerticoqTranslation (Program L1g.compile.Term) Lj}
  (p:program) : exception Lj :=
  let l1g:= L1g.compile.program_Program p in
  translate (Program L1g.compile.Term) Lj l1g.


Arguments translateTo Lj {H} p.

Definition ctranslateTo {Term Value BigStep WF} 
  (Lj : @CerticoqLanguage Term Value BigStep WF)
   `{CerticoqTranslation (Program L1g.compile.Term) (cTerm Lj)}
   : program -> exception (cTerm Lj) :=
  translateTo (cTerm Lj).

Arguments ctranslateTo {Term0} {Value} {BigStep} {WF} Lj {H} p.






