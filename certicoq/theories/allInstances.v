Require Export Common.certiClasses.
Require Export L2.instances.
Require Export L4.instances.
(*Require Export L6.instances.*)


Quote Recursively Definition p := (3 + 4).

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Print Instances CerticoqTranslation.
Print Instances CerticoqTotalTranslation.
Print Instances CerticoqLanguage.

Require Import Common.Common.
Eval compute in (translateTo (cTerm certiL4) p).

Time Eval compute in (translateTo (cTerm certiL5a) p).

(* Fix the type of [certiL5a_t0_L6]. It should return (cTerm certiL6) which 
also contains an environment. 
To debug typeclass resolution problems, try:
Typeclasses eauto := 5. (* or a small number to limit the search depth *)
Typeclasses eauto := debug. (* if your ide doesn't show debug messages, use coqc *)

Eval vm_compute in (translateTo (* (cTerm certiL6) *) cps.exp p).


*)


