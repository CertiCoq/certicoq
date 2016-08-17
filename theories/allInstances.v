Require Export Common.certiClasses.
Require Export L2.instances.
Require Export L4.instances.
Require Export L6.instances.


Quote Recursively Definition p := (3 + 4).

Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Print Instances CerticoqTranslation.
Print Instances CerticoqTotalTranslation.
Print Instances CerticoqLanguage.

Require Import Common.Common.
Eval compute in (translateTo (cTerm certiL4) p).

(* slow! Fix! The above is fast. The translation from L4 to L4a is a bottleneck -- it is
quadratic because of naive fresh name generation and can be made linear.

Eval compute in (translateTo (cTerm certiL4a) p).

*)


Eval vm_compute in (translateTo (cTerm certiL6) p).


