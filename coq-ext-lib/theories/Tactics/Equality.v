Require Import ExtLib.Structures.EqDep.

Ltac existT_inj :=
  repeat match goal with
           | [ H : @existT _ _ ?X ?Y = @existT _ _ ?X ?Y |- _ ] =>
             clear H
           | [ H : @existT _ _ ?X ?Y = @existT _ _ ?X ?Z |- _ ] =>
             eapply inj_pair2 in H
           | [ H : @existT _ _ ?X _ = @existT _ _ ?Y _ |- _ ] =>
             inversion H
         end.
