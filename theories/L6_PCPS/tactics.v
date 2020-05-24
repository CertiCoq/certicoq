(* General purpose tactics *)

Require Import Coq.Arith.Arith. 

Ltac inv H := inversion H; clear H; subst.

Ltac subst_exp :=
  match goal with
    | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e2 = ?e |- _ ] =>
      rewrite <- H1 in H2; inv H2
    | [H1 : ?e = ?e1, H2 : ?e2 = ?e |- _ ] =>
      rewrite H1 in H2; inv H2
    | [H1 : ?e1 = ?e, H2 : ?e = ?e2 |- _ ] =>
      rewrite <- H1 in H2; inv H2
  end.

Ltac tci := eauto with typeclass_instances.

Ltac sets := eauto with Ensembles_DB functions_BD.

Ltac xsets := eauto 20 with Ensembles_DB functions_BD.

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.

Ltac pi0 :=
  repeat match goal with
         | [ H: _ + _ = 0 |- _ ] =>
           apply plus_is_O in H; destruct H; subst
         | [ H: 0 = _ + _ |- _ ] =>
           apply plus_is_O in H; destruct H; subst
         (* | [ H: (if cps_util.var_dec ?X ?Y then _ else _) = 0 |- _] => *)
         (*   destruct (cps_util.var_dec X Y); try inversion H; pi0 *)
         | [ H: ?X <> ?X |- _] =>
           exfalso; apply H; auto
         end.
