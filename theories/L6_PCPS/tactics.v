(* General purpose tactics *)

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

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.
