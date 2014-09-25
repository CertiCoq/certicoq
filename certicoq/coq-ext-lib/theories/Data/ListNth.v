Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable T : Type.

  Lemma nth_error_app_L : forall (A B : list T) n,
    n < length A ->
    nth_error (A ++ B) n = nth_error A n.
  Proof.
    induction A; destruct n; simpl; intros; try omega; auto.
    eapply IHA. omega.
  Qed.

  Lemma nth_error_app_R : forall (A B : list T) n,
    length A <= n ->
    nth_error (A ++ B) n = nth_error B (n - length A).
  Proof.
    induction A; destruct n; simpl; intros; try omega; auto.
    apply IHA. omega.
  Qed.

  Lemma nth_error_weaken : forall ls' (ls : list T) n v,
    nth_error ls n = Some v ->
    nth_error (ls ++ ls') n = Some v.
  Proof.
    clear. induction ls; destruct n; simpl; intros; unfold value, error in *; try congruence; auto.
  Qed.

  Lemma nth_error_nil : forall n,
    nth_error nil n = @None T.
  Proof.
    destruct n; reflexivity.
  Qed.

  Lemma nth_error_past_end : forall (ls : list T) n,
    length ls <= n ->
    nth_error ls n = None.
  Proof.
    clear. induction ls; destruct n; simpl; intros; auto.
    exfalso; omega. rewrite IHls; auto. omega.
  Qed.

  Lemma nth_error_length : forall (ls ls' : list T) n,
    nth_error (ls ++ ls') (n + length ls) = nth_error ls' n.
  Proof.
    induction ls; simpl; intros.
    rewrite Plus.plus_0_r. auto.
    cutrewrite (n + S (length ls) = S n + length ls); [ | omega ]. simpl. auto.
  Qed.

  Theorem nth_error_length_ge : forall T (ls : list T) n,
    nth_error ls n = None -> length ls <= n.
  Proof.
    induction ls; destruct n; simpl in *; auto; simpl in *; try omega.
    inversion 1. intro. apply IHls in H. omega.
  Qed.

  Lemma nth_error_length_lt : forall {T} (ls : list T) n val,
    nth_error ls n = Some val -> n < length ls.
  Proof.
    induction ls; destruct n; simpl; intros; auto.
    { inversion H. }
    { inversion H. }
    { omega. }
    { apply Lt.lt_n_S. eauto. }
  Qed.


  Theorem nth_error_map : forall U (f : T -> U) ls n,
    nth_error (map f ls) n = match nth_error ls n with
                               | None => None
                               | Some x => Some (f x)
                             end.
  Proof.
    induction ls; destruct n; simpl; auto.
  Qed.

End parametric.
