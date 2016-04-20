Require Import Relations.
Require Import cps ctx.

Section Relations.

  Variable (R : relation exp).

  Open Scope ctx_scope.
  
  Inductive compat_closure : relation exp :=
  | Compat :
      forall c e e',
        R e e' ->
        compat_closure (c |[ e ]|) (c |[ e' ]|).
      
  Inductive refl_trans_closure_n : nat -> relation exp :=
  | Trans :
      forall n e1 e2 e3,
        R e1 e2 ->
        refl_trans_closure_n n e2 e3 ->
        refl_trans_closure_n (S n) e1 e3
  | Refl :
      forall e, refl_trans_closure_n 0 e e.

  Definition invariant (R : relation exp) (I : exp -> Prop)  : Prop :=
    forall (e1 e2 : exp),
      I e1 -> R e1 e2 -> I e2.

  Lemma invariant_refl_trans_closure (I : exp -> Prop) n :
    invariant R I ->
    invariant (refl_trans_closure_n n) I.
  Proof.
    induction n.
    - intros HInv e1 e2 HI Hrw. inv Hrw; eauto.
    - intros HInv e1 e2 HI Hrw. inv Hrw.
      apply (IHn HInv e3 e2); eauto.
  Qed.

  Definition ctx_compat (I : exp -> Prop) : Prop :=
    (forall c e e', I (c |[ e ]|) -> I e' ->  I (c |[ e' ]|)) /\
    (forall c e,  I (c |[ e ]|) ->  I e).
  

  Lemma invariant_compat_closure (I : exp -> Prop) :
    invariant R I ->
    ctx_compat I ->
    invariant compat_closure I.
  Proof.
    intros HInv [HS1 HS2] e1 e2 HI Hrw. inv Hrw.
    eapply HS1; eauto.
  Qed.

  Lemma refl_trans_closure_f_compat n e1 e2 f :
    (forall e1 e2, R e1 e2 -> R (f e1) (f e2)) ->
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n n (f e1) (f e2).
  Proof.
    revert e1 e2 f. induction n; intros e1 e2 f Hyp H.
    - inv H. constructor.
    - inv H. econstructor. apply Hyp. eauto. eauto. 
  Qed.

  Lemma refl_trans_closure_f_compat_inv n I e1 e2 f :
    invariant R I ->
    (forall e1 e2, I e1 -> R e1 e2 -> R (f e1) (f e2)) ->
    I e1 ->
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n n (f e1) (f e2).
  Proof.
    intros Inv.
    revert e1 e2 f. induction n; intros e1 e2 f Hyp Hyp' H.
    - inv H. constructor.
    - inv H. econstructor. apply Hyp. eauto. eauto. 
      apply IHn; eauto.
  Qed.

  Lemma refl_trans_closure_R_compat n (R' : relation exp) e1 e2 e1' :
    (forall e1 e2 e1',
       R' e1 e1' -> R e1 e2 ->
       exists e2', R e1' e2' /\ R' e2 e2') ->
    R' e1 e1' -> 
    refl_trans_closure_n n e1 e2 ->
    exists e2',
      R' e2 e2' /\
      refl_trans_closure_n n e1' e2'.
  Proof.
    revert e1 e2 e1'. induction n; intros e1 e2 e1' Hyp Hr1 H.
    - inv H. exists e1'. constructor; eauto. constructor.
    - inv H. edestruct Hyp as [e3' [Hrw' Hr3]]; eauto.
      edestruct IHn as [e2' [Hrw Hr2]]; [ | | eauto |]; eauto.
      eexists. split; eauto. econstructor; eauto.
  Qed.

  Lemma refl_trans_closure_R_compat_inv n I (R' : relation exp) e1 e2 e1' :
    invariant R I ->
    (forall e1 e2 e1',
       I e1 -> R' e1 e1' -> R e1 e2 ->
       exists e2', R e1' e2' /\ R' e2 e2') ->
    I e1 ->
    R' e1 e1' -> 
    refl_trans_closure_n n e1 e2 ->
    exists e2',
      R' e2 e2' /\
      refl_trans_closure_n n e1' e2'.
  Proof.
    intros Inv.
    revert e1 e2 e1'. induction n; intros e1 e2 e1' Hyp Hyp' Hr1 H.
    - inv H. exists e1'. constructor; eauto. constructor.
    - inv H.
      edestruct Hyp as [e3' [Hrw' Hr3]]; eauto.
      edestruct IHn as [e2' [Hrw Hr2]]; [ | | | eauto |]; eauto.
      eexists. split; eauto. econstructor; eauto.
  Qed.


  Lemma compat_closure_f_compat e1 e2 f :
    (forall e1 e2, R e1 e2 -> R (f e1) (f e2)) ->
    (forall c,  (exists c1, forall e, f (c |[ e ]|) = c1 |[ f e ]|) \/
                (exists c1, forall e, f (c |[ e ]|) = c1 |[ e ]|)) ->
    compat_closure e1 e2 ->
    compat_closure (f e1) (f e2).
  Proof.
    intros Hyp1 Hyp2 H. inv H.
    destruct (Hyp2 c) as [[c' Heq] | [c' Heq]]; rewrite !Heq; econstructor; eauto.
  Qed.

  Lemma compat_closure_f_compat_inv I e1 e2 f :
    invariant R I -> ctx_compat I ->
    (forall e1 e2, I e1 -> R e1 e2 -> R (f e1) (f e2)) ->
    (forall c,  (exists c1, forall e, f (c |[ e ]|) = c1 |[ f e ]|) \/
                (exists c1, forall e, f (c |[ e ]|) = c1 |[ e ]|)) ->
    I e1 ->
    compat_closure e1 e2 ->
    compat_closure (f e1) (f e2).
  Proof.
    intros Inv [HC1 HC2] Hyp1 Hyp2 HI H. inv H.
    destruct (Hyp2 c) as [[c' Heq] | [c' Heq]]; rewrite !Heq; econstructor; eauto.
  Qed.

(* (* How to call these two ?? *)
Definition rel_ctx_1 c (R : relation exp) :=
  exists c',
    (forall e e', R e e' -> R (c |[ e ]|) (c' |[ e' ]|)) /\ 
    (forall e e', R (c |[ e ]|) e' ->
                  exists e'', e' = c' |[ e'' ]| /\ R e e'').

 Definition rel_ctx_2 c (R : relation exp) :=
  exists c',
    (forall e, R (c |[ e ]|) (c' |[ e ]|)) /\ 
    (forall e e',
       R (c |[ e ]|) e' ->
       (exists e'', e' = c' |[ e'' ]| /\ R e e'') \/ (e' = c' |[ e ]|)).
 
           
Lemma compat_closure_R_compat I (R R' : relation exp) e1 e2 e1':
  invariant R I -> ctx_compat I ->
  (forall e1 e2 e1',
     I e1 -> R e1 e2 -> R' e1 e1' ->
     exists e2', R e1' e2' /\ R' e2 e2') ->
  (forall c, rel_ctx_1 c R' \/ rel_ctx_2 c R') ->
  I e1 ->
  R' e1 e1' ->
  compat_closure R e1 e2 ->
  exists e2', compat_closure R e1' e2' /\ R' e2 e2'.
Proof.
  intros Inv [HC1 HC2] Hyp1 Hyp2 HI Hr1 H. inv H.
  destruct (Hyp2 c) as [[c' [Hc1 Hc2]] | [c' [Hc1 Hc2]]].
  - destruct (Hc2 _ _ Hr1)  as [e1'' [Heq1 Hr1']]; subst.
    edestruct Hyp1 as [e2'' [Heq2 Hr2']]; subst.
    eapply HC2; eauto. eauto. eauto.
    eexists; split; eauto. constructor. eauto.
  - eapply Hc2 in Hr1. inv Hr1.
    + destruct H as [e'' [Heq Hr]]; subst.
      edestruct Hyp1 as [e2'' [Heq2 Hr2']]; subst.
Abort. *)

  Lemma refl_trans_closure_n_trans n m e1 e2 e3:
    refl_trans_closure_n n e1 e2 ->
    refl_trans_closure_n m e2 e3 ->
    refl_trans_closure_n (n+m) e1 e3.
  Proof.
    intros H1 H2. induction H1; eauto.
    econstructor 1; eauto.
  Qed.

  Lemma compat_closure_compat e1 e2 c :
    compat_closure e1 e2 ->
    compat_closure (c |[ e1 ]|) (c |[ e2 ]|).
  Proof.
    intros H. inv H. rewrite !app_ctx_f_fuse.
    constructor; eauto.
  Qed.
  
End Relations.