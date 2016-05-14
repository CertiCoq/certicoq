Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Lists.List Coq.omega.Omega
        Coq.Relations.Relations Coq.Classes.RelationClasses.
Require Import cps ctx eval identifiers.


Definition empty_env := M.empty val.

Open Scope ctx_scope. 

(** Contextual approximation w.r.t. R *)
Definition ctx_approx (R : relation val) : relation exp :=
  fun e1 e2 =>
    forall C i v1, eval.bstep_e empty_env (C |[ e1 ]|) v1 i ->
              exists v2 j, eval.bstep_e empty_env (C |[ e2 ]|) v2 j /\
                      R v1 v2.

(** Contextual equivalence w.r.t. R *)
Definition ctx_equiv (R : relation val) : relation exp :=
  fun e1 e2 => ctx_approx R e1 e2 /\ ctx_approx R e2 e1.


Lemma ctx_approx_trans (R : relation val) :
  Transitive R ->
  Transitive (ctx_approx R).
Proof. 
  intros Ht. intros x y z H1 H2 C i v1 Hstep.
  edestruct H1 as [v2 [j2 [Hstep2 Hr2]]]; eauto. 
  edestruct H2 as [v3 [j3 [Hstep3 Hr3]]]; eauto.
Qed.

Lemma ctx_approx_refl (R : relation val) :
  Reflexive R ->
  Reflexive (ctx_approx R).
Proof. 
  intros Ht. intros x C i v1 Hstep.
  repeat split; eauto.
Qed.

Lemma ctx_equiv_equiv (R : relation val) :
  Transitive R ->
  Reflexive R ->
  Equivalence (ctx_equiv R).
Proof.
  intros Ht Hr. constructor.
  - split; apply ctx_approx_refl; eauto.
  - split; eapply H.
  - intros x y z [H1 H2] [H3 H4]; split; eapply ctx_approx_trans; eauto.
Qed.

Lemma preord_exp_sound (R : relation val) e1 e2 :
  inclusion _ (fun v1 v2 => forall k, preord_val k v1 v2) R ->
  (forall k rho1 rho2, preord_env_P (occurs_free e1) k rho1 rho2 ->
                  preord_exp k (e1, rho1) (e2, rho2)) ->
  ctx_approx R e1 e2.
Proof.
  intros Hincl Hyp C i v1 Hstep.
  assert (Hyp' := Hyp).
  eapply (preord_exp_compat i empty_env empty_env C) in Hyp;
  [| now eapply preord_env_P_refl ].
  edestruct Hyp as [v2 [c2 [Hstep2 Hpre2]]]; eauto.
  repeat eexists; eauto. 
  eapply Hincl. intros k.
  eapply (preord_exp_compat (k + i) empty_env empty_env C) in Hyp';
  [| now eapply preord_env_P_refl ].
  edestruct Hyp' as [v2' [c2' [Hstep2' Hpre2']]]; [| eassumption |]; try omega.
  eapply bstep_e_deterministic in Hstep2'; [| now apply Hstep2 ].
  inv Hstep2'. eapply preord_val_monotonic. now apply Hpre2'. omega.
Qed.