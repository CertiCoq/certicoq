Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Lists.List Coq.omega.Omega
        Coq.Relations.Relations Coq.Classes.RelationClasses.
Require Import cps ctx eval logical_relations identifiers.
Import ListNotations.


Definition empty_env := M.empty val.

Ltac inv H := inversion H; clear H; subst.

Section ctx_approx.

  Variable pr : prims.

  Open Scope ctx_scope.
  
  (** Contextual approximation *)
  Definition ctx_approx : relation exp :=
    fun e1 e2 =>
      forall C i v1, bstep_e pr empty_env (C |[ e1 ]|) v1 i ->
                exists v2 j, bstep_e pr empty_env (C |[ e2 ]|) v2 j.
  
  (** Contextual equivalence *)
  Definition ctx_equiv : relation exp :=
    fun e1 e2 => ctx_approx e1 e2 /\ ctx_approx e2 e1.
  
  Lemma ctx_approx_trans :
  Transitive ctx_approx.
  Proof. 
    intros x y z H1 H2 C i v1 Hstep.
    edestruct H1 as [v2 [j2 Hstep2]]; eauto. 
  Qed.

  Lemma ctx_approx_refl :
    Reflexive ctx_approx.
  Proof. 
    intros x C i v1 Hstep.
    repeat split; eauto.
  Qed.
  
  Lemma ctx_equiv_equiv :
    Equivalence ctx_equiv.
  Proof.
    constructor.
    - split; apply ctx_approx_refl; eauto.
    - split; eapply H.
    - intros x y z [H1 H2] [H3 H4]; split; eapply ctx_approx_trans; eauto.
  Qed.

  Lemma preord_exp_sound e1 e2 :
    (forall k rho1 rho2, preord_env_P pr (occurs_free e1) k rho1 rho2 ->
                    preord_exp pr k (e1, rho1) (e2, rho2)) ->
    ctx_approx e1 e2.
  Proof.
    intros Hyp C i v1 Hstep.
    assert (Hyp' := Hyp).
    eapply (preord_exp_compat pr i empty_env empty_env C) in Hyp;
      [| now eapply preord_env_P_refl ].
    edestruct Hyp as [v2 [c2 [Hstep2 Hpre2]]]; eauto.
  Qed.
  
  Definition x : var := 1%positive.
  Definition y : var := 2%positive.
  
  Definition tau : type := 1%positive.
  Definition c : tag := 1%positive.
  
  Definition stuck : exp :=
    Econstr x tau c [] (
              Econstr y tau c [] (
                        Eapp x [y])).
  
  Lemma stuck_gets_stuck rho :
    ~ (exists v c, bstep_e pr rho stuck v c).
  Proof.
    intros [v [c H]]. inv H. inv H8.
    inv H10. inv H7. inv H9.
    rewrite M.gso, M.gss in H1. inv H1.
    intros Hc. inv Hc.
  Qed.
  
End ctx_approx.