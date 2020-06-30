
Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.
Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx L6.set_util
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.relations. 
Require Export L6.logical_relations L6.logical_relations_cc.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Section RelComp.


  Context (cenv : ctor_env) (ctag : ctor_tag).

  Definition rel {A} := PostT -> PostGT -> A -> A -> Prop.
  
  Inductive R_n {A} (R : PostT -> PostGT -> A -> A -> Prop) : nat -> PostT -> PostGT -> A -> A -> Prop :=
  | One :
      forall (P : PostT) (PG : PostGT) (c1 : A) (c2: A),
        R P PG c1 c2 ->
        R_n R 0%nat P PG c1 c2
  | More :
      forall (n : nat) (P : PostT) (PG : PostGT) (c1 : A) (c2: A) P1 P2 PG1 PG2 c',
        R P1 PG1 c1 c' ->
        R_n R n P2 PG2 c' c2 ->
        same_relation _ (compose P1 P2) P ->
        same_relation _ (compose PG1 PG2) PG ->
        R_n R (S n) P PG c1 c2.
    
  Definition preord_exp_n n := R_n (fun P PG c1 c2 => forall k, preord_exp cenv P PG k c1 c2) n.  

  Definition preord_val_n n := R_n (fun P PG c1 c2 => forall k, preord_val cenv PG k c1 c2) n.

  Definition preord_res_n n := R_n (fun P PG c1 c2 => forall k, preord_res (preord_val cenv) PG k c1 c2) n.

  Definition R_true : PostT := fun _ _ => True. 

  Lemma R_true_idempotent :
    same_relation _ (compose R_true R_true) R_true.
  Proof.
    firstorder.
  Qed.

  
  (* Lemma preord_res_R_inn n P P' PG v : (* we just don't care *)  *)
  (*   preord_res_n n R PG (Res v) OOT -> *)
  (*   ~ preord_res_n n R' PG (Res v) OOT. *)
      


  Lemma preord_res_n_OOT_r n P PG v :
    ~ preord_res_n n P PG (Res v) OOT.
  Proof.
    revert P PG v. induction n; intros P PG m H.
    - inv H. specialize (H0 0); eauto.
    - inv H. destruct c'. now specialize (H1 0); eauto.
      eapply IHn. eassumption.
  Qed.
  
  Lemma preord_res_n_OOT_l n P PG v :
    ~ preord_res_n n P PG OOT (Res v).
  Proof.
    revert P PG v. induction n; intros P PG m H.
    - inv H. specialize (H0 0); eauto.
    - inv H. destruct c'.
      eapply IHn. eassumption.
      now specialize (H1 0); eauto.      
  Qed.

  Lemma preord_exp_n_impl (n : nat) (P : PostT) (PG : PostGT) (c1 : exp * env) (c2: exp * env) :
    preord_exp_n n P PG c1 c2 ->
    (let
        '(e1, rho1) := c1 in
      let
        '(e2, rho2) := c2 in
      forall (v1 : res) (cin : nat),
        bstep_fuel cenv rho1 e1 v1 cin ->
        exists (v2 : res) (cin' : nat),
          bstep_fuel cenv rho2 e2 v2 cin' /\
          P (e1, rho1, cin) (e2, rho2, cin') /\
          preord_res_n n R_true PG v1 v2).
  Proof.
    intros Hrel. induction Hrel.
    + (* base case *)
      destruct c1, c2. intros. edestruct (H cin); eauto. destructAll.
      do 2 eexists. split; eauto. split; eauto. eapply One. intros k.
      edestruct (H (k + cin)); [| eassumption | ]. omega. destructAll.
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x1; eauto. simpl in H6. contradiction. 
        eapply bstep_fuel_deterministic in H1; [| clear H1; eassumption ].
        inv H1. eapply preord_res_monotonic. eassumption. omega. 
    + destruct c1 as [e1 rho1]; destruct c2 as [e2 rho2]; destruct c' as [e' rho'].
      intros. edestruct H; eauto. destructAll.
      edestruct IHHrel. eassumption. destructAll. 
      do 2 eexists. split; eauto. split.
      eapply H0. do 2 eexists. eassumption. eassumption. 
      eapply More; [| eassumption | eapply R_true_idempotent | eassumption ].
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x1. simpl in H8; eauto. simpl in H8. eapply preord_res_n_OOT_r in H8. contradiction.
        intros k.
        edestruct (H (k + cin)); [| eassumption | ]. omega. destructAll. destruct x; eauto. simpl in H11. contradiction. 
        eapply bstep_fuel_deterministic in H3; [| clear H3; eassumption ]. destructAll.
        eapply preord_res_monotonic. eassumption. omega.
  Qed.
  

  Definition P_implies_u_bound K M (p1 p2 : exp * env) (P : PostT) :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall c1 c2,
      P (e1, rho1, c1) (e2, rho2, c2) ->
      c1 <= (M + 1) * c2 + K.
    
  (* preord_exp_n preserves divergence *)
  Lemma preord_exp_n_preserves_divergence n K M P PG e1 rho1 e2 rho2 :
    P_implies_u_bound K M (e1, rho1) (e2, rho2) P ->
    preord_exp_n n P PG (e1, rho1) (e2, rho2) ->
    diverge cenv rho1 e1 -> 
    diverge cenv rho2 e2.
  Proof.
    intros Hrel Hexp Hdiv.
    eapply preord_exp_n_impl in Hexp. 
    intros c2. specialize (Hdiv ((M + 1)*c2 + K)).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. eassumption.
    eapply Hrel in Hp. 
    assert (Hleq : c2 <= c2').
    { eapply NPeano.Nat.add_le_mono_r in Hp.
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp. eassumption. omega. }
    destruct v2.
    + eapply bstep_fuel_OOT_monotonic. eassumption. eassumption.
    + eapply preord_res_n_OOT_l in Hval; eauto. contradiction.
  Qed.


  Lemma preord_exp_n_preserves_not_stuck K M n (P : PostT) (PG : PostGT) e1 rho1 e2 rho2 :
    P_implies_u_bound K M (e1, rho1) (e2, rho2) P ->
    not_stuck cenv rho1 e1 ->
    preord_exp_n n P PG (e1, rho1) (e2, rho2) ->
    not_stuck cenv rho2 e2.
  Proof.
    intros Piml Hns Hexp. inv Hns.
    - destructAll. eapply preord_exp_n_impl in Hexp.
      eapply Hexp in H; eauto. destructAll. destruct x1; eauto.
      eapply preord_res_n_OOT_r in H1. contradiction.
      left. eauto.
    - right. eapply preord_exp_n_preserves_divergence; eassumption.
  Qed.
  

  Definition post_propetry {A} := A -> A -> PostT -> Prop.

  Definition compose_rel {A} (Pr1 Pr2 : post_propetry) (* impose things on the intermediate rels *)
             (R1 R2 : rel) (P : PostT) (PG : PostGT) (c1 : A) (c2: A) : Prop :=
    exists P1 P2 PG1 PG2 c',
      R1 P1 PG1 c1 c' /\
      R2 P2 PG2 c' c2 /\
      same_relation _ (compose P1 P2) P /\
      same_relation _ (compose PG1 PG2) PG /\
      Pr1 c1 c' P1 /\ Pr2 c' c2 P2.

  Definition Pr_trivial {A} : @post_propetry A:= fun _ _ _ => True.
  
  (* Top-level relation for L6 pipeline *)
  Definition R_n_exp Pr1 Pr2 Pr3 Pr4 n m : rel :=
    compose_rel Pr1 Pr2
                (preord_exp_n n)
                (compose_rel Pr3 Pr4
                             (fun P PG c1 c2 => forall k, cc_approx_exp cenv ctag k P PG c1 c2) (preord_exp_n m)).
  
  Definition R_n_res n m : rel :=
    compose_rel Pr_trivial Pr_trivial (preord_res_n n)
                (compose_rel Pr_trivial Pr_trivial (fun P PG c1 c2 => forall k, cc_approx_res (cc_approx_val cenv ctag) k PG c1 c2) (preord_res_n m)).
  
  Definition R_n_val n m : rel :=
    compose_rel Pr_trivial Pr_trivial (preord_res_n n)
                (compose_rel Pr_trivial Pr_trivial (fun P PG c1 c2 => forall k, cc_approx_res (cc_approx_val cenv ctag) k PG c1 c2) (preord_res_n m)).
  
  
  Lemma R_n_exp_impl K M (n m : nat) (P : PostT) (PG : PostGT) e1 rho1 e2 rho2 :    
    R_n_exp (P_implies_u_bound K M) Pr_trivial Pr_trivial Pr_trivial n m P PG (e1, rho1) (e2, rho2) ->
    (forall (v1 : res) (cin : nat),
        bstep_fuel cenv rho1 e1 v1 cin ->
        not_stuck cenv rho1 e1 ->
        exists (v2 : res) (cin' : nat),
          bstep_fuel cenv rho2 e2 v2 cin' /\
          P (e1, rho1, cin) (e2, rho2, cin') /\
          R_n_res n m R_true PG v1 v2).
  Proof.
    intros Hrel. inv Hrel. destructAll. inv H0. destructAll.
    assert (Hexp1 := H). assert (Hexp2 := H5).
    eapply preord_exp_n_impl in H. 
    eapply preord_exp_n_impl in H5.
    destruct x3, x8. intros. edestruct H. eassumption. destructAll.    
    edestruct (H0 x8); eauto.

    eapply preord_exp_n_preserves_not_stuck; eassumption.
    
    destructAll. edestruct H5. eassumption. destructAll.
    
    do 2 eexists. split; eauto. split; eauto.

    eapply H1. eexists. split. eassumption. eapply H6. eexists. split; eassumption.

    do 5 eexists. split. eassumption.
    split; [| split; [ now eapply R_true_idempotent |  split; [ eassumption | now clear; firstorder ]]]. 

    do 5 eexists. split; [| split; [| split; [ now eapply R_true_idempotent | split; [ eassumption | now clear; firstorder ]]]].
    2:{ eassumption. }

    intros k. 
    destruct v1.
    - destruct x3.
      * destruct x9; eauto.
      * eapply preord_res_n_OOT_l in H14. contradiction.
    - destruct x3.
      + eapply preord_res_n_OOT_r in H14. contradiction.
      + destruct x9; eauto.
        edestruct (H0 (k + x8)); [| eassumption | | ]. omega.
        eapply preord_exp_n_preserves_not_stuck; eassumption.

        destructAll.
        destruct x3. simpl in H18. contradiction.
        eapply bstep_fuel_deterministic in H15; [| clear H15; eassumption ]. inv H15.
        eapply cc_approx_res_monotonic. eassumption. omega.
  Qed.

  (* Divergence preservation *)
  Lemma cc_approx_exp_rreserves_divergence K M P PG e1 rho1 e2 rho2 :
    P_implies_u_bound K M (e1, rho1) (e2, rho2) P ->
    (forall k, cc_approx_exp cenv ctag k P PG (e1, rho1) (e2, rho2)) ->
    diverge cenv rho1 e1 -> 
    diverge cenv rho2 e2.
  Proof.
    intros Hrel Hexp Hdiv. assert (Hdiv' := Hdiv).
    intros c2. specialize (Hdiv ((M + 1)*c2 + K)).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. reflexivity. eassumption.
    right. eassumption.
    
    eapply Hrel in Hp. 
    assert (Hleq : c2 <= c2').
    { eapply NPeano.Nat.add_le_mono_r in Hp.
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp. eassumption. omega. }
    destruct v2.
    + eapply bstep_fuel_OOT_monotonic. eassumption. eassumption.
    + contradiction.
  Qed.

  
  (* R_n_exp preserves divergence *)
  Lemma R_n_exp_preserves_divergence n m K1 M1 K2 M2 K3 M3 P PG e1 rho1 e2 rho2 :
    R_n_exp (P_implies_u_bound K1 M1) Pr_trivial (P_implies_u_bound K2 M2) (P_implies_u_bound K3 M3) n m P PG (e1, rho1) (e2, rho2) ->
    diverge cenv rho1 e1 -> 
    diverge cenv rho2 e2.
  Proof.
    intros Hrel Hdiv. inv Hrel. destructAll. destruct x3. inv H0. destructAll. destruct x7. 
    eapply preord_exp_n_preserves_divergence; [ eassumption | eassumption | ].
    eapply cc_approx_exp_rreserves_divergence; [ eassumption | eassumption | ].
    eapply preord_exp_n_preserves_divergence; eassumption.
  Qed.


  
  Section Linking.

    Definition link_src (e1 e2 : exp) : option exp :=
      match e2 with
      | Efun (Fcons f ft [x] e Fnil) (Ehalt f') =>
        if (f =? f')%positive then  
          match inline_letapp e x with
          | Some (C, x') =>
            Some (C |[ Efun (Fcons f ft [x] e Fnil) (Eapp f ft [x'])]|)
          | None => None
          end
        else None
      | _ => None
      end.

    Definition link_trg (e1 e2 : exp) : option exp :=
      match e2 with
      | Efun (Fcons f ft [x] e Fnil) (Ehalt f') =>
        if (f =? f')%positive then  
          match inline_letapp e x with
          | Some (C, x') =>
            let fv := max_var e1 f in
            let f' := (fv + 1)%positive in
            let Γ := (fv + 2)%positive in
            Some (C |[ Efun (Fcons f ft [x] e Fnil) (AppClo ctag f f' Γ |[ Eapp f ft [Γ; x] ]|) ]|)
          | None => None
          end
        else None
      | _ => None
      end.


    Lemma preord_exp_preserves_linking_src k P PG e1 e2 e1' e2' :
      preord_exp cenv P PG k (e1, M.empty _) (e2, M.empty _) ->
      preord_exp cenv P PG k (e1', M.empty _) (e2', M.empty _) ->
      match link_src e1 e1', link_src e2 e2' with
      | Some e, Some e' =>
        preord_exp cenv P PG k (e, M.empty _) (e', M.empty _)
      | _ , _ => True
      end.
    Proof.
      intros Hexp1 Hexp2. unfold link_src.
      
      destruct e1'; eauto. destruct f; eauto. destruct l; eauto. destruct l; eauto.
      destruct f0; eauto.  destruct e1'; eauto. destruct ((v =? v1)%positive); eauto.
      destruct (inline_letapp e v0) as [[C z] | ] eqn:Hinl1; eauto.

      destruct e2'; eauto. destruct f0; eauto. destruct l; eauto. destruct l; eauto.
      destruct f1; eauto.  destruct e2'; eauto. destruct ((v2 =? v4)%positive); eauto.
      destruct (inline_letapp e0 v3) as [[C' z'] | ] eqn:Hinl2; eauto.
      
      
      

      
      ; destruct e2'; eauto. 
      destruct e1. 
      
      
