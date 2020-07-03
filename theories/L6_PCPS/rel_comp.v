
Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.
Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx L6.set_util
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.relations. 
Require Export L6.logical_relations L6.logical_relations_cc L6.alpha_conv L6.inline_letapp.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Section Compose.

  Context {A : Type}.

  (* Properties that the intermediate post conditions have *)
  Definition post_property := PostT -> Prop.
  
  Context (wf_pres : A -> A -> Prop)
          (wf : A -> Prop)
          (post_prop : post_property).
  
  
  Definition log_rel := PostT -> PostGT -> A -> A -> Prop.
  Definition rel := PostT -> A -> A -> Prop.
  

  Inductive R_n (R : PostT -> PostGT -> A -> A -> Prop) : nat -> PostT -> A -> A -> Prop :=
  | One :
      forall (P : PostT) (c1 : A) (c2: A),
        R P P c1 c2 ->
        wf_pres c1 c2 ->
        post_prop P ->
        R_n R 1%nat P c1 c2
  | More :
      forall (n : nat) (P : PostT) (c1 : A) (c2: A) P1 P2 c',
        R P1 P1 c1 c' ->
        R_n R n P2 c' c2 ->
        wf_pres c1 c' -> (* well-formedness is preserved *)
        post_prop P1 -> (* the indermediate post has some desired property *)
        same_relation _ (compose P1 P2) P ->
        R_n R (S n) P c1 c2.

    Definition compose_rel (P1 P2 : PostT)
               (Pr1 Pr2 : post_property)
               (R1 R2 : rel) (c1 : A) (c2: A) : Prop :=
      exists c',
        R1 P1 c1 c' /\
        R2 P2 c' c2 /\
        Pr1 P1 /\ Pr2 P2.     

End Compose.

Definition pr_trivial : post_property := fun _ => True.

Definition wf_trivial {A} : A -> A -> Prop := fun _ _ => True.

Definition preserves_fv (e1 e2 : exp) := occurs_free e2 \subset occurs_free e1.

Fixpoint straight_code (e : exp) :=
  match e with
  | Econstr _ _ _ e
  | Eprim _ _ _ e
  | Eproj _ _ _ _ e
  | Eletapp _ _ _ _ e 
  | Efun _ e => straight_code e    
  | Ecase _ _ => false 
  | Eapp _ _ _ => true
  | Ehalt _ => true
  end.

Definition preserves_straight_code (e1 e2 : exp) := straight_code e1 = true -> straight_code e2 = true.


Section RelComp.

  Context (cenv : ctor_env) (ctag : ctor_tag).

  Context (wf_pres : exp -> exp -> Prop) (wf : exp -> Prop) (post_prop : post_property).
   
  Definition preord_exp_n n := R_n wf_pres post_prop
                                   (fun P PG e1 e2 =>
                                      forall k rho1 rho2,
                                        preord_env_P cenv PG (occurs_free e1) k rho1 rho2 ->
                                        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) n.  

  Definition preord_env_n n S := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_env_P cenv P S k c1 c2) n.  

  Definition preord_val_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_val cenv PG k c1 c2) n.

  Definition preord_res_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_res (preord_val cenv) PG k c1 c2) n.

  Definition R_true : PostT := fun _ _ => True. 
  
  Lemma R_true_idempotent :
    same_relation _ (compose R_true R_true) R_true.
  Proof.
    firstorder.
  Qed.
  
  Lemma preord_res_n_OOT_r n P v :
    ~ preord_res_n n P (Res v) OOT.
  Proof.
    revert P v. induction n; intros P m H.
    - inv H.
    - inv H. now specialize (H1 0); eauto.
      destruct c'. specialize (H1 0). contradiction.
      eapply IHn. eassumption.
  Qed.
  
  Lemma preord_res_n_OOT_l n P v :
    ~ preord_res_n n P OOT (Res v).
  Proof.
    revert P v. induction n; intros P m H.
    - inv H.
    - inv H. specialize (H1 0). contradiction.
      destruct c'. eapply IHn. eassumption.
      now specialize (H1 0); eauto.      
  Qed.

  Context (Hwf : forall e1 e2, wf_pres e1 e2 -> preserves_fv e1 e2).


  Lemma closed_preserved e1 e2 :
    closed_exp e1 ->
    wf_pres e1 e2 ->
    closed_exp e2.
  Proof.
    intros Hc1 Hwf1. split; [| now sets ]. eapply Included_trans.
    eapply Hwf. eassumption. eapply Hc1.
  Qed.
  
  Context (Hwf_c : forall e1 e2, wf_pres e1 e2 -> closed_exp e1 -> closed_exp e2).
  
  
  Lemma preord_exp_n_impl (n : nat) (P : PostT) (e1 : exp) (e2: exp) :
    closed_exp e1 ->
    preord_exp_n n P e1 e2 ->
    
    (forall rho1 rho2,        
      forall (v1 : res) (cin : nat),
        bstep_fuel cenv rho1 e1 v1 cin ->
        exists (v2 : res) (cin' : nat),
          bstep_fuel cenv rho2 e2 v2 cin' /\
          P (e1, rho1, cin) (e2, rho2, cin') /\
          preord_res_n n P v1 v2).
  Proof.
    intros Hwfe Hrel. induction Hrel.
    + (* base case *)
      intros. edestruct (H cin); eauto.
      eapply preord_env_P_antimon; [| eapply Hwfe ]. now intros z Hin; inv Hin.  
      destructAll.
      do 2 eexists. split; eauto. split; eauto. eapply One. intros k.
      edestruct (H (k + cin) rho1 rho2); [| | eassumption | ].
      eapply preord_env_P_antimon; [| eapply Hwfe ].
      now intros z Hin; inv Hin. omega. destructAll.
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x1. contradiction.
        eapply bstep_fuel_deterministic in H3; [| clear H3; eassumption ].
        inv H3. eapply preord_res_monotonic. eassumption. omega.
      * clear. firstorder.
      * clear; now firstorder.
    + intros. edestruct H; eauto. 
      eapply preord_env_P_antimon with (rho2 := rho2); [| eapply Hwfe ]. now intros z Hin; inv Hin. destructAll.
      edestruct IHHrel. eapply Hwf_c. eassumption. eassumption. eassumption.
      destructAll. 
      do 2 eexists. split; eauto. split.
      eapply H2. do 2 eexists. eassumption. eassumption. 
      eapply More; [| eassumption | | eapply R_true_idempotent | eassumption ].
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x1. eapply preord_res_n_OOT_r in H9. contradiction.
        intros k.
        edestruct (H (k + cin)); [| | eassumption | ].
        eapply preord_env_P_antimon; [| eapply Hwfe ]. now intros z Hin; inv Hin. omega. destructAll.
        destruct x; eauto. simpl in H11. contradiction.
        eapply bstep_fuel_deterministic in H4; [| clear H4; eassumption ]. destructAll.
        eapply preord_res_monotonic. eassumption. omega.
      * clear. firstorder.
      * clear. firstorder. split; eauto.

        Grab Existential Variables. eauto. eauto. (* Not sure where this comes from *)
  Qed.  
  
  Definition P_implies_u_bound (P : PostT) :=
    forall e1 rho1 e2 rho2,
    exists K M,
    forall c1 c2,
      P (e1, rho1, c1) (e2, rho2, c2) ->
      c1 <= (M + 1) * c2 + K.
    
  (* preord_exp_n preserves divergence *)
  Lemma preord_exp_n_preserves_divergence n P e1 e2 :
    P_implies_u_bound P ->
    closed_exp e1 ->
    
    preord_exp_n n P e1 e2 ->
    diverge cenv (M.empty _) e1 -> 
    diverge cenv (M.empty _) e2.
  Proof. 
    intros Hrel Hef Hexp Hdiv. destruct (Hrel e1 (M.empty _) e2 (M.empty _)) as [K [M Himpl]].
    
    intros c2. specialize (Hdiv ((M + 1)*c2 + K)).
    eapply preord_exp_n_impl in Hexp; [| eassumption | eassumption ].
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]].
    eapply Himpl in Hp. 
    assert (Hleq : c2 <= c2').
    { eapply NPeano.Nat.add_le_mono_r in Hp.
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp. eassumption. omega. }
    destruct v2.
    + eapply bstep_fuel_OOT_monotonic. eassumption. eassumption.
    + eapply preord_res_n_OOT_l in Hval; eauto. contradiction.
  Qed.


  Lemma preord_exp_n_preserves_not_stuck n (P : PostT) e1 e2 :
    P_implies_u_bound P ->
    closed_exp e1 ->
    
    preord_exp_n n P e1 e2 ->
    not_stuck cenv (M.empty _) e1 ->    
    not_stuck cenv (M.empty _) e2.
  Proof.
    intros Piml Hwfe Hexp Hns. inv Hns.
    - destructAll. eapply preord_exp_n_impl in Hexp; [| eassumption | eassumption ].
      destructAll. destruct x1; eauto.
      eapply preord_res_n_OOT_r in H2. contradiction.
      left. eauto.
    - right. eapply preord_exp_n_preserves_divergence; eassumption.
  Qed.
  
  
  (* Top-level relation for L6 pipeline *)
  Definition R_n_exp P1 P2 P3 Pr1 Pr2 Pr3 Pr4 n m : relation exp :=
    compose_rel P1 P2 Pr1 Pr2
                (preord_exp_n n)
                (fun P2 => compose_rel P2 P3 Pr3 Pr4
                                       (fun P e1 e2 =>
                                          wf_pres e1 e2 /\ 
                                          forall k rho1 rho2 ,
                                            cc_approx_env_P cenv ctag (occurs_free e1) k P rho1 rho2 ->
                                            cc_approx_exp cenv ctag k P P (e1, rho1) (e2, rho2)) (preord_exp_n m)).

  Definition post_trivial : PostT := fun c1 c2 => True.
  
  Definition R_n_res P1 P2 P3 n m : relation res :=
    compose_rel P1 P2 pr_trivial pr_trivial (preord_res_n n)
                (fun P2 => compose_rel P2 P3 pr_trivial pr_trivial 
                                       (fun P c1 c2 => forall k, cc_approx_res (cc_approx_val cenv ctag) k P c1 c2) (preord_res_n m)).
  
  Definition R_n_val P1 P2 P3 n m : relation val :=    
    compose_rel P1 P2 pr_trivial pr_trivial (preord_val_n n)
                (fun P2 => compose_rel P2 P3 pr_trivial pr_trivial
                                       (fun P (c1 : val) (c2 : val) => forall k, cc_approx_val cenv ctag k P c1 c2) (preord_val_n m)).

  Definition Pr_in_P_implies_u_bound (Pr1 : post_property) :=
    (forall P, Pr1 P -> P_implies_u_bound P). 

  Context (P1 P2 P3 : PostT)
          (Pr1 Pr2 Pr3 Pr4 : post_property)
          (wf_pres_trans : Transitive wf_pres).

  Lemma preord_exp_n_wf_pres n P e1 e2 : 
    preord_exp_n n P e1 e2 ->
    wf_pres e1 e2.
  Proof.
    intros Hn. induction Hn; eauto.
  Qed.
                 
  Lemma R_n_exp_impl (n m : nat) e1 e2 :    
    closed_exp e1 ->
    Pr_in_P_implies_u_bound Pr1 ->
    
    R_n_exp P1 P2 P3 Pr1 Pr2 Pr3 Pr4 n m e1 e2 ->
      
    forall (v1 : res) (cin : nat),
      bstep_fuel cenv (M.empty _) e1 v1 cin ->
      not_stuck cenv (M.empty _) e1 ->
      exists (v2 : res) (cin' : nat),
        bstep_fuel cenv (M.empty _) e2 v2 cin' /\
        (comp P1 (comp P2 P3)) (e1, (M.empty _), cin) (e2, M.empty _, cin') /\
        R_n_res P1 P2 P3 n m v1 v2.
  Proof.
    intros Hwfe Himpl Hrel. inv Hrel. destructAll. inv H0. destructAll. 
    assert (Hexp1 := H). assert (Hexp2 := H4). intros.
    eapply preord_exp_n_impl in H; [| eassumption | eassumption ]. destructAll.
    edestruct (H6 x2 (M.empty _) (M.empty _)); eauto.
    eapply cc_approx_env_P_antimon. 2:{ eapply Hwf_c. eapply preord_exp_n_wf_pres. eassumption. eassumption. }
    intros z Hin. inv Hin.
    
    eapply preord_exp_n_preserves_not_stuck. eapply Himpl; eassumption. eassumption. eassumption. eassumption.
    
    destructAll.
    eapply preord_exp_n_impl in H3; [| | eassumption ].
    2:{ eapply Hwf_c. eapply wf_pres_trans; [| eassumption ]. eapply preord_exp_n_wf_pres. eassumption. eassumption. }
    destructAll. 
    do 2 eexists. split; eauto. split.
    
    eexists. split. eassumption. eexists. split; eassumption.
    
    eexists. split. eassumption. split.
    2:{ clear. now firstorder. }
    eexists. split.
    2:{ split. eassumption. clear. now firstorder. }
    
    intros k. 
    destruct v1.
    - destruct x1.
      * destruct x3; eauto. 
      * eapply preord_res_n_OOT_l in H10. contradiction.
    - destruct x1.
      + eapply preord_res_n_OOT_r in H10. contradiction.
      + destruct x3; eauto.
        edestruct (H6 (k + x2)) with (rho2 := (M.empty val)); [| | eassumption | | ].
        eapply cc_approx_env_P_antimon; [| eapply Hwf_c; eauto ].
        intros z Hin. now inv Hin.
        eapply preord_exp_n_wf_pres. eassumption.
        omega.
        
        eapply preord_exp_n_preserves_not_stuck. eapply Himpl. eassumption. eassumption. eassumption. eassumption.
        
        destructAll.
        destruct x1. contradiction.
        eapply bstep_fuel_deterministic in H16; [| clear H16; eassumption ]. inv H16.
        eapply cc_approx_res_monotonic. eassumption. omega.
  Qed.

  (* Divergence preservation *)
  Lemma cc_approx_exp_rreserves_divergence P PG e1 rho1 e2 rho2 :
    P_implies_u_bound P ->
    (forall k, cc_approx_exp cenv ctag k P PG (e1, rho1) (e2, rho2)) ->
    diverge cenv rho1 e1 -> 
    diverge cenv rho2 e2.
  Proof.
    intros Hrel Hexp Hdiv. assert (Hdiv' := Hdiv).
    destruct (Hrel e1 rho1 e2 rho2) as [K [M Himpl]].
    intros c2. specialize (Hdiv ((M + 1)*c2 + K)).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. reflexivity. eassumption.
    right. eassumption.
    
    eapply Himpl in Hp. 
    assert (Hleq : c2 <= c2').
    { eapply NPeano.Nat.add_le_mono_r in Hp.
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp. eassumption. omega. }
    destruct v2.
    + eapply bstep_fuel_OOT_monotonic. eassumption. eassumption.
    + contradiction.
  Qed.
  
  
  (* R_n_exp preserves divergence *)
  Lemma R_n_exp_preserves_divergence n m e1 e2 :
    closed_exp e1 ->
    Pr_in_P_implies_u_bound Pr1 ->
    Pr_in_P_implies_u_bound Pr3 ->
    Pr_in_P_implies_u_bound Pr4 ->
    R_n_exp P1 P2 P3 Pr1 Pr2 Pr3 Pr4 n m e1 e2 ->
    diverge cenv (M.empty _) e1 -> 
    diverge cenv (M.empty _) e2.
  Proof.
    intros Hwfe Hp1 Hp2 Hp3 Hrel Hdiv. inv Hrel. destructAll. inv H0. destructAll. 
    eapply preord_exp_n_preserves_divergence; [| | eassumption | ].
    eapply Hp3. eassumption. eapply Hwf_c. eapply wf_pres_trans. eapply preord_exp_n_wf_pres. eapply H. eassumption.
    eassumption. 
    
    eapply cc_approx_exp_rreserves_divergence. eapply Hp2. eassumption.
    intros. eapply H6.
    eapply cc_approx_env_P_antimon; [| eapply Hwf_c; eauto ]. intros z Hin. now inv Hin.
    eapply preord_exp_n_wf_pres. eapply H.
    eapply preord_exp_n_preserves_divergence. eapply Hp1. eassumption. eassumption. eassumption. eassumption.
  Qed.

End RelComp.

Section Linking.
  
  Context (lft: fun_tag).
  Context (cenv : ctor_env) (ctag : ctor_tag).
    
  Definition link (x : var) (* the external reference that will be bound to e1 *)
             (e1 e2 : exp) : option exp :=
    match inline_letapp e1 x with
    | Some (C, x') =>
      let f := (max_var e1 (max_var e2 x') + 1)%positive in
      (* pick fresh name for function *) 
      Some (C |[ Efun (Fcons f lft [x] e1 Fnil) (Eapp f lft [x'])]|)
    | None => None
    end.


  Lemma inline_straight_code_l (e : exp) x :
    straight_code e = true ->
    exists C x', inline_letapp e x = Some (C, x').
  Proof.
    intros.
    induction e; simpl in *;
      try (eapply IHe in H; destructAll; do 2 eexists; rewrite H; reflexivity).
    - inv H.
    - do 2 eexists. reflexivity.
    - do 2 eexists. reflexivity.
  Qed.

  Lemma inline_straight_code_r (e : exp) x C x' :
    inline_letapp e x = Some (C, x') ->
    straight_code e = true.
  Proof.
    revert C x'.
    induction e; intros C x' Hin; simpl in *;
      try (match goal with
           | [ _ : context[inline_letapp ?E ?X] |- _ ] => 
             destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
           end); (try now inv Hin); try (now eauto).
  Qed.

  
  Lemma link_straight_code_r x (e1 e2 e : exp) :
    link x e1 e2 = Some e ->
    straight_code e1 = true.
  Proof.
    unfold link in *. intros H.
    match goal with
    | [ Hin : context[inline_letapp ?E ?X] |- _ ] => 
      destruct (inline_letapp E X) as [[C' w] | ] eqn:Hin'; inv Hin
    end. eapply inline_straight_code_r. eassumption.
  Qed.
  
  Lemma link_straight_code_l (e1 e2 : exp) x :
    straight_code e1 = true ->
    exists e, link x e1 e2 = Some e.
  Proof.
    intros. eapply inline_straight_code_l in H. destructAll.
    eexists. unfold link. rewrite H. reflexivity.
  Qed.


  Lemma link_src_closed x e1 e2 e :
    closed_exp e1 ->
    occurs_free e2 \subset [set x] ->
    link x e1 e2 = Some e ->
    closed_exp e.
  Proof.
    intros Hc1 Hc2 Hin. unfold link in *.    
    destruct (inline_letapp e1 x) as [[C z] | ] eqn:Hinl1; try congruence. inv Hin.
    split; [| now sets ].
    eapply Included_trans. eapply occurs_fee_inline_letapp; eauto.
    eapply Union_Included. now eapply Hc1. 
    unfold closed_exp in Hc1. repeat normalize_occurs_free.
    simpl in *. repeat normalize_sets.
    rewrite !Setminus_Union_distr in *. rewrite !Setminus_Same_set_Empty_set in *. repeat normalize_sets.
    eapply Union_Included.
    - rewrite Hc1. sets.
    - rewrite Setminus_Union. rewrite Union_commut. rewrite <- Setminus_Union.
      eapply Included_trans. eapply Setminus_Included.
      eapply inline_letapp_var_eq_alt in Hinl1. inv Hinl1.
      + inv H. intros z H. inv H. inv H0. contradiction.
      + inv H.
        * intros y H. inv H. inv H1. contradiction.
        * eapply Hc1 in H0. inv H0.
  Qed.
  
    
  Context (P : PostT) (PG : PostGT) (Hpr : Post_properties cenv P P PG)
          (Hinl : post_inline cenv P P P)
          (HinlOOT : post_inline_OOT P P)
          (HinclG : inclusion _ P PG) .

  
  Lemma preord_exp_preserves_linking_src x e1 e2 e1' e2' :
    
    (forall k rho1 rho2,
        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) ->
    
    (forall k rho1 rho2,
        preord_env_P cenv PG [set x] k rho1 rho2 ->                
        preord_exp cenv P PG k (e1', rho1) (e2', rho2)) ->
    
    closed_exp e1 ->
    
    match link x e1 e1', link x e2 e2' with
    | Some e, Some e' =>
      forall k rho1 rho2, preord_exp cenv P PG k (e, rho1) (e', rho2)
    | _ , _ => True
    end.
  Proof.
    intros Hexp1 Hexp2 (* Hc1 *) Hc1. inv Hpr.
    unfold link in *.
    
    destruct (inline_letapp e1 x) as [[C z] | ] eqn:Hinl1; eauto.
    destruct (inline_letapp e2 x) as [[C' z'] | ] eqn:Hinl2; eauto.
    
    intros k rho1 rho2.
    eapply inline_letapp_compat with (sig := id); [ | | | eapply Hc1 | eassumption | eassumption  | ].
    - eassumption.
    - eassumption.
    - intros. eapply Hexp1.
    - intros. eapply preord_exp_fun_compat.
      + eauto.
      + eauto.
      + eapply preord_exp_app_compat.
        * now eauto.
        * now eauto.
        * simpl. intros w Hget. rewrite M.gss in Hget. inv Hget. 
          eexists. rewrite M.gss. split. reflexivity. 
          rewrite preord_val_eq. intros vs1 vs2 j t xs1 eb rho1' Hlen Hdef Hset1.
          simpl in *. rewrite peq_true in Hdef. inv Hdef. simpl in Hset1. destruct vs1. congruence.
          destruct vs1; [| congruence ]. inv Hset1. destruct vs2. simpl in *. congruence.
          destruct vs2; [| simpl in *; congruence ].
          rewrite peq_true. do 3 eexists. split. reflexivity. split. reflexivity.
          intros. eapply (Hexp1 j) in H4; [| omega ]. destructAll. do 2 eexists. split. eassumption.
          split. eapply HinclG. eassumption. eassumption. 
        * assert (Hleq : (z' <= max_var e2 (max_var e2' z'))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }
          assert (Hleq' : (z <= max_var e1 (max_var e1' z))%positive).
          { eapply Pos.le_trans. eapply acc_leq_max_var. eapply acc_leq_max_var. }
          
          constructor; [| now constructor ].          
          simpl. intros w1 Hget.
          rewrite M.gso in Hget; auto. 
          rewrite M.gso; auto.
          eapply H0 in Hget; [| reflexivity ]. destructAll.
          rewrite functions.extend_gss in H1. 
          eexists. split; eauto. eapply preord_val_monotonic. eassumption. omega.
          
          intros Hc. rewrite Hc in Hleq at 1. zify; omega.
          intros Hc. rewrite Hc in Hleq' at 1. zify; omega.
  Qed.

  Context (wf_pres : exp -> exp -> Prop) (post_prop : post_property).
    


  Lemma preord_exp_n_1 P1 Pr e1 e2 :
    preord_exp_n cenv wf_pres Pr 1 P1 e1 e2 ->
    (forall k rho1 rho2,
        preord_env_P cenv P1 (occurs_free e1) k rho1 rho2 ->
        preord_exp cenv P1 P1 k (e1, rho1) (e2, rho2)).
  Proof.
    intros H. inv H. now eauto. intros. inv H2.
  Qed.

  (* Lemma preord_exp_n_wf_monotonic (wf1 wf2 : exp -> Prop) P1 Pr e1 e2 : *)
  (*   (forall e, wf1 e -> wf2 e) -> *)
  (*   preord_exp_n cenv wf1 Pr 1 P1 e1 e2 -> *)
  (*   preord_exp_n cenv wf2 Pr 1 P1 e1 e2. *)
  (* Proof. *)
  (*   intros. induction H0. *)
  (*   - constructor; eauto. *)
  (*   - econstructor; eauto. *)
  (* Qed. *)
  

End Linking.

Section LinkingComp.
      
  Context (P P1 P2 P3 : PostT)
          (Pr Pr1 Pr2 Pr3 Pr4 : post_property)
          (wf_pres : exp -> exp -> Prop)
          (wf1 wf2 : exp -> Prop)          
          (cenv : ctor_env) (lf : var).
  
  Context (Hwf : forall e e', wf_pres e e' -> preserves_fv e e')
          (Hwf' : forall e e', wf_pres e e' -> preserves_straight_code e e')
          (Hpr : forall P, Pr P -> Post_properties cenv P P P)
          (Hpr1 : forall P, Pr P -> post_inline cenv P P P)
          (Hpr2 : forall P, Pr P -> post_inline_OOT P P).

  Context (Hlinkwf :
             forall x e1 e2 e1' e2' e e',
               wf_pres e1 e2 -> wf_pres e1' e2' ->
               link lf x e1 e2 = Some e ->
               link lf x e1' e2' = Some e' ->
               wf_pres e e').
  
  
  Definition andp {A} (P1 P2 : A -> Prop) : A -> Prop := fun x => P1 x /\ P2 x.

  Lemma inclusion_refl {A} (Q : relation A) : inclusion _ Q Q.
  Proof. clear. now firstorder. Qed.

  Definition is_straightP := fun e => straight_code e = true.


  Definition preserves_closed (e1 e2 : exp) := closed_exp e1 -> closed_exp e2.

  Lemma preord_exp_n_preserves_linking_src_l x n e1 e2 e1' :
    preord_exp_n cenv (relation_conjunction preserves_closed preserves_straight_code) Pr n P e1 e2 ->
    
    closed_exp e1 ->
    straight_code e1 = true ->
    occurs_free e1' \subset [set x] ->
    
    match link lf x e1 e1', link lf x e2 e1' with
    | Some e, Some e' =>
      preord_exp_n cenv preserves_closed Pr n P e e'
    | _ , _ => True
    end.
  Proof.
    intros Hrel. revert e1'. induction Hrel; intros e1' Hw1 Hw2 Hfv.
    - assert (Hexp2 :
                forall k rho1 rho2,
                  preord_env_P cenv P [set x] k rho1 rho2 ->
                  preord_exp cenv P P k (e1', rho1) (e1', rho2)).
      { intros. eapply preord_exp_refl. eapply Hpr. eassumption.
        intros z Hin. eapply Hfv in Hin . eauto. } 
      assert (Hexp1 :
                forall (k : nat) (rho1 rho2 : env),
                  preord_exp' cenv (preord_val cenv) P P k (c1, rho1) (c2, rho2)).
      { intros. eapply H. intros z Hin. eapply Hw1 in Hin; eauto. inv Hin. }
      

      specialize (preord_exp_preserves_linking_src
                    lf cenv P P (Hpr _ H1) (Hpr1 _ H1) (Hpr2 _ H1) (inclusion_refl _) _ _ _ _ _ Hexp1 Hexp2 Hw1).
      intros Hc. destruct (link lf x c1 e1') eqn:Hl1; eauto. destruct (link lf x c2 e1') eqn:Hl2; eauto.
      constructor. 
      * intros. eapply Hc.
      * intros Hc1. eapply link_src_closed; [| | eassumption ]. eapply H0. eassumption. eassumption.
      * eassumption.
    - assert (Hc' : closed_exp c'). { eapply H0. eassumption. }
      assert (Hs' : straight_code c' = true). { eapply H0; eauto. }
      specialize (IHHrel e1' Hc' Hs' Hfv).
                                              
      destruct (link lf x c1 e1') eqn:Hl1; eauto. 
      destruct (link lf x c2 e1') eqn:Hl2; eauto.
      edestruct (link_straight_code_l lf c' e1'). eassumption. rewrite H3 in IHHrel.  
      
      assert (Hexp1 :
                  forall (k : nat) (rho1 rho2 : env),
                    preord_exp' cenv (preord_val cenv) P0 P0 k (c1, rho1) (c', rho2)).
      { intros. eapply H. intros z Hin. eapply Hw1 in Hin; eauto. inv Hin. } 
      assert (Hexp2 :
                forall k rho1 rho2,
                  preord_env_P cenv P0 [set x] k rho1 rho2 ->
                  preord_exp cenv P0 P0 k (e1', rho1) (e1', rho2)).
      { intros. eapply preord_exp_refl. eapply Hpr. eassumption.
        intros z Hin. eapply Hfv in Hin . eauto. }

      econstructor; [| | | eassumption | eassumption ].
      + specialize (preord_exp_preserves_linking_src
                      lf cenv P0 P0 (Hpr _ H1) (Hpr1 _ H1) (Hpr2 _ H1) (inclusion_refl _) _ _ _ _ _ Hexp1 Hexp2 Hw1).
        intros Hc. rewrite Hl1, H3 in Hc.
        intros. eapply Hc.
      + eapply IHHrel; eauto.
      + intros Hc1. eapply link_src_closed; [| | eassumption ]. eapply H0. eassumption. eassumption.
  Qed.    

  Lemma preord_exp_n_preserves_linking_src n m e1 e2 e1' e2' Pr :
    
    (forall rho1 rho2,
        preord_exp_n cenv closed_conf Pr n P1 PG1 (e1, rho1) (e2, rho2)) ->
    
    (forall rho1 rho2,
        preord_exp_n cenv closed_conf Pr m P2 PG2 (e1', rho1) (e2', rho2)) ->
    
    closed_exp e1 ->
    closed_exp e1' ->
    
    match link_src e1 e1', link_src e2 e2' with
    | Some e, Some e' =>
      preord_exp_n cenv closed_conf Pr (n + m) (comp P1 P2) (comp PG1 PG2) (e, M.empty _) (e', M.empty _)
    | _ , _ => True
    end.
  Proof.
    revert m e1 e2 e1' e2' Pr. induction n; induction m; intros e1 e2 e1' e2' Pr. 
    + intros Hexp1 Hexp2 Hc1 Hc2.
      assert (He1 : forall k rho1 rho2, preord_exp cenv P1 PG1 k (e1, rho1) (e2, rho2)).
      { intros. eapply preord_exp_n_0_env. eauto. }
      assert (He2 : forall k rho1 rho2, preord_exp cenv P2 PG2 k (e1', rho1) (e2', rho2)).
      { intros. eapply preord_exp_n_0_env. eauto. }
      assert (Hlink := preord_exp_preserves_linking_src e1 e2 e1' e2' He1 He2).
      
      unfold link_src.
      
    destruct e1'; eauto. destruct f; eauto. destruct l; eauto. destruct l; eauto.
    destruct f0; eauto.  destruct e1'; eauto.
    destruct ((v =? v1)%positive && (f =? lft)%positive) eqn:Hfeq; eauto.
    destruct (inline_letapp e1 v0) as [[C z] | ] eqn:Hinl1; eauto.
    destruct ((z =? v1)%positive) eqn:Hs; eauto.      
    
    destruct e2'; eauto. destruct f0; eauto. destruct l; eauto. destruct l; eauto.
    destruct f1; eauto.  destruct e2'; eauto.
    destruct ((v2 =? v4)%positive && (f0 =? lft)%positive) eqn:Hfeq'; eauto.
    destruct (inline_letapp e2 v3) as [[C' z'] | ] eqn:Hinl2; eauto.
    destruct ((z' =? v4)%positive) eqn:Hs'; eauto.
    
    eapply andb_prop in Hfeq. eapply andb_prop in Hfeq'. destructAll. 
    eapply Peqb_true_eq in H1. eapply Peqb_true_eq in H2.
    eapply Peqb_true_eq in H. eapply Peqb_true_eq in H0. subst.
    eapply Pos.eqb_neq in Hs. eapply Pos.eqb_neq in Hs'.
    
    revert e1 e2 e1' e2' Pr
    eapply inline_letapp_compat with (sig := id); [ | | | eapply Hc1 | eassumption | eassumption  | | ].
    - eassumption.
    - eassumption.
    - intros. eapply Hexp1. eapply preord_env_P_antimon; [| eapply Hc1 ].
      intros x Hin. inv Hin.
    - intros. eapply preord_exp_fun_compat.
      + eassumption.
      + eassumption.
      + assert (Hvalrel :
                  forall k,
                    preord_env_P cenv PG (Empty_set _) k rho1 rho2 ->
                    preord_val cenv PG k (Vfun rho1 (Fcons v1 lft [v0] e Fnil) v1) (Vfun rho2 (Fcons v4 lft [v3] e0 Fnil) v4)).
        { intros j. edestruct (Hexp2 (j + 2) rho1 rho2) with (cin:= 2).
          
          eapply preord_env_P_antimon; [| eapply Hc2 ].
            intros x Hin. now inv Hin.      
            
            omega.
            
            econstructor 2. simpl. omega.
            simpl. econstructor. simpl. econstructor 2. simpl. omega.  econstructor.
            rewrite M.gss. reflexivity.
            destructAll. inv H1. contradiction. inv H5. inv H10. contradiction. inv H5.
            simpl in H10. rewrite M.gss in H10. inv H10.
            simpl in H3. 
            simpl. intros Henv. eapply preord_val_monotonic. 
            eassumption. omega. }
          
          simpl. eapply preord_exp_app_compat.
        * eassumption.
        * eassumption.
        * simpl. intros w Hget. rewrite M.gss in Hget. inv Hget. 
          eexists. rewrite M.gss. split. reflexivity. eapply Hvalrel.
          intros x Hin. inv Hin.
        * constructor; [| now constructor ].
          
          simpl. intros w1 Hget.
          rewrite M.gso in Hget; auto. 
          rewrite M.gso; auto.
          eapply H0 in Hget; [| reflexivity ]. destructAll.
          rewrite functions.extend_gss in H1. 
          eexists. split; eauto. eapply preord_val_monotonic. eassumption. omega. 
    - intros x Hin v Hget. rewrite M.gempty in Hget. inv Hget.
  Qed.        

  Lemma preord_exp_n_preserves_linking_src k e1 e2 e1' e2' :
    
    (forall k rho1 rho2,
        preord_exp_n cenv P PG k (e1, rho1) (e2, rho2)) ->
    
    (forall k rho1 rho2,
        preord_exp cenv P PG k (e1', rho1) (e2', rho2)) ->
    
    closed_exp e1 ->
    closed_exp e1' ->
    
    match link_src e1 e1', link_src e2 e2' with
    | Some e, Some e' =>
      preord_exp cenv P PG k (e, M.empty _) (e', M.empty _)
    | _ , _ => True
    end.
  Proof.
    intros Hexp1 Hexp2 Hc1 Hc2. unfold link_src.
    
    destruct e1'; eauto. destruct f; eauto. destruct l; eauto. destruct l; eauto.
    destruct f0; eauto.  destruct e1'; eauto.
    destruct ((v =? v1)%positive && (f =? lft)%positive) eqn:Hfeq; eauto.
    destruct (inline_letapp e1 v0) as [[C z] | ] eqn:Hinl1; eauto.
    destruct ((z =? v1)%positive) eqn:Hs; eauto.      
    
    destruct e2'; eauto. destruct f0; eauto. destruct l; eauto. destruct l; eauto.
    destruct f1; eauto.  destruct e2'; eauto.
    destruct ((v2 =? v4)%positive && (f0 =? lft)%positive) eqn:Hfeq'; eauto.
    destruct (inline_letapp e2 v3) as [[C' z'] | ] eqn:Hinl2; eauto.
    destruct ((z' =? v4)%positive) eqn:Hs'; eauto.
    
    eapply andb_prop in Hfeq. eapply andb_prop in Hfeq'. destructAll. 
    eapply Peqb_true_eq in H1. eapply Peqb_true_eq in H2.
    eapply Peqb_true_eq in H. eapply Peqb_true_eq in H0. subst.
    eapply Pos.eqb_neq in Hs. eapply Pos.eqb_neq in Hs'.
    
    eapply inline_letapp_compat with (sig := id); [ | | | eapply Hc1 | eassumption | eassumption  | | ].
    - eassumption.
    - eassumption.
    - intros. eapply Hexp1.
    - intros. eapply preord_exp_fun_compat.
      + now eauto.
      + now eauto.
      + assert (Hvalrel :
                  forall k,
                    preord_env_P cenv PG (Empty_set _) k rho1 rho2 ->
                    preord_val cenv PG k (Vfun rho1 (Fcons v1 lft [v0] e Fnil) v1) (Vfun rho2 (Fcons v4 lft [v3] e0 Fnil) v4)).
        { intros j. edestruct (Hexp2 (j + 2) rho1 rho2) with (cin:= 2).
          
          omega.
          
          econstructor 2. simpl. omega.
          simpl. econstructor. simpl. econstructor 2. simpl. omega.  econstructor.
          rewrite M.gss. reflexivity.
          destructAll. inv H1. contradiction. inv H5. inv H10. contradiction. inv H5.
          simpl in H10. rewrite M.gss in H10. inv H10.
          simpl in H3. 
          simpl. intros Henv. eapply preord_val_monotonic. 
          eassumption. omega. }
        
          simpl. eapply preord_exp_app_compat.
        * now eauto.
        * now eauto.
        * simpl. intros w Hget. rewrite M.gss in Hget. inv Hget. 
          eexists. rewrite M.gss. split. reflexivity. eapply Hvalrel.
          intros x Hin. inv Hin.
        * constructor; [| now constructor ].
          
          simpl. intros w1 Hget.
          rewrite M.gso in Hget; auto. 
          rewrite M.gso; auto.
          eapply H0 in Hget; [| reflexivity ]. destructAll.
          rewrite functions.extend_gss in H1. 
          eexists. split; eauto. eapply preord_val_monotonic. eassumption. omega. 
    - intros x Hin v Hget. rewrite M.gempty in Hget. inv Hget.
  Qed.


    Definition Post_id : PostT := fun c1 c2 => c1 = c2.

    Lemma preord_exp_refl k e rho rho' :
    preord_env_P cenv Post_id (occurs_free e) k rho rho' ->
    preord_exp cenv Post_id Post_id k (e, rho) (e, rho').
  Proof with eauto with Ensembles_DB.
    revert e rho rho'.
    (* Well founded induction on the step-index *)
    induction k as [ k IH ] using lt_wf_rec1.
    (* Induction on e *) 
    intros e. revert k IH.
    induction e using exp_ind'; intros k IH rho rho' Henv. 
    (* Each case follows from the corresponding compat lemma *)
    - eapply preord_exp_constr_compat with (P1 := Post_id); eauto; intros.
      * clear. intro; intros. intro; intros. unfold Post_id in *.
        inv H1. firstorder. eapply Forall2_same. intros x HIn. apply Henv. now constructor.
      * eapply IHe. intros. eapply IH; eauto. omega.
        eapply preord_env_P_extend.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
        omega.
        now (normalize_occurs_free; eauto with Ensembles_DB). 
        rewrite preord_val_eq. constructor; eauto using Forall2_Forall2_asym_included.
    - eapply preord_exp_case_nil_compat. eassumption.
    - eapply preord_exp_case_cons_compat; eauto.
      now apply Forall2_refl.
      intros m Hlt. apply IHe; try eassumption.
      intros. eapply IH; eauto. omega.
      eapply preord_env_P_antimon. 
      eapply preord_env_P_monotonic; [| eassumption ]. omega.
      normalize_occurs_free. sets.
      eapply IHe0; eauto.
      eapply preord_env_P_antimon. 
      eapply preord_env_P_monotonic; [| eassumption ]. omega.
      normalize_occurs_free. sets.
    - eapply preord_exp_proj_compat; eauto.
      intros m v1 v2 Hlt Hval. apply IHe; try eassumption.
      intros. eapply IH; eauto. omega.
      eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. omega.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_letapp_compat; eauto.
      eapply Henv. constructor. now left.
      eapply Forall2_same. intros. apply Henv. constructor. now right.
      intros m v1 v2 Hlt Hval. 
      eapply IHe; try eassumption.
      intros. eapply IH; eauto. omega.
      eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. omega.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_fun_compat; eauto.
      eapply IHe; try eassumption. 
      intros. eapply IH; eauto. omega. 
      eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre; eauto.
      intros. eapply IH; eauto. omega. 
      eapply preord_env_P_monotonic; [| eassumption ]. omega.
      now eapply occurs_free_Efun_Included.
    - eapply preord_exp_app_compat. eassumption. eassumption.
      intros x HP. apply Henv; eauto.
      apply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_halt_compat; try eassumption.
      intros x HP. apply Henv; eauto.
   Qed.

    Instance Post_properties_post_id : Post_properties Post_id Post_id.
    Proof.
      constructor.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. inv H1.
        reflexivity. 
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. inv H1.
        reflexivity. 
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst.
        reflexivity.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst.
        reflexivity. 
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst.
        reflexivity.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. inv H1.
        reflexivity. 
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst. reflexivity.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst. reflexivity.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst. reflexivity.
      - intro; intros. intro; intros. unfold Post_id in *. simpl in *. subst. reflexivity.
      - firstorder.
    Qed. 
    
    Context (P1 P2 : PostT) (PG1 PG2 : PostGT).


  Definition closed_conf (c : exp * env) := closed_exp (fst c).


      
  Context (HPost_con : post_constr_compat P1 P1)
          (HPost_proj : post_proj_compat P1 P1)
          (HPost_fun : post_fun_compat P1 P1)
          (HPost_case_hd : post_case_compat_hd P1 P1)
          (HPost_case_tl : post_case_compat_tl P1 P1)
          (HPost_app : post_app_compat P1 PG1)
          (HPost_letapp : post_letapp_compat cenv P1 P1 PG1)
          (HPost_letapp_OOT : post_letapp_compat_OOT P1 PG1)
          (HPost_OOT : post_OOT P1)
          (Hpost_base : post_base P1)
          (HGPost : inclusion _ P1 PG1)
          (HPost_conG : post_constr_compat PG1 PG1)
          (HPost_projG : post_proj_compat PG1 PG1)
          (HPost_funG : post_fun_compat PG1 PG1)
          (HPost_case_hdG : post_case_compat_hd PG1 PG1)
          (HPost_case_tlG : post_case_compat_tl PG1 PG1)
          (HPost_appG : post_app_compat PG1 PG1)
          (HPost_letappG : post_letapp_compat cenv PG1 PG1 PG1)
          (HPost_letapp_OOTG : post_letapp_compat_OOT PG1 PG1)
          (HPost_OOTG : post_OOT PG1)
          (Hpost_baseG : post_base PG1).
  
    
  
  Lemma preord_exp_n_refl n Pr e1 rho1 :
    preord_exp_n cenv closed_conf Pr n P1 PG1 (e1, rho1) (e1, rho1).
  Proof.
    induction n.
    - constructor; [| clear; firstorder ].
      intros k. eapply preord_exp_refl; eauto. 
      eapply preord_env_P_refl; eauto.
    - econstructor.       
      2:{ eapply 
      + intros 
      intros H. inv H. eauto.
  Qed.

  Lemma preord_exp_n_m n m Pr e1 rho1 e2 rho2 :
    preord_exp_n cenv closed_conf Pr n P1 PG1 (e1, rho1) (e2, rho2) ->
    n <= m ->
    preord_exp_n cenv closed_conf Pr m P1 PG1 (e1, rho1) (e2, rho2).
  Proof.
    revert n Pr e1 rho1 e2 rho2. induction m using lt_wf_rec1; intros n Pr e1 rho1 e2 rho2 Hexp Hlt.
    destruct m. 
    - destruct n. eassumption. omega.
    - econstructor. intros k. eapply preord_exp_refl. 
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      eapply preord_env_P_refl.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      eapply H. omega. eassumption. omega. admit.
      
      admit.
      
    intros H. inv H. eauto.
  Qed.



  End Linking.

End RelComp.
