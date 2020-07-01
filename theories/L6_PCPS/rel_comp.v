
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
  
  Definition post_property := A -> A -> PostT -> PostGT -> Prop.
  
  Context (well_formed : A -> Prop)
          (post_prop : post_property).
  
  
  Definition wf_pres (e1 e2 : A) := well_formed e1 -> well_formed e2. 
  
  Definition rel := PostT -> PostGT -> A -> A -> Prop.
  
  Inductive R_n (R : PostT -> PostGT -> A -> A -> Prop) : nat -> PostT -> PostGT -> A -> A -> Prop :=
  | One :
      forall (P : PostT) (PG : PostGT) (c1 : A) (c2: A),
        R P PG c1 c2 ->
        wf_pres c1 c2 ->        
        R_n R 0%nat P PG c1 c2
  | More :
      forall (n : nat) (P : PostT) (PG : PostGT) (c1 : A) (c2: A) P1 P2 PG1 PG2 c',
        R P1 PG1 c1 c' ->
        R_n R n P2 PG2 c' c2 ->
        wf_pres c1 c2 ->
        post_prop c1 c2 P PG ->
        same_relation _ (compose P1 P2) P ->
        same_relation _ (compose PG1 PG2) PG ->
        R_n R (S n) P PG c1 c2.

End Compose.

Definition pr_trivial {A} : @post_property A := fun _ _ _ _ => True.

Definition wf_trivial {A} : A -> Prop := fun _ => True.


Section RelComp.

  Context (cenv : ctor_env) (ctag : ctor_tag).

  Context (wf_exp : exp * env -> Prop) (post_prop : @post_property (exp * env)).
   
  Definition preord_exp_n n := R_n wf_exp post_prop (fun P PG c1 c2 => forall k, preord_exp cenv P PG k c1 c2) n.  

  Definition preord_env_n n S := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_env_P cenv P S k c1 c2) n.  

  Definition preord_val_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_val cenv PG k c1 c2) n.

  Definition preord_res_n n := R_n wf_trivial pr_trivial (fun P PG c1 c2 => forall k, preord_res (preord_val cenv) PG k c1 c2) n.

  Definition R_true : PostT := fun _ _ => True. 

  Lemma R_true_idempotent :
    same_relation _ (compose R_true R_true) R_true.
  Proof.
    firstorder.
  Qed.

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
      * destruct x; eauto. destruct x1. contradiction.
        eapply bstep_fuel_deterministic in H2; [| clear H2; eassumption ].
        inv H2. eapply preord_res_monotonic. eassumption. omega.
      * clear. firstorder.
    + destruct c1 as [e1 rho1]; destruct c2 as [e2 rho2]; destruct c' as [e' rho'].
      intros. edestruct H; eauto. destructAll.
      edestruct IHHrel. eassumption. destructAll. 
      do 2 eexists. split; eauto. split.
      eapply H2. do 2 eexists. eassumption. eassumption. 
      eapply More; [| eassumption | | | eapply R_true_idempotent | eassumption ].
      destruct v1.
      * destruct x; eauto.
      * destruct x; eauto. destruct x1. eapply preord_res_n_OOT_r in H10. contradiction.
        intros k.
        edestruct (H (k + cin)); [| eassumption | ]. omega. destructAll. destruct x; eauto. simpl in H11. contradiction. 
        eapply bstep_fuel_deterministic in H5; [| clear H5; eassumption ]. destructAll.
        eapply preord_res_monotonic. eassumption. omega.
      * clear. firstorder.
      * clear. firstorder.        
  Qed.
  

  Definition P_implies_u_bound K M (p1 p2 : exp * env) (P : PostT) :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall c1 c2,
      P (e1, rho1, c1) (e2, rho2, c2) ->
      c1 <= (M + 1) * c2 + K.
    
  (* preord_exp_n preserves divergence *)
  Lemma preord_exp_n_preserves_divergence n K M P PG e1 rho1 e2 rho2 :
    (P_implies_u_bound K M) (e1, rho1) (e2, rho2) P ->
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
  

  Definition compose_rel {A} (P1 P2 : PostT) (PG1 PG2 : PostGT)
             (Pr1 Pr2 : post_property) (wf : A -> Prop)
             (R1 R2 : rel) (c1 : A) (c2: A) : Prop :=
    exists c',
      R1 P1 PG1 c1 c' /\
      R2 P2 PG2 c' c2 /\
      Pr1 c1 c' P1 PG1 /\ Pr2 c' c2 P2 PG2 /\
      wf_pres wf c1 c'.

  
  (* Top-level relation for L6 pipeline *)
  Definition R_n_exp P1 P2 P3 PG1 PG2 PG3 Pr1 Pr2 Pr3 Pr4 wf n m : relation (exp * env) :=
    compose_rel P1 P2 PG1 PG2 Pr1 Pr2 wf
                (preord_exp_n n)
                (fun P2 PG2 => compose_rel P2 P3 PG2 PG3 Pr3 Pr4 wf
                                           (fun P PG c1 c2 => forall k, cc_approx_exp cenv ctag k P PG c1 c2) (preord_exp_n m)).

  Definition post_trivial : PostT := fun c1 c2 => True.
  
  Definition R_n_res PG1 PG2 PG3 n m : relation res :=
    compose_rel post_trivial post_trivial PG1 PG2 pr_trivial pr_trivial wf_trivial (preord_res_n n)
                (fun P2 PG2 => compose_rel P2 post_trivial PG2 PG3 pr_trivial pr_trivial wf_trivial
                             (fun P PG c1 c2 => forall k, cc_approx_res (cc_approx_val cenv ctag) k PG c1 c2) (preord_res_n m)).
  
  Definition R_n_val PG1 PG2 PG3 n m : relation val :=
    compose_rel post_trivial post_trivial PG1 PG2 pr_trivial pr_trivial wf_trivial (preord_val_n n)
                (fun P2 PG2 => compose_rel P2 post_trivial PG2 PG3 pr_trivial pr_trivial wf_trivial
                                           (fun P PG c1 c2 => forall k, cc_approx_val cenv ctag k PG c1 c2) (preord_val_n m)).
  

  Definition Pr_in_P_implies_u_bound K M (Pr1 : @post_property (exp * env)) :=
    forall p1 p2 P PG,
      Pr1 p1 p2 P PG -> P_implies_u_bound K M p1 p2 P. 
  
  Lemma R_n_exp_impl K M P1 P2 P3 PG1 PG2 PG3 Pr1 Pr2 Pr3 Pr4 wf (n m : nat) e1 rho1 e2 rho2 :
    Pr_in_P_implies_u_bound K M Pr1 ->
    R_n_exp P1 P2 P3 PG1 PG2 PG3 Pr1 Pr2 Pr3 Pr4 wf n m (e1, rho1) (e2, rho2) ->    
    (forall (v1 : res) (cin : nat),
        bstep_fuel cenv rho1 e1 v1 cin ->
        not_stuck cenv rho1 e1 ->
        exists (v2 : res) (cin' : nat),
          bstep_fuel cenv rho2 e2 v2 cin' /\
          (comp P1 (comp P2 P3)) (e1, rho1, cin) (e2, rho2, cin') /\
          R_n_res PG1 PG2 PG3 n m v1 v2).
  Proof.
    intros Himpl Hrel. inv Hrel. destructAll. inv H0. destructAll. 
    assert (Hexp1 := H). assert (Hexp2 := H4).
    eapply preord_exp_n_impl in H.  
    eapply preord_exp_n_impl in H4.
    destruct x, x0. intros. edestruct H. eassumption. destructAll.    
    edestruct (H0 x0); eauto.
    
    eapply preord_exp_n_preserves_not_stuck. eapply Himpl. eassumption. eassumption. eassumption.
    
    destructAll. edestruct H4. eassumption. destructAll.
    
    do 2 eexists. split; eauto. split; eauto.

    eexists. split. eassumption. eexists. split; eassumption.

    eexists. split. eassumption. split.
    2:{ split. clear. now firstorder. split. now firstorder. now firstorder. }
    eexists. split.
    2:{ split. eassumption. split. now firstorder. now firstorder. }
    
    intros k. 
    destruct v1.
    - destruct x.
      * destruct x1; eauto. 
      * eapply preord_res_n_OOT_l in H12. contradiction.
    - destruct x.
      + eapply preord_res_n_OOT_r in H12. contradiction.
      + destruct x1; eauto.
        edestruct (H0 (k + x0)); [| eassumption | | ]. omega.
        eapply preord_exp_n_preserves_not_stuck. eapply Himpl. eassumption. eassumption. eassumption.
        
        destructAll.
        destruct x. contradiction.
        eapply bstep_fuel_deterministic in H19; [| clear H19; eassumption ]. inv H19.
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
  Lemma R_n_exp_preserves_divergence n m K1 M1 K2 M2 K3 M3 P1 P2 P3 PG1 PG2 PG3 Pr1 Pr2 Pr3 Pr4 wf e1 rho1 e2 rho2 :
    Pr_in_P_implies_u_bound K1 M1 Pr1 ->
    Pr_in_P_implies_u_bound K2 M2 Pr3 ->
    Pr_in_P_implies_u_bound K3 M3 Pr4 ->
    R_n_exp P1 P2 P3 PG1 PG2 PG3 Pr1 Pr2 Pr3 Pr4 n m wf (e1, rho1) (e2, rho2) ->
    diverge cenv rho1 e1 -> 
    diverge cenv rho2 e2.
  Proof.
    intros Hp1 Hp2 Hp3 Hrel Hdiv. inv Hrel. destructAll. destruct x. inv H0. destructAll. destruct x. 
    eapply preord_exp_n_preserves_divergence; [| eassumption | ];
      [| eapply cc_approx_exp_rreserves_divergence; [ | eassumption | ];
         [| eapply preord_exp_n_preserves_divergence; [| eassumption | eassumption ] ]].
    eapply Hp3. eassumption. eapply Hp2. eassumption. eapply Hp1. eassumption.
  Qed.

End RelComp.

Section Linking.
  
  Context (lft: fun_tag).
  Context (cenv : ctor_env) (ctag : ctor_tag).
    
  Definition link_src (e1 e2 : exp) : option exp :=
    match e2 with
    | Efun (Fcons f ft [x] e Fnil) (Ehalt f') =>
      if (f =? f')%positive && (ft =? lft)%positive  then  
        match inline_letapp e1 x with
        | Some (C, x') =>
          if (x' =? f')%positive then None (* shadowing happens *)                                          
          else Some (C |[ Efun (Fcons f lft [x] e Fnil) (Eapp f lft [x'])]|)
        | None => None
        end
      else None
    | _ => None
    end.

  Definition link_trg (e1 e2 : exp) : option exp :=
    match e2 with
    | Efun (Fcons f ft [x] e Fnil) (Ehalt f') =>
      if (f =? f')%positive && (ft =? lft)%positive then  
        match inline_letapp e1 x with
        | Some (C, x') =>
          if (x' =? f')%positive then None (* shadowing happens *)
          else
            let fv := max_var e1 f in
            let f' := (fv + 1)%positive in
            let Γ := (fv + 2)%positive in
            Some (C |[ Efun (Fcons f lft [x] e Fnil) (AppClo ctag f f' Γ |[ Eapp f lft [Γ; x] ]|) ]|)
        | None => None
        end
      else None
    | _ => None
    end.


  Definition rel_union {A} (P1 P2 : relation A) :=
    fun c1 c2 => P1 c1 c2 \/ P2 c1 c2.
  
  Definition id_rel {A} : relation A := fun x y => x = y.

  
  Lemma id_rel_neut_l {A} P :
    same_relation A (compose P id_rel) P.
  Proof.
    split; intro; intros.
    + unfold compose, id_rel in H. destructAll. eassumption.
    + unfold compose, id_rel. eexists; split; eauto.
  Qed.

  Lemma id_rel_neut_r {A} P :
    same_relation A (compose id_rel P) P.
  Proof.
    split; intro; intros.
    + unfold compose, id_rel in H. destructAll. eassumption.
    + unfold compose, id_rel. eexists; split; eauto.
  Qed.

    
  Context (P : PostT) (PG : PostGT)
          (Hinl : post_inline cenv P P P)
          (HinlOOT : post_inline_OOT P P)
          (Hpost : post_fun_compat P P)
          (HpostOOT : post_OOT P)
          (Hpostapp: post_app_compat P PG).

  
  Lemma preord_exp_preserves_linking_src k e1 e2 e1' e2' :
    
    (forall k rho1 rho2,
        preord_exp cenv P PG k (e1, rho1) (e2, rho2)) ->
    
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
      + eassumption.
      + eassumption.
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


    Class Post_properties (P1 : PostT) (PG : PostGT) : Prop :=
    { HPost_con : post_constr_compat P1 P1;
      HPost_proj : post_proj_compat P1 P1;
      HPost_fun : post_fun_compat P1 P1;
      HPost_case_hd : post_case_compat_hd P1 P1;
      HPost_case_tl : post_case_compat_tl P1 P1;
      HPost_app : post_app_compat P1 PG;
      HPost_letapp : post_letapp_compat cenv P1 P1 PG;
      HPost_letapp_OOT : post_letapp_compat_OOT P1 PG;
      HPost_OOT : post_OOT P1;
      Hpost_base : post_base P1;
      HGPost : inclusion _ P1 PG }.

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


  Lemma preord_exp_n_0 k Pr e1 rho1 e2 rho2 :
    preord_exp_n cenv closed_conf Pr 0 P1 PG1 (e1, rho1) (e2, rho2) ->
    preord_exp cenv P1 PG1 k (e1, rho1) (e2, rho2).
  Proof.
    intros H. inv H. eauto.
  Qed.

      
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

  Lemma preord_exp_n_preserves_linking_src n e1 e2 e1' e2' Pr :
    
    (forall rho1 rho2,
        preord_exp_n cenv closed_conf Pr n P1 PG1 (e1, rho1) (e2, rho2)) ->
    
    (forall rho1 rho2,
        preord_exp_n cenv closed_conf Pr n P2 PG2 (e1', rho1) (e2', rho2)) ->
    
    closed_exp e1 ->
    closed_exp e1' ->
    
    match link_src e1 e1', link_src e2 e2' with
    | Some e, Some e' =>
      preord_exp_n cenv closed_conf Pr n (comp P1 P2) (comp PG1 PG2) (e, M.empty _) (e', M.empty _)
    | _ , _ => True
    end.
  Proof.
    revert e1 e2 e1' e2' Pr. induction n; intros e1 e2 e1' e2' Pr.
    + intros Hexp1 Hexp2 Hc1 Hc2. unfold link_src.
    
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


  End Linking.

End RelComp.
