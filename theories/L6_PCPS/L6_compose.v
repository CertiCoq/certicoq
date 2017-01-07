(* Composition of L6 transformations and correctness. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.cps L6.ctx L6.cps_util L6.List_util L6.eval L6.identifiers
        L6.functions L6.hoare L6.Ensembles_util L6.closure_conversion
        L6.closure_conversion_correct L6.closure_conversion_corresp L6.hoisting
        L6.logical_relations.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.


Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.

(** * Composition of L6 transformations and their correctness proofs *)

Section L6_trans.
   
    Variable (clo_tag : cTag).
    Variable (pr : prims).
    Variable (cenv : cEnv).

    (** Observation relation for phases other than closure conversion *)
    Inductive obs_rel : val -> val -> Prop :=
    | Obs_constr :
        forall ct vs1 vs2,
          (* This can be potentially changed to [Forall2]. The reason for using
             [Forall2_asym] is for the logical relation to be complete w.r.t. to
             contextual equivalence but this is something we don't necessarily need  *)
          Forall2_asym obs_rel vs1 vs2 ->
          obs_rel (Vconstr ct vs1) (Vconstr ct vs2)
    | Obs_fun :
        forall rho1 B1 f1 rho2 B2 f2,
          obs_rel (Vfun rho1 B1 f1) (Vfun rho2 B2 f2)
    | Obs_int :
        forall z, obs_rel (Vint z) (Vint z).
    
    (** Observation relation for closure conversion *)
    Inductive obs_rel_cc : val -> val -> Prop :=
    | Obscc_constr :
        forall ct vs1 vs2,
          Forall2_asym obs_rel_cc vs1 vs2 ->
          obs_rel_cc (Vconstr ct vs1) (Vconstr ct vs2)
    | Obscc_fun :
        forall rho1 B1 f1 rho2 B2 f2 c1 c2 vs l,
          (* This can be potentially changed to [Vconstr c1 [(Vfun rho2 B2 f2) ; (Vconstr c2 vs)]].
             The only reason it's not written this way is the use of [Forall2_asym]
             above *)
          obs_rel_cc (Vfun rho1 B1 f1)
                     (Vconstr c1 ((Vfun rho2 B2 f2) :: (Vconstr c2 vs) :: l))
    | Obscc_int :
        forall z, obs_rel_cc (Vint z) (Vint z).
    

    (** [obs_rel] is reflexive *)
    Global Instance Reflexive_obs_rel : Reflexive obs_rel.
    Proof. 
      intros x; induction x using val_ind'; constructor; eauto.
      constructor; eauto. now inv IHx0.
    Qed.

    (** [obs_rel] is transitive *)
    Global Instance Transitive_obs_rel : Transitive obs_rel.
    Proof. 
      intros x y. revert x. induction y using val_ind'; intros x w H1 H2.
      + inv H1. inv H2. inv H3. inv H4.  constructor; eauto.
      + inv H1. inv H2. inv H3.
        * constructor; eauto.
        * inv H4. constructor; eauto.
          constructor; eauto.
          assert (H : obs_rel (Vconstr t l0) (Vconstr t l')).
          { eapply IHy0; constructor; eauto. }
          inv H; eauto.
      + inv H1. inv H2. constructor.
      + inv H1. inv H2. constructor.
    Qed.
    
    (** [obs_rel_cc] respects [obs_rel]. Required to compose closure conversion with phases before and after *)

    Lemma obs_rel_cc_respects_obs_rel_l (v1 v2 v3 : val) :
      obs_rel v1 v2 -> obs_rel_cc v2 v3 -> obs_rel_cc v1 v3.
    Proof.
      revert v1 v3; induction v2 using val_ind'; intros v1 v3 H1 H2.
      - inv H1; inv H2. inv H3; inv H4. constructor. constructor.
      - inv H1; inv H2. inv H3; inv H4.
        + constructor. constructor; eauto.
        + constructor. constructor; eauto.
          assert (H : obs_rel_cc (Vconstr t l0) (Vconstr t l')).
          { eapply IHv0; constructor; eauto. }
        inv H; eauto.
      - inv H1. inv H2. constructor.
      - inv H1. inv H2. constructor.
    Qed.


    Lemma obs_rel_cc_respects_obs_rel_r (v1 v2 v3 : val) :
      obs_rel_cc v1 v2 -> obs_rel v2 v3 -> obs_rel_cc v1 v3.
    Proof.
      revert v1 v3; induction v2 using val_ind'; intros v1 v3 H1 H2.
      - inv H1; inv H2. inv H3; inv H4. constructor. constructor.
      - inversion H1.
        + subst. inv H2. inv H3; inv H5.
          * constructor. constructor; eauto.
          * constructor. constructor; eauto.
            assert (H : obs_rel_cc (Vconstr t l0) (Vconstr t l')).
            { eapply IHv0; constructor; eauto. }
            inv H; eauto.
        + subst v1 v2 l t. inv H2. inv H4. inv H2. inv H5.
          inv H2. inv H4. constructor. constructor.
      - inv H1.
      - inv H1. inv H2. constructor.
    Qed.

    (** The logical relation implies [obs_rel] *)
    Lemma preord_val_implies_obs_rel k v1 v2 :
      preord_val pr cenv k v1 v2 -> obs_rel v1 v2.
    Proof.
      revert v2; induction v1 using val_ind'; intros v2 Hpre; rewrite preord_val_eq in Hpre.
      - destruct v2; simpl in *; try contradiction. inv Hpre. inv H0; eauto.
        constructor; eauto.
      - destruct v2; simpl in *; try contradiction. inv Hpre. inv H0; eauto.
        constructor; eauto. constructor; eauto.
        assert (H : obs_rel (Vconstr c l) (Vconstr c l')).
        { eapply IHv0. rewrite preord_val_eq. constructor; eauto. }
        inv H; eauto.
      - destruct v2; simpl in *; try contradiction. constructor.
      - destruct v2; simpl in *; try contradiction. subst. constructor.
    Qed.

    (** The closure conversion logical relation implies [obs_rel_cc] *)
    Lemma  cc_approx_val_implies_obs_rel_cc k S v1 v2 :
      cc_approx_val pr cenv clo_tag k S v1 v2 ->
      obs_rel_cc v1 v2.
    Proof.
      revert v2; induction v1 using val_ind'; intros v2 Hpre; rewrite cc_approx_val_eq in Hpre.
      - destruct v2; simpl in *; try contradiction. inv Hpre. inv H0; eauto.
        constructor; eauto.
      - destruct v2; simpl in *; try contradiction. inv Hpre. inv H0; eauto.
        constructor; eauto. constructor; eauto.
        assert (H : obs_rel_cc (Vconstr c l) (Vconstr c l')).
        { eapply IHv0. rewrite cc_approx_val_eq. constructor; eauto. }
        inv H; eauto.
      - destruct v2; simpl in *; try contradiction.
        destruct l; simpl in *; try contradiction.
        destruct v0; simpl in *; try contradiction.
        destruct l; simpl in *; try contradiction.
        destruct v1; simpl in *; try contradiction.        
        constructor.
      - destruct v2; simpl in *; try contradiction. subst. constructor.
    Qed.

    (** Currently cannot compose the two logical relations because of the cost invariants.
        TODO fix *)
    
(* 
    (** Top level correctness property of closure conversion and hoisting for closed terms *)
    Corollary closure_conversion_hoist_correct k e ctag itag nmap :
      (* [e] is closed *)
      closed_exp e ->
      (* [e] has unique bindings *)
      unique_bindings e ->
      (* Then [e] and its translation are related by the logical relation *)
      (* No *)
      cc_approx_exp pr cenv clo_tag k (fun _ _ => True) (fun _ _ _ => True)
                    (e, M.empty val)
                    (snd (fst (closure_conversion_hoist clo_tag e ctag itag cenv nmap, M.empty val)),
                     snd (closure_conversion_hoist clo_tag e ctag itag cenv nmap, M.empty val)).
    Proof with now eauto with Ensembles_DB.
      intros Hclo Hun.
      unfold closure_conversion_hoist. 
      set (S := fun y => BinPos.Pos.le (max_var e 1 + 1 + 1)%positive y).
      set (s := {| next_var := (max_var e 1 + 1 + 1)%positive;
                   nect_cTag := ctag;
                   next_iTag := itag;
                   closure_conversion.cenv := cenv |} ).
      assert ({{ fun s : state_contents => fresh S (next_var s)}}
                exp_closure_conv clo_tag e (Maps.PTree.empty VarInfo)
                                 1%positive (max_var e 1 + 1)%positive
              {{fun (_ : state_contents) (ef : exp * (exp -> exp))
                  (_ : state_contents) =>
                  let
                    '(e', f) := ef in
                  cc_approx_exp pr cenv clo_tag k (e, M.empty val) (f e', M.empty val) /\
                  closed_exp (f e') /\
                  unique_bindings (f e') /\
                  closed_fundefs_in_exp (f e')
               }}).
      { eapply post_weakening;
        [| eapply exp_closure_conv_correct_inv; try eassumption ].
        - intros s1 [e' f] s2 _ [H1 [H2 [H3 [H4 _]]]]. split. eassumption.
          split; [| now eauto ]. unfold closed_exp in *. rewrite Hclo in H2.
          now split; eauto with Ensembles_DB.
        - now apply FVmap_inv_empty.
        - intros Hc. inv Hc.
          eapply bound_var_leq_max_var with (y := 1%positive) in H.
          zify; omega.
          eapply occurs_free_leq_max_var with (y := 1%positive) in H.
          zify; omega.
        - unfold closed_exp in Hclo. intros x Hx. rewrite Hclo in Hx. inv Hx.
        - unfold closed_exp in Hclo. intros x Hx. rewrite Hclo in Hx. inv Hx.
        - intros x Hx. now apply M.gempty.
        - intros x Hin. inv Hin.
        - apply Union_Disjoint_r.
          constructor. intros x Hc. 
          inv Hc. eapply bound_var_leq_max_var with (y := 1%positive) in H0.
          unfold S, In in H. zify; omega.
          constructor. intros x Hc. 
          inv Hc. inv H0. eapply occurs_free_leq_max_var with (y := 1%positive) in H1.
          unfold S, In in H. zify; omega.
          inv H1. unfold S, In in H. zify; omega. }
      assert (Hf : fresh S (next_var s)) by (unfold S, s; intros x Hin; eauto).
      unfold triple in H. specialize (H s Hf). 
      destruct (runState _ _) as [[e' f] s'] eqn:Heq.
      destruct H as [Hcc [Hclo' [Hun' HcloB]]].
      eapply cc_approx_exp_respects_preord_exp_r with (e2 := f e').
      eassumption.
      intros k'. eapply hoist_exp_correct.
      - eassumption.
      - eassumption.
      - unfold closed_exp in Hclo'. rewrite Hclo'...
      - apply preord_env_P_refl.
    Qed.
    
    (** Top level correctness property of closure conversion and hoisting for open terms *)
    Corollary closure_conversion_hoist_open_correct k rho rho' e ctag itag nmap :
      (* [e] has unique bindings *)
      unique_bindings e ->
      (* the free variables of [e] are disjoint from the bound variables of [e] *)
      Disjoint _ (bound_var e) (occurs_free e) ->
      (* [rho] contains all the free variables of [e] *)
      binding_in_map (occurs_free e) rho ->
      (* [rho] and [rho'] are related by the closure conversion log. relation *)
      cc_approx_env pr cenv clo_tag k rho rho' ->
      (* Then [e] and its translation are related by the closure conversion log. relation *)
      cc_approx_exp pr cenv clo_tag k
                    (e, rho)
                    (closure_conversion_hoist_open clo_tag rho e ctag itag cenv nmap, rho').
    Proof with now eauto with Ensembles_DB.
      intros Hun HD Hbin Hcc.
      unfold closure_conversion_hoist_open.
      set (Γ := ((max_list (map fst (M.elements rho)) (max_var e 1)) + 1)%positive).
      set (S := fun y => BinPos.Pos.le (Γ + 1)%positive y).
      set (s := {| next_var := (Γ + 1)%positive;
                   nect_cTag := ctag;
                   next_iTag := itag;
                   closure_conversion.cenv := cenv |} ).
      set (map := fold_left
                    (fun (map : M.t VarInfo) (p : M.elt * val) =>
                       M.set (fst p) BoundVar map) (M.elements rho)
                    (Maps.PTree.empty VarInfo)).
      assert ({{ fun s : state_contents => fresh S (next_var s) }}
                exp_closure_conv clo_tag e map 1%positive Γ
                {{fun (_ : state_contents) (ef : exp * (exp -> exp))
                    (_ : state_contents) =>
                    let
                      '(e', f) := ef in
                    cc_approx_exp pr cenv clo_tag k (e, rho) (f e', rho') /\
                    Included _ (occurs_free (f e')) (occurs_free e) /\
                    unique_bindings (f e') /\
                    closed_fundefs_in_exp (f e') /\
                    Included _ (bound_var (f e'))
                             (Union _ (bound_var e) S)
                 }}).
      { eapply post_weakening;
        [| eapply exp_closure_conv_correct_inv
           with (Scope := FromList (List.map fst (M.elements rho)));
           try eassumption ].
        - intros s1 [e' f] s2 _ [H1 [H2 [H3 [H4 H5]]]]. eauto.
        - rewrite <- (Union_Empty_set_neut_r (FromList (List.map fst (M.elements rho))) ).
          eapply populate_map_FVmap_inv. now apply FVmap_inv_empty.
        - intros Hc. inv Hc.
          eapply bound_var_leq_max_var with (y := 1%positive) in H.
          eapply Pos.le_trans
          with (p := max_list (List.map fst (M.elements rho)) (max_var e 1)) in H.
          unfold Γ in H. zify; omega.
          now apply max_list_spec1.
          eapply binding_in_map_Included in H; [| eassumption ].
          eapply max_list_spec2 with (z := (max_var e 1)) in H.
          unfold Γ in H. zify; omega.
        - eapply binding_in_map_antimon;
          [| now eapply populate_map_binding_in_map with (S := Empty_set _);
             intros x Hc; inv Hc ].
          rewrite Union_Empty_set_neut_r. apply binding_in_map_Included.
          eassumption.
        - eapply populate_map_binding_not_in_map.
          intros x Hc. now apply Maps.PTree.gempty. 
          eapply Union_Disjoint_l.
          constructor. intros x Hc. inv Hc.
          unfold S, Γ, In in H. eapply max_list_spec2 with (z := max_var e 1) in H0.
          zify; omega.
          eapply Disjoint_Singleton_l. intros Hc.
          eapply max_list_spec2 with (z := max_var e 1) in Hc.
          unfold S, Γ in Hc. zify; omega.
        - eapply cc_approx_env_P_antimon. eassumption.
          now eauto with Ensembles_DB.
        - apply Union_Disjoint_r.
          constructor. intros x Hc. 
          inv Hc. eapply bound_var_leq_max_var with (y := 1%positive) in H0.
          eapply Pos.le_trans
          with (p := max_list (List.map fst (M.elements rho)) (max_var e 1)) in H.
          unfold S, In, Γ in H. zify; omega.
          eapply Pos.le_trans. eassumption. now apply max_list_spec1.
          apply Union_Disjoint_r.
          constructor. intros x Hc. inv Hc.
          eapply binding_in_map_Included in H0; [| eassumption ].
          eapply max_list_spec2 with (z := (max_var e 1)) in H0.
          unfold S, Γ, In in H. zify; omega.
          eapply Disjoint_Singleton_r. intros Hc. 
          unfold S, Γ, In in Hc. zify; omega. }
      assert (Hf : fresh S (next_var s)) by (unfold S, s; intros x Hin; eauto).
      unfold triple in H. specialize (H s Hf). 
      destruct (runState _ _) as [[e' f] s'] eqn:Heq.
      destruct H as [Hcc' [Hin1 [Hun' [HcloB Hin2]]]].
      eapply cc_approx_exp_respects_preord_exp_r with (e2 := f e').
      eassumption.
      intros k'. eapply hoist_exp_correct; [ eassumption | eassumption | | ].
      - eapply Disjoint_Included_r. eassumption.
        eapply Disjoint_Included_l. eassumption.
        eapply Union_Disjoint_l. eassumption.
        constructor. intros x Hc. inv Hc.
        eapply binding_in_map_Included in H0; [| eassumption ].
        eapply max_list_spec2 with (z := (max_var e 1)) in H0.
        unfold S, Γ, In in H. zify; omega.
      - apply preord_env_P_refl.
    Qed.  
*)
    
End L6_trans.
