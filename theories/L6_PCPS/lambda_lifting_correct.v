Require Import L6.cps L6.cps_util L6.set_util L6.hoisting L6.identifiers L6.ctx
        L6.Ensembles_util L6.alpha_conv L6.List_util L6.functions L6.lambda_lifting
        L6.eval L6.logical_relations L6.hoare.
Require Import Libraries.Coqlib.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Section Lambda_lifting_correct.

  Variable pr : prims.
  Variable cenv : cEnv.

  (** The invariant that relates the original function definitions with the lifted ones *)
  Definition Funs_inv k (rho rho' : env) (σ : var -> var) (ζ : var -> option (var * fTag * list var)) :=
    forall f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1 xs1 e1,
      ζ f = Some (f', ft', fvs) ->
      M.get f rho = Some (Vfun rho1 B1 f1) ->
      length vs1 = length vs2 ->
      find_def f1 B1 = Some (ft1, xs1, e1) ->
      Some rho1' = setlist xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
      exists rho2 rho2' B2 f2 xs2 e2 vs2',
        M.get f' rho' = Some (Vfun rho2 B2 f2) /\
        find_def f2 B2 = Some (ft', xs2, e2) /\
        getlist (map σ fvs) rho' = Some vs2' /\
        Some rho2' = setlist xs2 (vs2 ++ vs2') (def_funs B2 B2 rho2 rho2) /\
        (j < k -> Forall2 (preord_val pr cenv j) vs1 vs2 ->
         preord_exp pr cenv j (e1, rho1') (e2, rho2')).

  (*& Map from the original name to the name of the lifted function *)
  Definition lifted_name (ζ : var -> option (var * fTag * list var)) : var -> option var :=
    fun f => (liftM (fun x => (fst (fst x)))) (ζ f).
  
  (** The domain of ζ *)
  Definition Funs (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
    domain (lifted_name ζ).
  
  (** The image of ζ on its domain - i.e. the names of the lifted functions *)
  Definition LiftedFuns (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
    image' (lifted_name ζ) (Funs ζ).

  (**  The free variables of functions in ζ *)
  Definition FunsFVs (ζ : var -> option (var * fTag * list var)) : Ensemble var :=
    fun v => exists f f' ft' fvs, ζ f = Some (f', ft', fvs) /\
                          In _ (FromList fvs) v.

  (**  The free variables of functions in ζ, alternative definition *)
  Definition FunsFVsLst (ζ : var -> option (var * fTag * list var)) : Ensemble (list var) :=
    fun fvs => exists f f' ft', ζ f = Some (f', ft', fvs).
  
  (** * Lemmas about [lifted_name], [Funs], [LiftedFuns], [FunsFVs] and [FunsFVsLst] *)

  Lemma lifted_name_extend f x x' xs l :
    f_eq (lifted_name (f {x ~> Some (x', xs, l)})) ((lifted_name f) { x ~> Some x' }).
  Proof.
    intros y. unfold lifted_name; simpl.
    destruct (peq x y); subst.
    - rewrite !extend_gss. reflexivity.
    - rewrite !extend_gso; eauto.
  Qed.

  Lemma lifted_name_eq f x x' xs l :
    f x = Some (x', xs, l) ->
    lifted_name f x = Some x'.
  Proof.
    intros Heq; unfold lifted_name; rewrite Heq; eauto.
  Qed.

  Lemma Funs_extend_Some ζ f f' ft fvs :
    Included _ (Funs (ζ {f ~> Some (f', ft, fvs)}))
             (Union _ (Funs ζ) (Singleton _ f)).
  Proof.
    intros x [val H].
    destruct (peq f x); subst.
    - rewrite lifted_name_extend, extend_gss in H. inv H. eauto.
    - rewrite lifted_name_extend, extend_gso in H; eauto.
      left. eexists; eauto.
  Qed.

  Lemma LiftedFuns_extend_Some ζ f f' ft fvs :
    Included _ (LiftedFuns (ζ {f ~> Some (f', ft, fvs)}))
            (Union _ (LiftedFuns ζ) (Singleton _ f')).
  Proof.
    intros x [g [H1 H2]].
    destruct (peq f g); subst; rewrite lifted_name_extend in H2;
    apply Funs_extend_Some in H1.
    - rewrite extend_gss in H2. inv H2. eauto.
    - rewrite extend_gso in H2; eauto. inv H1; eauto.
      left. repeat eexists; eauto.
      inv H; congruence.
  Qed.
  
  Lemma FunsFVs_extend_Some ζ f f' ft fvs :
    Included _ (FunsFVs (ζ {f ~> Some (f', ft, fvs)}))
            (Union _ (FunsFVs ζ) (FromList fvs)).
  Proof.
    intros x [g [g' [gt' [fvs' [H1 H2]]]]].
    destruct (peq f g); subst.
    - rewrite extend_gss in H1. inv H1. eauto.
    - rewrite extend_gso in H1; eauto.
      left. eexists; eauto.
  Qed.
  
  Lemma FunsFVs_extend_Some_eq ζ f f' ft fvs :
    ~ In _ (Funs ζ) f ->
    Same_set var (FunsFVs (ζ {f ~> Some (f', ft, fvs)}))
             (Union var (FunsFVs ζ) (FromList fvs)).
  Proof.
    intros Hn; split.
    - now apply FunsFVs_extend_Some.
    - intros x Hin. inv Hin.
      destruct H as [g [g' [fg [l [Heq Hin]]]]].
      repeat eexists; eauto. rewrite extend_gso.
      eassumption. intros Hc; apply Hn. subst.
      repeat eexists; eauto. eapply lifted_name_eq.
      subst. eassumption.
      repeat eexists; eauto. rewrite extend_gss.
      reflexivity.
  Qed.

  (** * Lemmas about [Funs_inv] *)  
  
  Lemma Funs_inv_set k rho rho' σ ζ v1 v2 x y :
    ~ In _ (Funs ζ) x ->
    ~ In _ (LiftedFuns ζ) y ->
    ~ In _ (FunsFVs ζ) x ->
    ~ In _ (image σ (FunsFVs ζ)) y ->
    Funs_inv k rho rho' σ ζ ->
    Funs_inv k (M.set x v1 rho) (M.set y v2 rho') (σ {x ~> y}) ζ.
  Proof.
    intros Hnin1 Hnin2 Hnin3 Hnin4 Hinv f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    assert (Heq : lifted_name ζ f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    assert (Hneq : f <> x)
      by (intros Hc; subst; eapply Hnin1; eexists; eauto).    
    rewrite M.gso in Hget2; eauto. 
    edestruct Hinv as
        [rho2 [rho2' [B2 [f2 [xs2 [e2 [vs2' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - rewrite M.gso. eassumption. intros Hc; subst.
      eapply Hnin2. eexists; split; eauto. repeat eexists; eauto.
    - rewrite getlist_set_neq. rewrite map_extend_not_In. eassumption.
      intros Hc. eapply Hnin3. now repeat eexists; eauto.
      intros Hc. eapply in_map_iff in Hc. destruct Hc as [x' [Heq' HIn]].
      destruct (peq x x') as [ Heq'' | Hneq' ].
      eapply Hnin3. repeat eexists. eassumption. rewrite Heq''.
      eassumption.
      rewrite extend_gso in Heq'; eauto. eapply Hnin4.
      repeat eexists; eassumption.
  Qed.

  Lemma Funs_inv_setlist k rho rho' rho1 rho1' σ ζ vs1 vs2 xs ys :
    setlist xs vs1 rho = Some rho1 ->
    setlist ys vs2 rho' = Some rho1' ->
    Funs_inv k rho rho' σ ζ ->                        
    Disjoint _ (Funs ζ) (FromList xs) ->
    Disjoint _ (LiftedFuns ζ) (FromList ys) ->
    Disjoint _ (FunsFVs ζ) (FromList xs) ->
    Disjoint _ (image σ (Setminus _ (FunsFVs ζ) (FromList xs))) (FromList ys) ->
    Funs_inv k rho1 rho1' (σ <{xs ~> ys}>) ζ.
  Proof.
    intros Hset1 Hset2 Hinv HD1 HD2 HD3 HD4 f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    assert (Heq := lifted_name_eq _ _ _ _ _ Hget1).
    assert (Hneq : ~ In _ (FromList xs) f)
      by (intros Hc; subst; eapply HD1; constructor; eauto; eexists; eauto).
    erewrite <- setlist_not_In in Hget2; eauto.
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - erewrite <- setlist_not_In; eauto.
      intros Hc; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
    - erewrite getlist_setlist_Disjoint; eauto.
      rewrite map_extend_lst_Disjoint. eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eassumption.
      eapply Disjoint_Included_r_sym; [| eassumption ].
      rewrite map_extend_lst_Disjoint.
      intros x Hin. unfold In, FromList in Hin. eapply list_in_map_inv in Hin.
      edestruct Hin as [x' [Heq' Hin']]. eexists; split; eauto.
      constructor. 
      repeat eexists; eassumption.
      intros Hc. eapply HD3. constructor; eauto.
      now repeat eexists; eauto.
      eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eassumption.
  Qed.

  Lemma Funs_inv_setlist_getlist_r k rho rho' rho'' σ ζ vs xs ys :
    setlist ys vs rho' = Some rho'' ->
    getlist (map σ xs) rho' = Some vs ->
    Funs_inv k rho rho' σ ζ ->
    NoDup ys -> NoDup xs ->
    length xs = length ys ->
    Disjoint _ (LiftedFuns ζ) (FromList ys) ->
    Disjoint _ (image σ (FunsFVs ζ)) (FromList ys) ->
    Funs_inv k rho rho'' (σ <{xs ~> ys}>) ζ.
  Proof.
    intros Hset1 Hgetl Hinv Hnd1 Hnd2 Hlen HD1 Hinc  f f' ft' fvs vs1'
           vs2' j ft1  rho2 rho2' B1 f1 xs1 e1 Hget1 Hget2 Hlen' Hdef Hset.
    assert (Heq : lifted_name ζ f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl' [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - erewrite <- setlist_not_In; eauto.
      intros Hc; subst. eapply HD1. constructor; eauto.
      repeat eexists; eauto.
    - erewrite <- getlist_reset_lst; try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply image_monotonic. 
      intros x Hin. repeat eexists; eauto.
  Qed.

  Lemma Funs_inv_monotonic k i rho rho' σ ζ :
    Funs_inv k rho rho' σ ζ ->
    i <= k ->
    Funs_inv i rho rho' σ ζ.
  Proof.
    intros Hinv Hleq f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 7 eexists; repeat split; try eassumption.
    intros Hlt. eapply Hpre. omega.
  Qed.

  Instance Funs_inv_Proper : Proper (eq ==> eq ==> eq ==> f_eq ==> eq ==> iff) Funs_inv.
  Proof.
    constructor; intros Hinv f f' ft' fvs vs1' vs2' j ft1  rho2 rho2' B1 f1
                        xs1 e1 Hget1 Hget2 Hlen Hdef Hset; subst;
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto;
    do 7 eexists; repeat split; eauto.
    rewrite <- H2. eassumption.
    rewrite H2. eassumption.
  Qed.  
  
  Lemma Funs_inv_set_lifted k rho rho' rho1 rho2 B1 B1' ζ σ v v' ft ft' xs xs' ys fvs e1 e1' vs  :
    preord_val pr cenv k (Vfun rho1 B1 v) (Vfun rho2 B1' v) ->

    find_def v B1 = Some (ft, xs, e1) ->
    find_def v' B1' = Some (ft', xs ++ ys, e1') ->
    find_def v B1' = Some (ft, xs', Eapp v' ft' (xs' ++ (map σ fvs))) ->
    NoDup xs' ->
    length xs = length xs' ->
    length ys = length fvs ->

    getlist (map σ fvs) rho' = Some vs ->
    getlist (map σ fvs) rho2 = Some vs ->

    Disjoint _ (Union _ (FunsFVs ζ) (FromList fvs)) (bound_var_fundefs B1) ->
    Disjoint _ (LiftedFuns ζ) (bound_var_fundefs B1) ->
    Disjoint _ (image σ (Union _ (FromList fvs) (FunsFVs ζ))) (Union _ (name_in_fundefs B1') (FromList xs')) ->
    Disjoint _ (FromList xs') (name_in_fundefs B1') ->
    ~ In _ (LiftedFuns ζ) v' ->
    
    preord_env_P_inj pr cenv (FromList fvs) k σ rho rho' ->
    Funs_inv k rho rho' σ ζ ->

    Funs_inv k (M.set v (Vfun rho1 B1 v) rho)
             (M.set v' (Vfun rho2 B1' v')
                    (M.set v (Vfun rho2 B1' v) rho'))
             (σ {v ~> v}) (ζ {v ~> Some (v', ft', fvs)}).
  Proof.    
    intros Hval Hf1 Hf2 Hf3 Hnd Hlen1 Hlen2 Hgetfvs Hgetfvs1 HD1 HD2 HD3 HD4
           Hnin Henv Hinv.
    intros g g' t fvsg vs1 vs2 j gt1 rho3 rho4 B g1 xs1 e2 Happ Hget Hlen Hdef Hset.
    assert (Heq1 := lifted_name_eq _ _ _ _ _ Happ).
    destruct (peq g v).
    - subst. rewrite extend_gss in Happ. inv Happ.
      rewrite M.gss in Hget; inv Hget. rewrite Hf1 in Hdef. inv Hdef.
      edestruct setlist_length3 with (xs := xs1 ++ ys) (vs := vs2 ++ vs) as [rho4' Hset4'].
      rewrite !app_length. erewrite setlist_length_eq; [| now eauto ].
      erewrite <- (getlist_length_eq _ vs); [| eassumption ].
      rewrite map_length. congruence.
      do 7 eexists. repeat split; eauto.
      + rewrite M.gss; eauto.
      + rewrite map_extend_not_In; eauto. rewrite !getlist_set_neq; eauto. 
        intros Hc.
        assert (Hin : In _ (image σ (FromList fvsg)) g1).  
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD3. constructor. 
        eapply image_monotonic; [| eassumption ].
        now eauto with Ensembles_DB.
        left. eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
        intros Hc.
        assert (Hin : In _ (image σ (FromList fvsg)) g').
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD3. constructor.
        eapply image_monotonic; [| eassumption ].
        now eauto with Ensembles_DB.
        left. eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
        intros Hc. eapply HD1. constructor; eauto.
        eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
      + intros Hlt Hall. rewrite preord_val_eq in Hval.
        edestruct Hval as [xs2 [e2' [rho5 [Hf5 [Hset5 Hpre5]]]]]; try eassumption.
        rewrite Hf3 in Hf5; inv Hf5. specialize (Hpre5 Hlt Hall).
        intros v1 c1 Heq' Hstep.
        edestruct (@setlist_app val) as [rho6 [Hset6 Hset6']]. eassumption.
        erewrite setlist_length_eq; now eauto.
        specialize (Hpre5 v1 c1 Heq' Hstep).
        edestruct Hpre5 as [v2 [c2 [Hstep' Hval']]]. inv Hstep'.
        erewrite <- setlist_not_In in H2; [| now eauto  |].
        rewrite def_funs_eq in H2. inv H2. rewrite Hf2 in H5; inv H5.
        assert (Heq'' : vs0 = vs2 ++ vs).
        { edestruct (@app_getlist val) as [vs1' [vs2' [Hget1 [Hget2 Heq3]]]]; subst.
          eassumption. subst.
          erewrite getlist_setlist in Hget1; [| | now eauto ]. inv Hget1.
          erewrite getlist_setlist_Disjoint in Hget2; [| | now eauto].
          rewrite getlist_def_funs_Disjoint in Hget2.
          rewrite Hget2 in Hgetfvs1. inv Hgetfvs1. reflexivity.
          rewrite FromList_map_image_FromList.
          eapply Disjoint_Included ;[ | | now apply HD3 ].
          now eauto with Ensembles_DB.
          apply image_monotonic. now eauto with Ensembles_DB.
          eapply Disjoint_sym. eapply Disjoint_Included ;[ | | now apply HD3 ].
          now eauto with Ensembles_DB.
          rewrite FromList_map_image_FromList.
          apply image_monotonic. now eauto with Ensembles_DB.
          eassumption. } 
        subst.
        rewrite Hset4' in H8. inv H8. do 2 eexists; eauto.
        eapply fun_in_fundefs_name_in_fundefs. apply find_def_correct.
        eassumption.
        intros Hc. eapply HD4. constructor; eauto.
        eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
    - rewrite lifted_name_extend in Heq1.
      rewrite extend_gso in Happ; rewrite extend_gso in Heq1; eauto.
      subst. rewrite M.gso in Hget; eauto.
      assert (Hnin' : ~ In _ (FromList fvsg) v).
      { intros Hc. eapply HD1. constructor. left; eauto. 
        repeat eexists; eauto. apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs. apply find_def_correct.
        eassumption. }      
      edestruct Hinv
        as [rho5 [rho6 [B3 [f3 [xs3 [e3 [vs3' [Hget3 [Hfind3 [Hgetl3 [Hset3 Hpre3]]]]]]]]]]];
        try eassumption.
      do 7 eexists.
      split; [| split; [| split; [| split ]]]; try eassumption.
      + rewrite !M.gso. eassumption.
        intros Hc; subst. eapply HD2. constructor.
        now repeat eexists; eauto.
        apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption. intros Hc. subst.
        apply Hnin. repeat eexists; eauto.
      + rewrite map_extend_not_In; eauto.
        rewrite !getlist_set_neq. eassumption.
        intros Hc. 
        assert (Hin : In _ (image σ (FromList fvsg)) v). 
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD3. constructor.
        eapply image_monotonic; [| eassumption ].
        intros x Hl. repeat eexists. right. now repeat eexists; eauto.
        left. eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
        intros Hc. 
        assert (Hin : In _ (image σ (FromList fvsg)) v'). 
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD3. constructor.
        eapply image_monotonic; [| eassumption ].
        intros x Hl. repeat eexists. right. now repeat eexists; eauto.
        left. eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
  Qed.

  (** * Lemmas about [Add_functions] *)

  Lemma Add_functions_free_set_Included B fvs ζ σ S ζ' σ' S' :
    Add_functions B fvs ζ σ S ζ' σ' S' ->
    Included _ S' S.
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd...
  Qed.

  Lemma Add_functions_fvs_eq B fvs σ ζ S σ' ζ' S' f f' ft fvs' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    ζ' f = Some (f', ft, fvs') ->
    In _ (name_in_fundefs B) f ->
    fvs' = fvs.
  Proof.
    intros Hadd Heq Hin; induction Hadd.
    - destruct (peq f f0); subst.
      + rewrite extend_gss in Heq. inv Heq. eauto.
      + inv Hin. inv H0; congruence.
        rewrite extend_gso in Heq; eauto.
    - inv Hin.
  Qed.

  Lemma Add_functions_image_Included P B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included _ (image σ' P) (Union _ (image σ (Setminus _ P (name_in_fundefs B))) (name_in_fundefs B)).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. revert P. induction Hadd; intros P.
    - eapply Included_trans.
      eapply image_extend_Included'. 
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Included_trans. eapply IHHadd.
      rewrite Setminus_Union...
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Add_functions_LiftedFuns_Included B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included _ (LiftedFuns ζ') (Union _ (LiftedFuns ζ) (Setminus _ S S')).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd.
    - eapply Included_trans.
      eapply LiftedFuns_extend_Some.
      eapply Union_Included.
      eapply Included_trans. now eapply IHHadd.
      now eauto with Ensembles_DB.
      eapply Included_Union_preserv_r.
      eapply Singleton_Included. constructor.
      eapply Add_functions_free_set_Included; eassumption.
      intros Hc. inv Hc. eauto.
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Add_functions_Funs_Included B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included _ (Funs ζ') (Union _ (Funs ζ) (name_in_fundefs B)).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd.
    - eapply Included_trans.
      eapply Funs_extend_Some.
      eapply Union_Included.
      eapply Included_trans. now eapply IHHadd.
      now eauto with Ensembles_DB.
      eapply Included_Union_preserv_r...
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Add_functions_FunsFVs_Included_r B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included _ (FunsFVs ζ') (Union _ (FunsFVs ζ) (FromList fvs)).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd.
    - eapply Included_trans.
      eapply FunsFVs_extend_Some.
      eapply Union_Included.
      eapply Included_trans. now eapply IHHadd.
      now eauto with Ensembles_DB.
      eapply Included_Union_preserv_r...
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Add_functions_FunsFVs_Included_l B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    unique_bindings_fundefs B ->
    Disjoint _ (Funs ζ) (name_in_fundefs B) ->
    Included _ (FunsFVs ζ) (FunsFVs ζ').
  Proof with now eauto with Ensembles_DB.
    intros Hadd Hun HD. induction Hadd.
    - inv Hun. eapply Included_trans. eapply IHHadd.
      eassumption. now eauto with Ensembles_DB.
      rewrite FunsFVs_extend_Some_eq.
      now eauto with Ensembles_DB.
      intros Hc. 
      eapply Add_functions_Funs_Included in Hc; [| eassumption ].
      inv Hc. eapply HD. constructor; eauto. left; eauto.
      eapply H6. apply name_in_fundefs_bound_var_fundefs. eassumption.
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Add_functions_σ_eq B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    f_eq_subdomain (Complement _ (name_in_fundefs B)) σ σ'.
  Proof.
    intros Hadd. induction Hadd; simpl.
    - eapply f_eq_subdomain_extend_not_In_S_r.
      intros Hc; apply Hc. eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      now eauto with Ensembles_DB.
    - reflexivity.
  Qed.

  Lemma Add_functions_lifted_name_Disjoint B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    unique_bindings_fundefs B ->
    Disjoint _ (LiftedFuns ζ) S ->
    Disjoint _ (image (lifted_name ζ') (name_in_fundefs B))
             (image (lifted_name ζ') (Complement _ (name_in_fundefs B))).
  Proof.
    intros Hadd Hun HD. induction Hadd; simpl.
    - inv Hun. rewrite image_Union. apply Union_Disjoint_l.
      rewrite image_Singleton.
      rewrite !lifted_name_extend, !extend_gss.
      rewrite image_extend_not_In_S; eauto.
      constructor. intros x Hc. inv Hc. inv H0.
      destruct H1 as [x' [Hin Heq]].
      assert (Hin' : In _ (LiftedFuns ζ') f').
      now repeat eexists; eauto.
      eapply Add_functions_LiftedFuns_Included in Hin'; [| eassumption ].
      inv Hin'. eapply HD.  constructor; eauto.
      eapply Add_functions_free_set_Included; eassumption.
      inv H0; eauto.
      eapply Disjoint_Included; [| | now apply IHHadd ].
      rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
      apply image_monotonic...
      now eauto with Ensembles_DB.
      rewrite lifted_name_extend. rewrite image_extend_not_In_S; eauto.
      reflexivity. intros Hc. eapply H6.
      now eapply name_in_fundefs_bound_var_fundefs.
    - rewrite image_Empty_set. now eauto with Ensembles_DB.
  Qed.


  Lemma Add_functions_map_eq B fvs σ ζ S σ' ζ' S' l :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Disjoint _ (FromList l) (name_in_fundefs B) ->
    map σ l = map σ' l.
  Proof.
    intros Hadd HD. induction l; eauto.
    simpl. rewrite FromList_cons in HD.
    erewrite Add_functions_σ_eq; [| eassumption |].
    rewrite IHl. reflexivity.
    now eauto with Ensembles_DB.
    intros Hc. eapply HD; eauto.
  Qed.

  Lemma Add_functions_FunsFVs_Included_alt P B fvs σ ζ S σ' ζ' S' f f' ft fvs' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Disjoint _ (FunsFVs ζ) P ->
    ζ' f = Some (f', ft, fvs') ->
    fvs' = fvs \/ Disjoint _ (FromList fvs') P.
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd; intros Hin Heq.
    - destruct (peq f0 f); subst.
      + rewrite extend_gss in Heq.
        inv Heq; eauto.        
      + rewrite extend_gso in Heq; eauto.
    - right. eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eauto.
  Qed.

  Lemma Add_functions_injective_subdomain P B fvs σ ζ S σ' ζ' S'  :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    unique_bindings_fundefs B ->
    injective_subdomain (Setminus _ P (name_in_fundefs B)) σ ->
    Disjoint _ (image σ (Setminus _ P (name_in_fundefs B))) (name_in_fundefs B) ->
    injective_subdomain P σ'.
  Proof with now eauto with Ensembles_DB.
    intros Hadd. revert P; induction Hadd; intros P Hun Hinj HD.
    - inv Hun. eapply injective_subdomain_extend'.
      eapply IHHadd. eassumption. now rewrite Setminus_Union.
      rewrite Setminus_Union...
      intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ].
      inv Hc. eapply HD.
      constructor; eauto. rewrite Setminus_Union in H0; eassumption.
      left; eauto.
      eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption.
    - simpl in Hinj. now rewrite Setminus_Empty_set_neut_r in Hinj.
  Qed.
  
  Lemma Add_functions_image_LiftedFuns_Included B fvs σ ζ S σ' ζ' S' x f :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    lifted_name ζ' x = Some f ->
    In _ (name_in_fundefs B) x ->
    In _ S f /\ ~ In _ S' f.
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd; intros Heq Hin.
    - destruct (peq f0 x); subst.
      + rewrite lifted_name_extend, extend_gss in Heq. inv Heq.
        split.
        eapply Add_functions_free_set_Included; eassumption.
        intros Hc. inv Hc; eauto.
      + rewrite lifted_name_extend, extend_gso in Heq; eauto.
        inv Hin. inv H0; congruence.
        eapply IHHadd in Heq; eauto. inv Heq.
        split; eauto. intros Hc. inv Hc. eauto.
    - inv Hin.
  Qed.
    
  Lemma Add_functions_injective_subdomain_LiftedFuns B fvs σ ζ S σ' ζ' S'  :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    injective_subdomain (name_in_fundefs B) (lifted_name ζ').
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd.
    - simpl. rewrite lifted_name_extend. eapply injective_subdomain_extend.
      eassumption.
      intros [x [Hin Heq]]; subst. inv Hin.
      eapply Add_functions_image_LiftedFuns_Included in Hadd; try eassumption.
      inv Hadd; eauto.
    - eapply injective_subdomain_Empty_set.
  Qed.

  Lemma Add_functions_map_Disjoint B fvs f g S f' g' S' l :
    Add_functions B fvs f g S f' g' S' ->
    Disjoint positive (FromList l) (name_in_fundefs B) ->
    map f' l = map f l.
  Proof with now eauto with Ensembles_DB.
    intros Hadd HD. induction Hadd.
    - rewrite map_extend_not_In. eapply IHHadd...
      intros Hc. eapply HD; eauto.
      constructor; eauto. left; eauto.
    - reflexivity.
  Qed.

  (** * Lemmas about [Exp_lambda_lift] and [Fundefs_lambda_lift] *)

  Lemma Fundefs_lambda_lift_name_in_fundefs ζ σ B S B' S' :
    Fundefs_lambda_lift ζ σ B S B' S' ->
    Included _ (name_in_fundefs B') (Union _ (name_in_fundefs B) (LiftedFuns ζ)).
  Proof.
    intros Hadd; induction Hadd; simpl.
    - assert (Heq := lifted_name_eq _ _ _ _ _ H).
      assert (Hin : Included _ (Singleton var f') (LiftedFuns ζ)).
      { eapply Singleton_Included. repeat eexists; eauto. }
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans; now eauto with Ensembles_DB.
    - now eauto with Ensembles_DB.
  Qed.

  Lemma Lambda_lift_free_set_Included_mut :
    (forall e ζ σ S e' S',
       Exp_lambda_lift ζ σ e S e' S' ->
       Included _ S' S) /\
    (forall B ζ σ S B' S',
       Fundefs_lambda_lift ζ σ B S B' S' ->
       Included _ S' S).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros; inv H; try now eauto with Ensembles_DB.
    - eapply Included_trans. now eapply IHl; eauto.
      eapply IHe; eauto.
    - eapply Included_trans. now eapply IHe; eauto.
      eapply Included_trans. now eapply IHB; eauto.
      eapply Add_functions_free_set_Included; eauto.
    - eapply Included_trans. now eapply IHB; eauto.
      eapply Included_trans. now eapply IHe; eauto.
      now eauto with Ensembles_DB.
  Qed.

  Corollary Exp_Lambda_lift_free_set_Included :
    forall e ζ σ S e' S',
      Exp_lambda_lift ζ σ e S e' S' ->
      Included _ S' S.
  Proof.
    destruct Lambda_lift_free_set_Included_mut; eauto.
  Qed.

  Corollary Fundefs_Lambda_lift_free_set_Included :
    forall B ζ σ S B' S',
      Fundefs_lambda_lift ζ σ B S B' S' ->
      Included _ S' S.
  Proof.
    destruct Lambda_lift_free_set_Included_mut; eauto.
  Qed.
  
  Lemma Fundefs_lambda_lift_find_def σ ζ S1 B1 S2 B2 f t xs1 e1 f' t' fvs :
    Fundefs_lambda_lift ζ σ B1 S1 B2 S2 ->
    ζ f = Some (f', t', fvs) ->
    Disjoint _ (bound_var_fundefs B1) (LiftedFuns ζ) ->
    injective_subdomain (name_in_fundefs B1) (lifted_name ζ) ->
    find_def f B1 = Some (t, xs1, e1) ->
    exists (xs1' ys : list var) (e2 : exp) S2 S2',
      find_def f B2 = Some (t, xs1', (Eapp f' t' (xs1' ++ map σ fvs))) /\
      find_def f' B2 = Some (t', xs1 ++ ys, e2) /\
      NoDup ys /\ NoDup xs1' /\
      length xs1 = length xs1' /\
      length ys = length fvs /\
      Included _ S2 S1 /\
      Included _ (FromList ys) S1 /\
      Included _ (FromList xs1') S1 /\
      Disjoint _ (FromList ys) S2 /\
      Disjoint _ (FromList xs1') S2 /\
      Disjoint _ (FromList xs1') (FromList ys) /\
      Exp_lambda_lift ζ (σ <{ xs1 ++ fvs ~> xs1 ++ ys }>) e1 S2 e2 S2'.
  Proof with now eauto with Ensembles_DB.
    intros Hll. induction Hll; intros Heq HD Hinj Hdef.
    - assert (Heq' := lifted_name_eq _ _ _ _ _ Heq).
      simpl in Hdef. destruct (M.elt_eq f f0); subst.
      + rewrite Heq in H; inv H. inv Hdef.
        exists xs', ys, e'. do 2 eexists.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]];
        [ | | | | | | | | | | | | eassumption ]; eauto.
        * simpl. rewrite peq_false, peq_true. reflexivity.
          intros Hc. subst. eapply HD. constructor; eauto.
          repeat eexists; eauto.
        * simpl. rewrite peq_true. reflexivity.
        * now eauto with Ensembles_DB.
        * eapply Included_trans; [ eassumption |]...
        * now eauto with Ensembles_DB.
        * now eauto with Ensembles_DB.
        * eapply Disjoint_Included_l; [ eassumption |]...
      + destruct IHHll as (xs1' & ys' & e2 & S2 & S2' & Hf1 & Hf2 & Hnd1 & Hnd2
                                & Heq1 & Heq2 & Hinc1 & Hinc2 & Hinc3 & Hd1 & Hd2 & Hd3 & Hexp).
        eassumption. normalize_bound_var_in_ctx...
        eapply injective_subdomain_antimon. eassumption.
        now eauto with Ensembles_DB. eassumption.
        eexists xs1', ys', e2. do 2 eexists.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]];
        [ | | | | | | | | | | | | eassumption ]; eauto.
        * simpl. rewrite peq_false; eauto. rewrite peq_false; now eauto.
          intros Hc. subst. eapply HD. constructor.
          constructor 2. apply name_in_fundefs_bound_var_fundefs.
          eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
          eassumption. eexists.
          split; repeat eexists; now unfold lifted_name; rewrite H; eauto.
        * simpl. rewrite peq_false; eauto. rewrite peq_false; eauto.
          intros Hc. subst. eapply HD. constructor. now eauto.
          now repeat eexists; eauto.
          intros Hc; subst. eapply n. eapply Hinj.
          constructor 2. eapply fun_in_fundefs_name_in_fundefs.
          eapply find_def_correct. eassumption.
          now simpl; eauto. erewrite !lifted_name_eq; eauto.
        * eapply Included_trans. eassumption.
          eapply Included_trans. eapply Exp_Lambda_lift_free_set_Included.
          eassumption.
          now eauto with Ensembles_DB.
        * eapply Included_trans. eassumption.
          eapply Included_trans.
          eapply Exp_Lambda_lift_free_set_Included; now eauto.
          now eauto with Ensembles_DB.
        * eapply Included_trans. eassumption.
          eapply Included_trans.
          eapply Exp_Lambda_lift_free_set_Included; now eauto.
          now eauto with Ensembles_DB.
    - inv Hdef.
  Qed.
      
  Lemma Fundefs_lambda_lift_correct k rho rho' B1 B1' B2 B2' σ ζ σ1 ζ1 σ2 ζ2 S
        S1' S1'' S1''' S2' S2'' S2''' fvs e:
    (* The IH for expressions *)
     (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
          (ζ : var -> option (var * fTag * list var)) 
          (σ : var -> var) (S : Ensemble var) (e' : exp) 
          (S' : Ensemble var),
        unique_bindings e ->
        Disjoint var (image σ (Union _ (occurs_free e) (FunsFVs ζ)))
                 (Union var S (Union _ (bound_var e) (LiftedFuns ζ))) ->
        Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
        Disjoint var (LiftedFuns ζ) (Union _ S (bound_var e)) ->
        Disjoint var (Funs ζ) (bound_var e) ->
        Disjoint var (FunsFVs ζ) (bound_var e) ->
        Disjoint _ (bound_var e) (occurs_free e) ->
        binding_in_map (Union _ (occurs_free e) (FunsFVs ζ)) rho ->
        preord_env_P_inj pr cenv (Union _ (occurs_free e) (FunsFVs ζ)) m σ rho rho' ->
        Funs_inv m rho rho' σ ζ ->
        Exp_lambda_lift ζ σ e S e' S' ->
        preord_exp pr cenv m (e, rho) (e', rho')) ->

     (* Unique bindings *)
     unique_bindings_fundefs B1 ->
     unique_bindings_fundefs B2 ->

     (* The image of σ is neither in the free set nor in the set of bound variables *)
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)))
              (Union var S (Union _ (bound_var_fundefs B1) (LiftedFuns ζ))) ->
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)))
              (Union var S (Union _ (bound_var_fundefs B2) (LiftedFuns ζ))) ->

     (* The free set is disjoint from the set of bound and free variables *)
     Disjoint var S (Union var (bound_var_fundefs B1) (occurs_free_fundefs B1)) ->
     Disjoint var S (Union var (bound_var_fundefs B2) (occurs_free_fundefs B2)) ->

     (* The names of lifted functions is neither in the free set nor in the set of bound variables*) 
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B1)) ->
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B2)) ->

     (* The domain of ζ is disjoint with the bound variables *)
     Disjoint var (Funs ζ) (bound_var_fundefs B1) ->

     (* The free variables of the funs in ζ are disjoint from the bound variables *) 
     Disjoint var (FunsFVs ζ) (bound_var_fundefs B1) ->
     Disjoint var (FunsFVs ζ) (bound_var_fundefs B2) ->

     (* The bound variables and the free variables are disjoint *)
     Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

     (* The free variables are in the environment *)
     binding_in_map (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)) rho ->

     (** ζ1 and ζ2 are equal in a [name_in_fundefs B2] *) 
     f_eq_subdomain (name_in_fundefs B2) ζ1 ζ2 ->

     (** The invariant hold for the initial environments **)
     preord_env_P_inj pr cenv (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)) k σ rho rho' ->
     Funs_inv k rho rho' σ ζ ->
     
     NoDup fvs ->
     Included _ (FromList fvs) (occurs_free_fundefs B1) ->
     Disjoint var (FromList fvs) (bound_var_fundefs B1) ->
     Disjoint var (FromList fvs) (bound_var_fundefs B2) ->

     Included _ (name_in_fundefs B2) (name_in_fundefs B1) ->
     
     Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
     Included _ S1'' S1' ->
     Fundefs_lambda_lift ζ1 σ1 B1 S1'' B1' S1''' ->
     
     Add_functions B2 fvs σ ζ S σ2 ζ2 S2' ->
     Included _ S2'' S2' ->
     Fundefs_lambda_lift ζ1 σ1 B2 S2'' B2' S2''' ->

     (** The invariants hold for the final environments **)
     preord_env_P_inj pr cenv (Union _ (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B2)) (FunsFVs ζ1))
                      k σ2 (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho') /\
     Funs_inv k (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho') σ2 ζ2.
  Proof with now eauto with Ensembles_DB.
    revert B2 rho rho' B1 B1' B2' σ ζ σ1 ζ1 σ2 ζ2 S S1' S1'' S1''' S2' S2'' S2''' fvs.
    induction k as [ k IH' ] using lt_wf_rec1.
    induction B2;
      intros rho rho' B1 B1' B2' σ ζ σ1 ζ1 σ2 ζ2 S S1' S1'' S1''' S2' S2'' S2''' fvs
             IHe Hun1 Hun2 Him1 Him2 Hf1 Hf2 Hlf1 Hlf2 Hfun1 Hfvs1 Hfvs2
             HD Hbin Hfeq Henv Hinv Hnd Hin HD1 HD2 Hinc Hadd1 Hinc1 Hll1 Hadd2 Hinc2 Hll2.
    - inv Hadd2. inv Hll2. inv Hun2. simpl.
      assert
        (HB1 : forall j, j < k ->
                    preord_env_P_inj pr cenv
                                     (Union var
                                            (Union var (occurs_free (Efun B1 e)) (name_in_fundefs B1))
                                            (FunsFVs ζ1)) j σ1
                                     (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') /\
                    Funs_inv j (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') σ1 ζ1).
      { intros j leq. eapply IH'; (try now apply Hll1); (try now apply Hnd);
                      (try now apply Hadd1); try eassumption.
        - intros. eapply IHe; eauto. omega.
        - reflexivity.
        - eapply preord_env_P_inj_monotonic; [| eassumption]. omega.
        - eapply Funs_inv_monotonic. eassumption. omega.
        - reflexivity. } clear IH'.
      assert (HB2 : preord_env_P_inj pr cenv
                                     (Union var
                                            (Union var (occurs_free (Efun B1 e)) (name_in_fundefs B2))
                                            (FunsFVs ζ1)) k σ'
                                     (def_funs B1 B2 rho rho) (def_funs B1' B' rho' rho') /\
                    Funs_inv k (def_funs B1 B2 rho rho)
                             (def_funs B1' B' rho' rho') σ' ζ').
      { eapply IHB2; try (now apply Hnd);  try eassumption;
        try now (eapply Disjoint_Included_r; [| eassumption ]; normalize_bound_var; eauto with Ensembles_DB).
        - eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_fundefs_Fcons_Included.
        - eapply f_eq_subdomain_extend_not_In_S_r'.
          rewrite Union_commut. eassumption. intros Hc.
          eapply H9. now apply name_in_fundefs_bound_var_fundefs.
        - eapply Included_trans; [| eassumption]...
        - eapply Included_trans. 
          eapply Exp_Lambda_lift_free_set_Included. eassumption.
          (do 2 eapply Setminus_Included_preserv).
          eapply Included_trans; [ eassumption |]... } clear IHB2.
      destruct HB2 as [HB2env HB2inv].
      assert (Hval : preord_val pr cenv k (Vfun rho B1 v) (Vfun rho' B1' v)).
      { rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct Fundefs_lambda_lift_find_def with (B1 := B1)
          as (xs2 & ys' & e2 & S3 & S2 & Hfind1 & Hfind2 & Hnd1
                  & Hnd2 & Hlen1 & Hlen2 & Hinc1' & Hinc2' & Hinc3' & HD1' & HD2' & HD3' & Hll).
        eassumption. eassumption.
        eapply Disjoint_Included_r_sym. eapply Add_functions_LiftedFuns_Included. eassumption.
        eapply Union_Disjoint_l. eapply Disjoint_Included_r; [| now apply Hlf1 ]...
        eapply Disjoint_Included; [| | now apply Hf1]...
        eapply Add_functions_injective_subdomain_LiftedFuns; eassumption. eassumption.
        (* Various useful assertions *)
        assert (Hfree : Included _ (occurs_free e1)
                                 (Union var (FromList xs1)
                                        (Union var (name_in_fundefs B1) (occurs_free_fundefs B1)))).
        { eapply occurs_free_in_fun. apply find_def_correct. eassumption. }
        assert (Hbound : In _ (bound_var_fundefs B1) v /\
                         Included _ (FromList xs1) (bound_var_fundefs B1) /\
                         Included _ (bound_var e1) (bound_var_fundefs B1) ).
        { specialize (bound_var_fun_in_fundefs B1 v t1 xs1 e1 (find_def_correct _ _ _ _ _ Hf)).
          intros Hinc'. split. now eapply Hinc'; eauto.
          split; (eapply Included_trans; [| eassumption ])... }
        destruct Hbound as [Hb1 [Hb2 Hb3]].
        edestruct unique_bindings_fun_in_fundefs as [Hune1 [HunB1 [HunB2 [HunB3 [HunB4 [HunB5 HunB6]]]]]].
        exact (find_def_correct _ _ _ _ _ Hf). eassumption.
        assert (Heq : fvs0 = fvs). 
        { eapply Add_functions_fvs_eq; [| eassumption |]; try eassumption.
          eapply fun_in_fundefs_name_in_fundefs. now eapply find_def_correct; eauto. }
        edestruct setlist_length2 as [rho2' Hs']; [| eassumption | now eauto | ]. eauto.
        assert (HDim : Disjoint _ (image σ1
                                         (Union _
                                                (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ1))
                                                (name_in_fundefs B1)))
                                (Union _ S (Union _ (Union _ (bound_var e1) (FromList xs1))
                                                  (LiftedFuns ζ1)))).
        { eapply Disjoint_Included_l.
          eapply Add_functions_image_Included. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included; [| | now apply Him1 ].
          apply Union_Included. now eauto with Ensembles_DB.
          apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eapply Add_functions_LiftedFuns_Included.
          eassumption. now eauto with Ensembles_DB.
          apply image_monotonic. apply Setminus_Included_Included_Union.
          apply Included_Union_compat ; [| reflexivity ].
          apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
          eassumption. normalize_occurs_free...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| now apply Hf1 ].
          eapply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          apply Union_Disjoint_r. eapply Disjoint_sym...
          eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.          
          eapply Disjoint_Included_r.  eapply Add_functions_LiftedFuns_Included.
          eassumption. clear Hlf2 Hf2. now eauto with Ensembles_DB. }
        assert (Hsub : Included _ S1'' S).
        { eapply Included_trans. eassumption.
          eapply Add_functions_free_set_Included. eassumption. }
        assert (Hsub' : Included _ S3 S).
        { eapply Included_trans. eassumption. eassumption. }
        assert (HD' : Disjoint var (Union var (FromList xs1) (FromList ys'))
                               (Union _ (Union var S3 (bound_var e1)) (LiftedFuns ζ1))).
        { eapply Disjoint_Included_r. eapply Included_Union_compat.
          reflexivity.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          eapply Union_Disjoint_r. eapply Union_Disjoint_r.
          eapply Union_Disjoint_l. eapply Disjoint_sym.
          eapply Disjoint_Included ; [ | | now apply Hf1 ].
          apply Included_Union_preserv_l; eassumption. eassumption.
          eassumption.
          eapply Union_Disjoint_l. apply Disjoint_sym. eassumption.
          eapply Disjoint_Included ; [ | | now apply Hf1 ].
          apply Included_Union_preserv_l. eassumption.
          eapply Included_trans; eassumption.
          eapply Union_Disjoint_r. eapply Disjoint_sym.
          eapply Disjoint_Included_r ; [ | now apply Hlf1 ].
          apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eapply Included_trans. eassumption.
          eassumption. now eauto with Ensembles_DB.
          eapply Union_Disjoint_l. eapply Disjoint_sym.
          eapply Disjoint_Included ; [ | | now apply Hf1 ].
          apply Included_Union_preserv_l; eassumption. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eapply Included_trans.
          eassumption. now apply Hinc1. now eauto with Ensembles_DB. }
        assert (HDfuns : Disjoint _ (Funs ζ1) (Union _ (bound_var e1) (FromList xs1))).
        { eapply Disjoint_Included_l.
          eapply Add_functions_Funs_Included. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hfun1 ].
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_r; apply Disjoint_sym; eassumption. }
        assert (HDlfuns : Disjoint _ (LiftedFuns ζ1)
                                   (Union _ S1'' (Union _ (bound_var e1) (FromList xs1)))).
        { eapply Disjoint_Included_l. 
          eapply Add_functions_LiftedFuns_Included. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hlf1 ].
          apply Included_Union_compat. eassumption.
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_r. 
          eapply Disjoint_Included_r. now apply Hinc1.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [ | now apply Hf1 ].
          now eauto with Ensembles_DB. }
        assert (HDfunsfvs : Disjoint _ (FunsFVs ζ1) (Union _ (bound_var e1) (FromList xs1))).
        { eapply Disjoint_Included_l.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hfvs1 ].
          now eauto with Ensembles_DB. clear HD2.
          now eauto with Ensembles_DB. }
        (* Various useful assertions end *)
        do 3 eexists. split. eassumption.
        split. now eauto. 
        intros Hleq Hall. intros v1 c1 Hleq' Hstep.
        edestruct (HB1 j) as [Henvj Hinvj]. eassumption.
        edestruct Hinvj with (f := v) (vs2 := vs2) (j0 := 0)
          as [rho3 [rho3' [B3 [f3 [xs3 [e3 [vs3' [Hget3 [Hfind3 [Hgetl3 [Hset3 _]]]]]]]]]]].
        eassumption. rewrite def_funs_eq. reflexivity.
        eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
        eassumption. eassumption. eassumption. eassumption.
        rewrite def_funs_eq in Hget3;
          [| eapply fun_in_fundefs_name_in_fundefs; eapply find_def_correct; eassumption ].
        inv Hget3. rewrite Hfind3 in Hfind2. inv Hfind2.
        symmetry in Hset3. edestruct (@setlist_app val) as [rho3'' [Hset1 Hset2]].
        eassumption. rewrite <- Hlen. now eapply setlist_length_eq; eauto.
        { edestruct IHe with (rho := rho1') (rho' := rho3') (e := e1) (e' := e2)
            as [v2 [c2 [Hstep2 Hpre2]]]; try eassumption.  
          - (* Disjoint _ (image (σ1' <{ xs1 ++ fvs ~> xs1 ++ ys' }>) (occurs_free e1))
                          (Union _ S3 (bound_var e1)) *)
            eapply Disjoint_Included_l. eapply image_extend_lst_Included.
            + rewrite !app_length; congruence.
            + eapply Union_Disjoint_l.
              * eapply Disjoint_Included; [| | now apply HDim ].
                now eauto with Ensembles_DB.
                eapply image_monotonic. normalize_occurs_free.
                apply Setminus_Included_Included_Union.
                eapply Included_trans.
                apply Included_Union_compat. eassumption. reflexivity.
                rewrite FromList_app. now eauto 10 with Ensembles_DB.
              * rewrite FromList_app. now eauto with Ensembles_DB.
          - (*  Disjoint _ S3 (Union _ (bound_var e1) (occurs_free e1)) *)
            eapply Disjoint_Included_l. eassumption.
            eapply Disjoint_Included_r; [| now apply Hf1 ].
            eapply bound_var_occurs_free_in_fun_Included.
            apply find_def_correct. eassumption.
          - (*  Disjoint var (LiftedFuns ζ1') (bound_var  e1) *)
            now eauto with Ensembles_DB.
          - (* Disjoint var (Funs ζ1') (bound_var e1) *)
            now eauto with Ensembles_DB.
          - (* Disjoint var (FunsFVs ζ1') (bound_var e1) *)
            now eauto with Ensembles_DB.
          - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free;
             [| | eassumption ]; eauto.
            eapply find_def_correct. eassumption.
          - eapply binding_in_map_antimon.
            eapply Included_Union_compat. eassumption.
            eapply Add_functions_FunsFVs_Included_r. eassumption.
            intros x Hx. rewrite <- !Union_assoc in Hx.
            eapply binding_in_map_setlist; [| now eauto | ].
            eapply binding_in_map_def_funs. eassumption.
            normalize_occurs_free. inv Hx; eauto.
            inv H; eauto. inv H0; eauto. inv H; eauto.
            eapply Hin in H0; eauto.
          - (* preord_env_P_inj pr cenv (occurs_free e1) j (σ1' <{ xs1 ++ fvs ~> xs1 ++ ys' }>) rho1' rho3' *)
            rewrite extend_lst_app; [| reflexivity ].  
            eapply preord_env_P_inj_setlist_alt with (f := σ1 <{ fvs ~> ys' }>);
              [| eassumption | eassumption | eassumption | now eauto | | now eauto | now eauto ].
            + eapply preord_env_P_inj_resetlist; try eassumption.
              * (* Disjoint M.elt (image σ1' (Setminus var (occurs_free e1) (FromList xs1)))
                             (FromList ys') *)
                eapply Disjoint_Included; [ | | now apply HDim ].
                eapply Included_trans. eassumption. now eauto with Ensembles_DB.
                apply image_monotonic. normalize_occurs_free.
                apply Setminus_Included_Included_Union.
                eapply Union_Included. eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
                now eauto with Ensembles_DB.
              * now eauto.
              * eapply preord_env_P_inj_antimon. eassumption.
                normalize_occurs_free. apply Setminus_Included_Included_Union.
                eapply Union_Included. eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
                now eauto with Ensembles_DB.
            + (* Disjoint var (image (σ1' <{ fvs ~> ys' }>)
                                       (Setminus var (occurs_free e1) (FromList xs1))) 
                            (FromList xs1) *)
              eapply Disjoint_Included_l. eapply image_extend_lst_Included.
              now eauto. eapply Union_Disjoint_l.
              * eapply Disjoint_Included;[| | now apply HDim ].
                now eauto with Ensembles_DB.
                apply image_monotonic. normalize_occurs_free.
                do 2 apply Setminus_Included_Included_Union.
                eapply Union_Included. eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
                now eauto with Ensembles_DB.
              * (* Disjoint var (FromList ys') (FromList xs1) *)
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_r; [| now apply Hf1 ].
                eapply Included_Union_preserv_l. eassumption.
          - rewrite extend_lst_app; [| reflexivity ].
            eapply Funs_inv_setlist; eauto.
            + eapply Funs_inv_setlist_getlist_r; eauto. 
              * (* Disjoint var (LiftedFuns ζ1') (FromList ys') *)
                now eauto with Ensembles_DB.
              * eapply Disjoint_Included ; [ | | eapply HDim ].
                eapply Included_trans. eapply Included_trans.
                eassumption. eassumption. now eauto with Ensembles_DB.
                apply image_monotonic...
            + (* Disjoint var (Funs ζ1') (FromList xs1) *)
              now eauto with Ensembles_DB.
            + (* Disjoint var (LiftedFuns ζ1') (FromList xs1) *)
              now eauto with Ensembles_DB.
            + (* Disjoint var (FunsFVs ζ1') (FromList xs1) *)
              now eauto with Ensembles_DB.
            + eapply Disjoint_Included_l.
              * eapply image_extend_lst_Included. now eauto.
              * apply Union_Disjoint_l.
                eapply Disjoint_Included; [ | | now apply HDim ].
                now eauto with Ensembles_DB.
                apply image_monotonic...
                eapply Disjoint_Included; [| | now apply Hf1 ].
                eapply Included_Union_preserv_l. eassumption.
                eapply Included_trans; eassumption.
          - do 2 eexists; split; eauto. econstructor; try eassumption.
            + erewrite <- setlist_not_In; [| now eauto |].
              rewrite def_funs_eq. reflexivity.
              eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
              eassumption.
              intros Hc. eapply Hinc3' in Hc.
              assert (Hin' : In _ (name_in_fundefs B3) f3).
              { eapply fun_in_fundefs_name_in_fundefs.
                eapply find_def_correct; eassumption. }
              eapply Fundefs_lambda_lift_name_in_fundefs in Hin'; [| eassumption ].
              inv Hin'. eapply Hf1. constructor.
              now eauto. left. now apply name_in_fundefs_bound_var_fundefs.
              eapply Add_functions_LiftedFuns_Included in H; [| eassumption ].
              inv H. eapply Hlf1. now constructor; eauto.
              now inv H0; eauto.
            + erewrite getlist_app. reflexivity.
              erewrite getlist_setlist. reflexivity. eassumption. eassumption.
              erewrite getlist_setlist_Disjoint; try eassumption.
              eapply Disjoint_Included_l. eassumption.
              rewrite FromList_map_image_FromList.
              eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply HDim ].
              now eauto with Ensembles_DB.
              apply image_monotonic. normalize_occurs_free... } }
      split.
      + eapply preord_env_P_inj_set_not_In_P_r; [ eapply preord_env_P_inj_set_alt |].
        * eapply preord_env_P_inj_antimon. eassumption.
          now eauto 10 with Ensembles_DB.
        * eassumption.
        * intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ].
          inv Hc. eapply Him2. constructor; eauto. eapply image_monotonic; [| eassumption ].
          do 2 apply Setminus_Included_Included_Union.
          apply Union_Included. now eauto 6 with Ensembles_DB.
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
          eassumption. apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eassumption. normalize_occurs_free...
          normalize_bound_var...
          eapply H9. now eapply name_in_fundefs_bound_var_fundefs.
        * assert (Heqlf := lifted_name_eq _ _ _ _ _ H4).
          assert (Hinlf : In var (LiftedFuns ζ1) f'0) by (repeat eexists; eauto).
          eapply Add_functions_LiftedFuns_Included in Hinlf; [| eassumption ]. 
          intros Hc. eapply image_extend_Included' in Hc. inv Hc.
          eapply Add_functions_image_Included in H; [| eassumption ].
          inv H.
          eapply Him2. constructor; eauto. eapply image_monotonic; [| eassumption ].
          do 2 apply Setminus_Included_Included_Union.
          apply Union_Included. now eauto 6 with Ensembles_DB.
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
          eassumption. apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eassumption. normalize_occurs_free...
          inv Hinlf. now eauto. left. eapply Setminus_Included. eassumption.
          inv Hinlf. eapply Hlf2. constructor; eauto.
          right. normalize_bound_var. do 3 right. now apply name_in_fundefs_bound_var_fundefs.
          eapply Hf2 with (x := f'0). constructor; eauto.
          eapply Setminus_Included. eassumption.
          left. normalize_bound_var. do 3 right. now apply name_in_fundefs_bound_var_fundefs.
          inv H. inv Hinlf.
          eapply Hlf2. now constructor; eauto.
          eapply Hf2. constructor; eauto. eapply Setminus_Included. eassumption.
      + edestruct name_in_fundefs_find_def_is_Some as [ft1 [xs1 [e1 Hdef]]].
        apply Hinc. now left.
        edestruct Fundefs_lambda_lift_find_def with (B1 := B1)
          as (xs2 & ys' & e2 & S3 & S2 & Hfind1 & Hfind2 & Hnd1
                  & Hnd2 & Hlen1 & Hlen2 & Hinc1' & Hinc2' & Hinc3' & HD1' & HD2' & HD3' & Hll);
        try eassumption.
        eapply Disjoint_Included_r_sym. eapply Add_functions_LiftedFuns_Included. eassumption.
        eapply Union_Disjoint_l. eapply Disjoint_Included_r; [| now apply Hlf1 ]...
        eapply Disjoint_Included; [| | now apply Hf1]...
        eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
        assert (Hinc' : Included M.elt (FromList fvs0)
                                (Union var (occurs_free (Efun B1 e)) (FunsFVs ζ))).
        { eapply Included_trans with (s2 := FunsFVs ζ1).
          intros x Hx. now repeat eexists; eauto. 
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r. eassumption.
          normalize_occurs_free... }
        assert (HDfvs :  Disjoint var (FromList fvs0) (name_in_fundefs B1)).
        { eapply Disjoint_Included_l with (s3 := (FunsFVs ζ1)).
          eexists; eauto.
          eapply Disjoint_Included_l. eapply Add_functions_FunsFVs_Included_r.
          eassumption.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB. }
        assert (HDfvs' :  Disjoint var (FromList fvs0) (name_in_fundefs B2)).
        { eapply Disjoint_Included_l with (s3 := (FunsFVs ζ1)).
          eexists; eauto.
          eapply Disjoint_Included_l. eapply Add_functions_FunsFVs_Included_r.
          eassumption.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          rewrite !bound_var_fundefs_Fcons in Hfvs2, HD2.
          eapply Union_Disjoint_l; now eauto with Ensembles_DB. }
        assert (Ha1 : @map var var  σ1 fvs0 = map σ fvs0).
        { symmetry. eapply Add_functions_map_eq; eassumption. }
        assert (Ha2 : @map var var σ' fvs0 = map σ fvs0).
        { symmetry. eapply Add_functions_map_eq; eassumption. }
        edestruct (@binding_in_map_getlist val) with (xs := fvs0) as [vs Hget]; eauto.
        edestruct preord_env_P_inj_getlist_l as [vs2' [Hgetfvs' Hprefvs]]. now apply Henv.
        eassumption. eassumption.
        rewrite Hfeq in H4. rewrite extend_gss in H4. inv H4.
        rewrite Ha1, <- Ha2 in Hfind1. 
        eapply Funs_inv_set_lifted; (try now apply H4); eauto.
        * rewrite Ha2. 
          rewrite getlist_def_funs_Disjoint. eassumption.
          rewrite FromList_map_image_FromList.
          eapply Disjoint_Included; [| | now apply Him2 ].
          eapply Included_trans.
          eapply Fundefs_lambda_lift_name_in_fundefs. eassumption.
          eapply Included_trans. apply Included_Union_compat.
          apply name_in_fundefs_bound_var_fundefs.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          normalize_bound_var; now eauto 9 with Ensembles_DB.
          apply image_monotonic. eassumption.
        * congruence.
        * eapply Union_Disjoint_l; [| eassumption ].
          eapply Disjoint_Included_l.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eassumption.
        * clear Hlf2 Hf2. 
          eapply Disjoint_Included_l.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          now eauto with Ensembles_DB.
        * eapply Disjoint_Included_l with (s3 := image σ (Union var (FromList fvs0) (FunsFVs ζ'))).
          rewrite <- image_f_eq_subdomain. reflexivity.
          eapply f_eq_subdomain_antimon; [| eapply Add_functions_σ_eq; eauto ].
          eapply Included_trans.
          eapply Included_Union_compat. reflexivity.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          intros x Hx Hc. apply name_in_fundefs_bound_var_fundefs in Hc. inv Hx.
          eapply HD2. now constructor; eauto.
          inv H. eapply Hfvs2. now constructor; eauto.
          eapply HD2. now constructor; eauto.
          eapply Disjoint_Included_l. 
          apply image_monotonic. eapply Included_Union_compat. reflexivity.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          eapply Disjoint_Included_r. apply Included_Union_compat.
          eapply Included_trans. eapply Fundefs_lambda_lift_name_in_fundefs.
          eassumption. apply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          eapply Included_trans. eapply Included_trans; eassumption.
          eapply Add_functions_free_set_Included. eassumption.
          rewrite image_Union. 
          apply Union_Disjoint_l.
          eapply Disjoint_Included; [| | now apply Him1 ].
          now eauto 7 with Ensembles_DB. apply image_monotonic...
          eapply Disjoint_Included; [| | now apply Him1 ].
          now eauto 7 with Ensembles_DB.
          apply image_monotonic; normalize_occurs_free... 
        * eapply Disjoint_Included_r.
          eapply Included_trans.
          eapply Fundefs_lambda_lift_name_in_fundefs. eassumption.
          apply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          eapply Disjoint_Included_l.
          eapply Included_trans; eassumption.
          rewrite Union_assoc. apply Union_Disjoint_r.
          eapply Disjoint_Included_l.
          eapply Add_functions_free_set_Included. eassumption.
          clear Hf2...
          now eauto with Ensembles_DB.
        * intros Hc.
          eapply Add_functions_LiftedFuns_Included in Hc; [| eassumption ].
          inv Hc. eapply Hlf1. constructor; eauto.
          left. eapply Add_functions_free_set_Included; eassumption.
          inv H; eauto.
        * eapply preord_env_P_inj_antimon. eassumption.
          eapply Included_trans. eassumption.
          normalize_occurs_free...
        * left; eauto.
    - inv Hll2. inv Hadd2. simpl. rewrite Union_Empty_set_neut_r.
      split; eauto.
      eapply preord_env_P_inj_antimon. eassumption.
      eapply Included_trans.
      eapply Included_Union_compat. reflexivity.
      eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
      eassumption.
      eapply Included_Union_compat. reflexivity. eassumption.
      intros x Hin'. inv Hin'; eauto. inv H; eauto.
  Qed.

  Corollary Fundefs_lambda_lift_correct_cor k rho rho' B1 B1' σ ζ σ1 ζ1 S
        S1' S1'' S1''' fvs e:
    (* The IH for expressions *)
     (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
          (ζ : var -> option (var * fTag * list var)) 
          (σ : var -> var) (S : Ensemble var) (e' : exp) 
          (S' : Ensemble var),
        unique_bindings e ->
        Disjoint var (image σ (Union _ (occurs_free e) (FunsFVs ζ)))
                 (Union var S (Union _ (bound_var e) (LiftedFuns ζ))) ->
        Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
        Disjoint var (LiftedFuns ζ) (Union _ S (bound_var e)) ->
        Disjoint var (Funs ζ) (bound_var e) ->
        Disjoint var (FunsFVs ζ) (bound_var e) ->
        Disjoint _ (bound_var e) (occurs_free e) ->
        binding_in_map (Union _ (occurs_free e) (FunsFVs ζ)) rho ->
        preord_env_P_inj pr cenv (Union _ (occurs_free e) (FunsFVs ζ)) m σ rho rho' ->
        Funs_inv m rho rho' σ ζ ->
        Exp_lambda_lift ζ σ e S e' S' ->
        preord_exp pr cenv m (e, rho) (e', rho')) ->

     (* Unique bindings *)
     unique_bindings_fundefs B1 ->

     (* The image of σ is neither in the free set nor in the set of bound variables *)
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)))
              (Union var S (Union _ (bound_var_fundefs B1) (LiftedFuns ζ))) ->

     (* The free set is disjoint from the set of bound and free variables *)
     Disjoint var S (Union var (bound_var_fundefs B1) (occurs_free_fundefs B1)) ->

     (* The names of lifted functions is neither in the free set nor in the set of bound variables*) 
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B1)) ->

     (* The domain of ζ is disjoint with the bound variables *)
     Disjoint var (Funs ζ) (bound_var_fundefs B1) ->

     (* The free variables of the funs in ζ are disjoint from the bound variables *) 
     Disjoint var (FunsFVs ζ) (bound_var_fundefs B1) ->

     (* The free and bound variables are disjoint *)
     Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

     (* All the free variables are in the map *)
     binding_in_map (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)) rho ->

     (* The invariants hold in the initial environment *)
     preord_env_P_inj pr cenv (Union _ (occurs_free (Efun B1 e)) (FunsFVs ζ)) k σ rho rho' ->
     Funs_inv k rho rho' σ ζ ->
     
     NoDup fvs ->
     Included _ (FromList fvs) (occurs_free_fundefs B1) ->
     Disjoint var (FromList fvs) (bound_var_fundefs B1) ->
     
     Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
     Included _ S1'' S1' ->
     Fundefs_lambda_lift ζ1 σ1 B1 S1'' B1' S1''' ->
     
     (* The invariants hold in the final environment *)
     preord_env_P_inj pr cenv (Union _ (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B1)) (FunsFVs ζ1))
                      k σ1 (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') /\
     Funs_inv k (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') σ1 ζ1.
  Proof.
    intros. eapply Fundefs_lambda_lift_correct; eauto.
    reflexivity. reflexivity.
  Qed.

  Lemma Exp_lambda_lift_Ecase ζ σ x P S e S' :
    Exp_lambda_lift ζ σ (Ecase x P) S e S' ->
    exists P', e = Ecase (σ x) P' /\
          Forall2 (fun p p' : cTag * exp => fst p = fst p') P P'.
  Proof.
    revert S S' e; induction P; intros S S' e Hexp; inv Hexp.
    - eexists; eauto.
    - eapply IHP in H8. edestruct H8 as [P'' [Heq Hall]]. inv Heq.
      eexists; eauto.
  Qed.

  Lemma Exp_lambda_lift_correct k rho rho' ζ σ e S e' S' :
    (* The expression has unique bindings *)
    unique_bindings e ->
    (* The new free variable names are fresh *)
    Disjoint _ (image σ (Union _ (occurs_free e) (FunsFVs ζ)))
             (Union _ S (Union _ (bound_var e) (LiftedFuns ζ))) ->
    (* The fresh set is fresh *)
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    (* The new function names for lifted functions are fresh *)
    Disjoint _ (LiftedFuns ζ) (Union _ S (bound_var e)) ->
    (* The names of the (already defined) functions are disjoint from the bound variables of the expression *)
    Disjoint _ (Funs ζ) (bound_var e) ->
    (* The free variables of a function are disjoint from the bound variables of the expression *)
    Disjoint _ (FunsFVs ζ) (bound_var e) ->
    (* The bound variables of the expression are disjoint from the free variables *)
    Disjoint _ (bound_var e) (occurs_free e) ->
    (* All the free variables are in the environment *)
    binding_in_map (Union _ (occurs_free e) (FunsFVs ζ)) rho ->
    (* The environments are related *)
    preord_env_P_inj pr cenv (Union _ (occurs_free e) (FunsFVs ζ)) k σ rho rho' ->
    (* The invariant about lifted functions hold*)
    Funs_inv k rho rho' σ ζ ->
    (* e' is the translation of e*)
    Exp_lambda_lift ζ σ e S e' S' ->
    (* e and e' are related *)
    preord_exp pr cenv k (e, rho) (e', rho').
  Proof with now eauto with Ensembles_DB.
    revert e rho rho' ζ σ S e' S'; induction k as [k IHk] using lt_wf_rec1.
    induction e using exp_ind';
      intros rho rho' ζ σ S e' S' Hun Him Hf Hlf Hfun Hfvs HD Hin Henv Hinv Hll;
      inv Hll.
    - inv Hun. eapply preord_exp_const_compat.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free...
      + intros vs1 vs2 Hall. eapply IHe; [ eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Econstr in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. inv Hc. now eauto.
          eapply Hlf. now constructor; eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Econstr_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Econstr_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ]. 
          apply Union_Included; [| now eauto with Ensembles_DB ].
          rewrite Union_commut, Union_assoc.
          apply Included_Union_preserv_l.
          normalize_occurs_free. rewrite Union_assoc.
          rewrite Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eassumption.
          rewrite Setminus_Union_distr; normalize_occurs_free...
          rewrite preord_val_eq. constructor. reflexivity.
          now apply Forall2_Forall2_asym_included.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          rewrite Setminus_Union_distr; normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eassumption.
    - eapply preord_exp_case_nil_compat.
    - inv Hun. edestruct Exp_lambda_lift_Ecase as [P'' [Heq Hall]]; eauto. inv Heq.
      eapply preord_exp_case_cons_compat; eauto.
      + eapply Henv. left; eauto.
      + eapply IHe; eauto.
        * eapply Disjoint_Included; [| | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. normalize_occurs_free...
        * eapply Disjoint_Included_r; [ | now eapply Hf ].
          normalize_occurs_free. normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hlf ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfun ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfvs ].
          normalize_bound_var...
        * eapply Disjoint_Included; [ | | now eapply HD ].
          normalize_occurs_free... normalize_bound_var...
        * eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free...
      + assert (Hinc : Included _ S'0 S).
        { eapply Exp_Lambda_lift_free_set_Included; eauto. }
        eapply IHe0; eauto.
        * eapply Disjoint_Included; [| | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. normalize_occurs_free...
        * eapply Disjoint_Included; [ | eassumption | now eapply Hf ].
          normalize_occurs_free. normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hlf ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfun ].
          normalize_bound_var...
        * eapply Disjoint_Included_r; [ | now eapply Hfvs ].
          normalize_bound_var...
        * eapply Disjoint_Included; [ | | now eapply HD ].
          normalize_occurs_free... normalize_bound_var...
        * eapply binding_in_map_antimon; [| eassumption ].
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free...
    - inv Hun. eapply preord_exp_proj_compat.
      + eapply Henv. left. normalize_occurs_free...
      + intros vs1 vs2 Hall. eapply IHe; [ eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Eproj in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. inv Hc. now eauto.
          eapply Hlf. now constructor; eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Eproj_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Eproj_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ]. 
          apply Union_Included; [| now eauto with Ensembles_DB ].
          rewrite Union_commut, Union_assoc.
          apply Included_Union_preserv_l.
          normalize_occurs_free. rewrite Union_assoc.
          rewrite Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eassumption.
          rewrite Setminus_Union_distr; normalize_occurs_free...
          eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          rewrite Setminus_Union_distr; normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eassumption.
    - assert (Hinc : Included _ S'' S).
      { eapply Included_trans.
        now eapply Fundefs_Lambda_lift_free_set_Included; eauto.
        now eapply Add_functions_free_set_Included; eauto. }
      inv Hun. eapply preord_exp_fun_compat.
      repeat normalize_bound_var_in_ctx.
      edestruct Fundefs_lambda_lift_correct_cor; eauto; eauto with Ensembles_DB.
      + eapply Disjoint_Included_r; [| now apply Hf ].
        rewrite <- bound_var_Efun.
        now apply bound_var_occurs_free_fundefs_Efun_Included.
      + eapply Disjoint_Included; [| | now apply HD].
        normalize_occurs_free... now eauto with Ensembles_DB.
      + apply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD ].
        normalize_occurs_free... now eauto with Ensembles_DB. 
      + eapply IHe; eauto.
        * eapply Disjoint_Included_r.
          apply Included_Union_compat. eassumption.
          eapply Included_Union_compat. reflexivity.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          eapply Disjoint_Included_l. 
          eapply Add_functions_image_Included. eassumption.
          apply Union_Disjoint_l.
          eapply Disjoint_Included; [| | now apply Him ].
          now eauto 10 with Ensembles_DB.
          apply image_monotonic. rewrite Setminus_Union_distr.
          eapply Union_Included. normalize_occurs_free...
          apply Setminus_Included_Included_Union. normalize_occurs_free.
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
          eassumption. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs. 
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Included_r. now apply Setminus_Included.
          now eauto with Ensembles_DB.
        * eapply Disjoint_Included; [| | now apply Hf ].
          rewrite <- bound_var_Efun.
          now apply bound_var_occurs_free_Efun_Included.
          eassumption.
        * eapply Disjoint_Included_l.
          eapply Add_functions_LiftedFuns_Included. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_r. eapply Fundefs_Lambda_lift_free_set_Included.
          eassumption. now eauto with Ensembles_DB.
          now eauto with Ensembles_DB.
        * eapply Disjoint_Included_l.
          eapply Add_functions_Funs_Included. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l_sym; [| eassumption ].
          now apply name_in_fundefs_bound_var_fundefs.
        * eapply Disjoint_Included_l.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_sym.
          eapply Disjoint_Included; [ | | now apply HD ].
          normalize_occurs_free...  now eauto with Ensembles_DB.
        * eapply Disjoint_Included_r.
          now eapply occurs_free_Efun_Included.
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          eassumption. 
        * eapply binding_in_map_antimon;
          [| eapply binding_in_map_def_funs; eassumption ].
          apply Union_Included. rewrite Union_assoc.
          apply Included_Union_preserv_l. normalize_occurs_free. 
          rewrite Union_assoc, Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
          eapply Included_trans.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          normalize_occurs_free...
        * eapply preord_env_P_inj_antimon. eassumption.
          apply Union_Included.
          apply Included_Union_preserv_l. normalize_occurs_free. 
          rewrite Union_commut, Union_assoc, Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
          now eauto with Ensembles_DB.
    - intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct preord_env_P_inj_getlist_l as [vs' [Hgetl' Hprevs]]; try eassumption.
      normalize_occurs_free...
      assert (Hlen := Forall2_length _ _ _ Hprevs).
      edestruct Hinv with (vs2 := vs') (j := k-1)
        as [rho2 [rho2' [B2 [f2 [xs2 [e2 [vs2' [Hget [Hfind [Hgetl [Hset Hpre]]]]]]]]]]]; eauto.
      edestruct Hpre as [v2 [c2 [Hstep Hpre2]]]; try eassumption.
      omega. eapply Forall2_monotonic; [| eassumption ].
      intros. eapply preord_val_monotonic. eassumption. omega. omega.
      exists v2, (c2 + 1). split.
      simpl. econstructor. eassumption.
      rewrite list_append_map.
      erewrite getlist_app; try eassumption. reflexivity.
      eassumption. now eauto. eassumption.
      eapply preord_val_monotonic. eassumption. omega.
    - eapply preord_exp_app_compat.
      eapply Henv. now left; eauto.
      eapply Forall2_preord_var_env_map. eassumption.
      normalize_occurs_free...
    - inv Hun. eapply preord_exp_prim_compat.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free...
      + intros vs1 vs2 Hall. eapply IHe; [ eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Eprim in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. inv Hc. now eauto.
          eapply Hlf. now constructor; eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          now apply bound_var_occurs_free_Eprim_Included.
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * repeat normalize_bound_var_in_ctx...
        * eapply Disjoint_Included_r. now apply occurs_free_Eprim_Included.
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l ; [| now apply HD].
          normalize_bound_var... now apply Disjoint_Singleton_r.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ]. 
          apply Union_Included; [| now eauto with Ensembles_DB ].
          rewrite Union_commut, Union_assoc.
          apply Included_Union_preserv_l.
          normalize_occurs_free. rewrite Union_assoc.
          rewrite Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
        * eapply preord_env_P_inj_set_alt. 
          eapply preord_env_P_inj_antimon. eassumption.
          rewrite Setminus_Union_distr; normalize_occurs_free...
          eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          rewrite Setminus_Union_distr; normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eassumption.
    - eapply preord_exp_halt_compat.
      eapply Henv; left; eauto.
  Qed.

End Lambda_lifting_correct.