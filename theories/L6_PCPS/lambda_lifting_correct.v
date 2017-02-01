(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

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
  Definition Funs_inv k (rho rho' : env) (σ : var -> var)
             (ζ : var -> option (var * fTag * list var)) : Prop :=
    forall f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1 xs1 e1,
      ζ f = Some (f', ft', fvs) ->
      M.get f rho = Some (Vfun rho1 B1 f1) ->
      length vs1 = length vs2 ->
      find_def f1 B1 = Some (ft1, xs1, e1) ->
      Some rho1' = setlist xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
      exists rho2 rho2' B2 f2 xs2 e2 vs2',
        M.get (σ f') rho' = Some (Vfun rho2 B2 f2) /\
        find_def f2 B2 = Some (ft', xs2, e2) /\
        getlist (map σ fvs) rho' = Some vs2' /\
        Some rho2' = setlist xs2 (vs2 ++ vs2') (def_funs B2 B2 rho2 rho2) /\
        (j < k -> Forall2 (preord_val pr cenv j) vs1 vs2 ->
         preord_exp pr cenv j (e1, rho1') (e2, rho2')).
  
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
    ~ In _ (LiftedFuns ζ) x ->
    ~ In _ (FunsFVs ζ) x ->
    ~ In _ (image σ (Union _ (FunsFVs ζ) (LiftedFuns ζ))) y ->
    Funs_inv k rho rho' σ ζ ->
    Funs_inv k (M.set x v1 rho) (M.set y v2 rho') (σ {x ~> y}) ζ.
  Proof.
    intros Hnin1 Hnin2 Hnin4 Hnin5 Hinv f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1
           xs1 e1 Hget1 Hget2 Hlen Hdef Hset.
    assert (Heq : lifted_name ζ f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    assert (Hneq : f <> x)
      by (intros Hc; subst; eapply Hnin1; eexists; eauto).
    assert (Hneq' : f' <> x)
      by (intros Hc; subst; eapply Hnin2; repeat eexists; eauto).    
    rewrite M.gso in Hget2; eauto. 
    edestruct Hinv as
        [rho2 [rho2' [B2 [f2 [xs2 [e2 [vs2' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - rewrite extend_gso; eauto. rewrite M.gso; eauto.
      intros Hc; subst.
      eapply Hnin5. eexists; split; eauto. right. repeat eexists; eauto.
    - rewrite map_extend_not_In. rewrite getlist_set_neq. eassumption.
      intros Hc. eapply in_map_iff in Hc. destruct Hc as [x' [Heq' HIn]].
      eapply Hnin5. eexists; split; eauto. left. now repeat eexists; eauto.
      intros Hc. eapply Hnin4. repeat eexists. eassumption. eassumption.
  Qed.

  Lemma Funs_inv_setlist k rho rho' rho1 rho1' σ ζ vs1 vs2 xs ys :
    setlist xs vs1 rho = Some rho1 ->
    setlist ys vs2 rho' = Some rho1' ->
    Funs_inv k rho rho' σ ζ ->                        
    Disjoint _ (Funs ζ) (FromList xs) ->
    Disjoint _ (LiftedFuns ζ) (FromList xs) ->
    Disjoint _ (FunsFVs ζ) (FromList xs) ->
    Disjoint _ (image σ (Setminus _ (Union _ (FunsFVs ζ) (LiftedFuns ζ)) (FromList xs))) (FromList ys) ->
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
    - rewrite extend_lst_gso. erewrite <- setlist_not_In; eauto.
      intros Hc; subst. eapply HD4. constructor; eauto.
      eexists. split; eauto. constructor. right. now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
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
      left. repeat eexists; eassumption.
      intros Hc. eapply HD3. constructor; eauto.
      now repeat eexists; eauto.
      eapply Disjoint_Included_l; [| eassumption ].
      repeat eexists; eassumption.
  Qed.

  Lemma get_reset_lst σ xs ys (vs : list val) rho rho' z  : 
    setlist ys vs rho = Some rho' ->
    getlist (map σ xs) rho = Some vs ->
    ~ In _ (FromList ys) (σ z) ->
    length xs = length ys ->
    NoDup xs -> NoDup ys ->
    M.get (σ z) rho = M.get (σ <{ xs ~> ys }> z) rho'.
  Proof with now eauto with Ensembles_DB.
    revert σ ys vs rho' rho. induction xs as [| x xs IHxs ];
      intros σ ys vs rho' rho Hset Hget HD Hlen Hnd1 Hnd2.
    - destruct ys; try discriminate.
      inv Hget. inv Hset. reflexivity.
    - destruct ys; try discriminate. simpl in *.
      inv Hlen. destruct vs; try discriminate.
      destruct (setlist ys vs rho) eqn:Hset'; try discriminate.
      destruct (M.get (σ x) rho) eqn:Hget'; try discriminate.
      destruct (getlist (map σ xs) rho) eqn:Hgetl; try discriminate.
      inv Hget. inv Hset. inv Hnd1. inv Hnd2. rewrite !FromList_cons in HD.
      assert (H : M.get ((σ <{ xs ~> ys }> {x ~> e}) z) (M.set e v t) =
                  M.get (σ <{ xs ~> ys }> z) t).
      { destruct (peq x z); subst.
        - rewrite extend_gss, M.gss.
          rewrite extend_lst_gso; eauto.
          erewrite <- setlist_not_In. symmetry. eassumption.
          eassumption.
          intros Hc. eapply HD. right; eauto.
        - rewrite extend_gso; eauto. rewrite M.gso. reflexivity.
          destruct (in_dec peq z xs).
          + edestruct (extend_lst_gss σ) as [y' [Hin' Heq']]; eauto.
            intros Hc. congruence.
          + rewrite extend_lst_gso; eauto.
            intros Hc. subst. eapply HD. constructor; eauto. }
      rewrite H.
      erewrite <- IHxs; eauto.
  Qed.


  Lemma Funs_inv_setlist_getlist_r k rho rho' rho'' σ ζ vs xs ys :
    setlist ys vs rho' = Some rho'' ->
    getlist (map σ xs) rho' = Some vs ->
    Funs_inv k rho rho' σ ζ ->
    NoDup ys -> NoDup xs ->
    length xs = length ys ->
    Disjoint _ (image σ (Union _ (FunsFVs ζ) (LiftedFuns ζ))) (FromList ys) ->
    Funs_inv k rho rho'' (σ <{xs ~> ys}>) ζ.
  Proof.
    intros Hset1 Hgetl Hinv Hnd1 Hnd2 Hlen HD1  f f' ft' fvs vs1'
           vs2' j ft1  rho2 rho2' B1 f1 xs1 e1 Hget1 Hget2 Hlen' Hdef Hset.
    assert (Heq : lifted_name ζ f = Some f')
      by (unfold lifted_name; rewrite Hget1; simpl; eauto).
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl' [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - erewrite <- get_reset_lst; eauto.
      intros Hc; subst. eapply HD1. constructor; eauto.
      eexists; split; eauto. right. repeat eexists; eauto.
    - erewrite <- getlist_reset_lst; try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply image_monotonic. 
      intros x Hin. left. repeat eexists; eauto.
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
    rewrite <- H2. eassumption.
    rewrite H2. eassumption.
    rewrite H2. eassumption.
  Qed.  
  
  Lemma Funs_inv_set_lifted k rho rho' rho1 rho2 B1 B1' ζ σ v v' ft ft' xs xs' ys fvs e1 e1' vs :
    (* B1' is the lifted version of B1, thus it satisfies the following *)
    preord_val pr cenv k (Vfun rho1 B1 v) (Vfun rho2 B1' v) ->

    find_def v B1 = Some (ft, xs, e1) ->
    find_def v' B1' = Some (ft', xs ++ ys, e1') ->
    find_def v B1' = Some (ft, xs', Eapp v' ft' (xs' ++ (map σ fvs))) ->  
    NoDup xs' ->
    length xs = length xs' ->
    length ys = length fvs ->
    Included _ (name_in_fundefs B1) (name_in_fundefs B1') ->
    (* the free variables have not been shadowed between the time of the function
       definition and the application *)
    getlist (map σ fvs) rho' = Some vs ->
    getlist (map σ fvs) rho2 = Some vs ->

    (* The names of the free function vars are disjoint from the original function names *)
    Disjoint _ (Union _ (FunsFVs ζ) (FromList fvs)) (bound_var_fundefs B1) ->
    (* The names of the LiftedFuns are disjoint from the original function names *)
    Disjoint _ (LiftedFuns ζ) (bound_var_fundefs B1) ->
    (* Τhe image of σ on the lifted functions is disjoint form the original names *)
    Disjoint _ (image σ (LiftedFuns ζ)) (name_in_fundefs B1) ->
    (* Τhe image of σ on the free variables is disjoint form the original and the lifted names and [xs'] *)
    Disjoint _ (image σ (Union _ (FromList fvs) (FunsFVs ζ))) (Union _ (name_in_fundefs B1') (FromList xs')) ->
       
    Disjoint _ (FromList xs') (name_in_fundefs B1') ->
    Disjoint _ (FunsFVs ζ) (name_in_fundefs B1') ->
    ~ In _ (LiftedFuns ζ) v' -> ~ In _ (FromList fvs) v' ->
    ~ In _ (image σ (LiftedFuns ζ)) v' ->

    (* the invariant holds for the initial environments *)
    Funs_inv k rho rho' σ ζ ->

    Funs_inv k (M.set v (Vfun rho1 B1 v) rho)
             (M.set v' (Vfun rho2 B1' v')
                    (M.set v (Vfun rho2 B1' v) rho'))
             (σ {v ~> v} {v' ~> v'}) (ζ {v ~> Some (v', ft', fvs)}).
  Proof.
    intros Hval Hf1 Hf2 Hf3 Hnd Hlen1 Hlen2 Hinc Hgetfvs Hgetfvs1 HD1 HD2 HD3 HD4 HD5 HD6
           Hnin1 Hnin2 Hnin3 Hinv.
    intros g g' t fvsg vs1 vs2 j gt1 rho3 rho4 B g1 xs1 e2 Happ Hget Hlen Hdef Hset.
    assert (Heq1 := lifted_name_eq _ _ _ _ _ Happ).
    destruct (peq g v).
    - subst. rewrite extend_gss in Happ. inv Happ.
      rewrite M.gss in Hget; inv Hget. rewrite Hf1 in Hdef. inv Hdef.
      edestruct (@setlist_length3 val) with (xs := xs1 ++ ys) (vs := vs2 ++ vs) as [rho4' Hset4'].
      rewrite !app_length. erewrite setlist_length_eq; [| now eauto ].
      erewrite <- (getlist_length_eq _ vs); [| eassumption ].
      rewrite map_length. congruence.
      do 7 eexists. repeat split; eauto.
      + rewrite extend_gss. rewrite M.gss; eauto.
      + rewrite map_extend_not_In; eauto. rewrite map_extend_not_In; eauto.
        rewrite !getlist_set_neq; eauto.
        intros Hc.
        assert (Hin : In _ (image σ (FromList fvsg)) g1).  
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD4. constructor. eapply image_monotonic; [| eassumption ].
        now eauto with Ensembles_DB.
        left. eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
        intros Hc.
        assert (Hin : In _ (image σ (FromList fvsg)) g').
        { rewrite <- FromList_map_image_FromList. eassumption. }
        eapply HD4. constructor. eapply image_monotonic; [| eassumption ]...
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
        specialize (Hpre5 v1 c1 Heq' Hstep).
        edestruct Hpre5 as [v2 [c2 [Hstep' Hval']]]. inv Hstep'.        
        erewrite <- setlist_not_In in H2; [| now eauto |].
        rewrite def_funs_eq in H2. inv H2. rewrite Hf2 in H5; inv H5.
        edestruct (@setlist_app val) as [rho6 [Hset6 Hset6']]. eassumption.
        erewrite setlist_length_eq; now eauto.
        assert (Heq'' : vs0 = vs2 ++ vs).
        { edestruct (@app_getlist val) as [vs1' [vs2' [Hget1 [Hget2 Heq3]]]]; subst.
          eassumption. subst.
          erewrite getlist_setlist in Hget1; [| now eauto | now eauto ].
          inv Hget1. f_equal; eauto.
          erewrite getlist_setlist_Disjoint in Hget2; [| | now eauto].
          rewrite getlist_def_funs_Disjoint in Hget2.
          rewrite Hget2 in Hgetfvs1. inv Hgetfvs1. reflexivity.
          rewrite FromList_map_image_FromList.
          eapply Disjoint_Included ;[ | | now apply HD4 ]...
          now eauto with Ensembles_DB.
          apply image_monotonic. now eauto with Ensembles_DB.
          eapply Disjoint_sym. eapply Disjoint_Included ;[ | | now apply HD4 ].
          now eauto with Ensembles_DB.
          rewrite FromList_map_image_FromList.
          apply image_monotonic. now eauto with Ensembles_DB. } 
        subst.
        rewrite Hset4' in H8. inv H8. do 2 eexists; eauto.
        eapply fun_in_fundefs_name_in_fundefs. apply find_def_correct.
        eassumption.
        intros Hc. eapply HD5. constructor; eauto.
        eapply fun_in_fundefs_name_in_fundefs.
        apply find_def_correct. eassumption.
    - rewrite lifted_name_extend in Heq1.
      rewrite extend_gso in Happ; rewrite extend_gso in Heq1; eauto.
      subst. rewrite M.gso in Hget; eauto.
      assert (Hnin'' : ~ In _ (FromList fvsg) v).
      { intros Hc. eapply HD1. constructor. left; eauto. 
        repeat eexists; eauto. apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs. apply find_def_correct.
        eassumption. }      
      edestruct Hinv
        as [rho5 [rho6 [B3 [f3 [xs3 [e3 [vs3' [Hget3 [Hfind3 [Hgetl3 [Hset3 Hpre3]]]]]]]]]]];
        try eassumption.
      do 7 eexists.
      split; [| split; [| split; [| split ]]]; try eassumption.
      + rewrite extend_gso. rewrite extend_gso. rewrite !M.gso. eassumption.
        * intros Hc. eapply HD3. constructor.
          eexists; split; eauto. now repeat eexists; eauto.
          eapply fun_in_fundefs_name_in_fundefs.
          eapply find_def_correct. eassumption.
        * intros Hc. eapply Hnin3.
          eexists; split; eauto. now repeat eexists; eauto.
        * intros Hc; subst. eapply HD2. constructor.
          now repeat eexists; eauto.
          eapply name_in_fundefs_bound_var_fundefs. eapply fun_in_fundefs_name_in_fundefs.
          eapply find_def_correct. eassumption.
        * intros Hc; subst. eapply Hnin1.
          now repeat eexists; eauto.
      + rewrite map_extend_not_In; eauto.
        rewrite map_extend_not_In; eauto.
        rewrite !getlist_set_neq. eassumption.
        * intros Hc. 
          assert (Hin : In _ (image σ (FromList fvsg)) v). 
          { rewrite <- FromList_map_image_FromList. eassumption. }
          eapply HD4. constructor.
          eapply image_monotonic; [| eassumption ].
          intros x Hl. repeat eexists. right. now repeat eexists; eauto.
          left. eapply fun_in_fundefs_name_in_fundefs.
          apply find_def_correct. eassumption.
        * intros Hc. 
          assert (Hin : In _ (image σ (FromList fvsg)) v'). 
          { rewrite <- FromList_map_image_FromList. eassumption. }
          eapply HD4. constructor.
          eapply image_monotonic; [| eassumption ].
          intros x Hl. repeat eexists. right. now repeat eexists; eauto.
          left. eapply fun_in_fundefs_name_in_fundefs.
          apply find_def_correct. eassumption.
        * intros Hc. eapply HD6. constructor; eauto.
          now repeat eexists; eauto.
          eapply fun_in_fundefs_name_in_fundefs.
          eapply find_def_correct. eassumption.
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


  Lemma Setminus_Setminus_Included {A} S1 S2 S3 :
    Decidable S3 ->
    Included A (Setminus _ S1 (Setminus _ S2 S3))
             (Union _ (Setminus _ S1 S2) S3).
  Proof.
    intros HD x H1. inv H1. destruct HD. destruct (Dec x); eauto.
    left; constructor; eauto. intros Hc.
    eapply H0; constructor; eauto.
  Qed.
    

  Lemma Add_functions_image_Included P B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Included _ (image σ' P)
             (Union _ (image σ (Setminus _ P (Union _ (name_in_fundefs B) (Setminus _ S S'))))
                                   (Union _ (name_in_fundefs B) (Setminus _ S S'))).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. revert P. induction Hadd; intros P.
    - eapply Included_trans. now eapply image_extend_Included'.
      eapply Union_Included.
      eapply Included_trans. now eapply image_extend_Included'. 
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Included_trans. eapply IHHadd.
      simpl. eapply Included_Union_compat.
      rewrite !Setminus_Union. eapply image_monotonic.
      eapply Included_Setminus_compat. reflexivity.
      apply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply Setminus_Setminus_Included.
      now eauto with typeclass_instances.
      now eauto with Ensembles_DB.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Included_Union_preserv_r. apply Included_Setminus_compat.
      reflexivity. now eauto with Ensembles_DB.
      simpl. do 2 apply Included_Union_preserv_r.
      apply Singleton_Included. constructor.
      eapply Add_functions_free_set_Included; now eauto.
      intros Hc; inv Hc; eauto.
    - simpl. rewrite Setminus_Same_set_Empty_set at 1.
      rewrite Setminus_Same_set_Empty_set at 1.
      repeat rewrite Union_Empty_set_neut_r at 1.
      rewrite Setminus_Empty_set_neut_r. reflexivity.
  Qed.
  
  Lemma Add_functions_LiftedFuns_Included_r B fvs σ ζ S σ' ζ' S' :
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

    Lemma image'_Union {A B} f S1 S2 :
    Same_set B (image' f (Union A S1 S2))
             (Union _ (image' f S1) (image' f S2)).
  Proof.
    split; intros x H.
    - destruct H as [y [Hin Heq]].
      inv Hin; [ left | right ]; eexists; eauto.
    - inv H; destruct H0 as [y [Hin Heq]]; eexists; split; eauto.
  Qed.

  Lemma image'_Singleton_is_Some {A B} f x y :
    f x = Some y ->
    Same_set B (image' f (Singleton A x)) (Singleton B y).
  Proof.
    split; intros z H'.
    - destruct H' as [w [Hin Heq ]].
      inv Hin. rewrite Heq in H; inv H. eauto.
    - inv H'. eexists; split; eauto.
  Qed.

  Lemma image'_extend_is_Some {B} f x y S :
    Included B (image' (f {x ~> Some y}) S)
             (Union _ (image' f (Setminus _ S (Singleton _ x))) (Singleton _ y)).
  Proof.
    intros z H'. 
    destruct H' as [w [Hin Heq ]].
    destruct (peq x w); subst.
    - rewrite extend_gss in Heq. inv Heq.
      eauto.
    - rewrite extend_gso in Heq; eauto.
      left. eexists; split; eauto.
      constructor; eauto. intros Hc; inv Hc; congruence.
  Qed.

  Lemma image'_extend_is_Some_In_P {B} f x y S :
    In _ S x ->
    Same_set B (image' (f {x ~> Some y}) S)
             (Union _ (image' f (Setminus _ S (Singleton _ x))) (Singleton _ y)).
  Proof.
    intros Hin. split.
    - now apply image'_extend_is_Some; eauto.
    - intros z H'. inv H'.
      + destruct H as [w [Hin' Heq]].
        destruct (peq x w); subst.
        * inv Hin'. exfalso; eauto.
        * inv Hin'. eexists; split; eauto.
          rewrite extend_gso; eauto.
      + inv H. eexists; split; eauto.
        rewrite extend_gss; eauto.
  Qed.
  
  Lemma image'_extend_is_Some_not_In_P {B} f x y S :
    ~ In _ S x ->
    Same_set B (image' (f {x ~> Some y}) S) (image' f S).
  Proof.
    intros Hnin. split.
    - intros z H'. 
      destruct H' as [w [Hin Heq ]].
      destruct (peq x w); subst.
      + rewrite extend_gss in Heq. inv Heq. exfalso; eauto.
      + rewrite extend_gso in Heq; eauto.
        eexists; split; eauto.
    - intros z [w [Hin Heq]]. 
      destruct (peq x w); subst.
      + exfalso; eauto.
      + eexists; split; eauto. rewrite extend_gso; eauto.
  Qed.

  Lemma image'_monotonic {A B} f S1 S2 :
    Included A S1 S2 ->
    Included B (image' f S1) (image' f S2).
  Proof.
    intros Hc x [y [Hin Heq]].
    eexists; split; eauto.
  Qed.

  Lemma image'_Empty_set {A B} f:
    Same_set B (image' f (Empty_set A)) (Empty_set B).
  Proof.
    split. now intros x [y [Hin Heq]]; inv Hin.
    now eauto with Ensembles_DB.
  Qed.

  Lemma Setminus_Setminus_Same_set A S1 S2 S3 :
    Decidable S3 ->
    Included _ S3 S1 ->
    Same_set A (Setminus A S1 (Setminus A S2 S3))
             (Union A (Setminus A S1 S2) S3).
  Proof.
    intros Hd Hin. split.
    now apply Setminus_Setminus_Included.
    destruct Hd. intros x H. destruct (Dec x).
    - constructor. now eapply Hin.
      intros Hc; inv Hc; eauto.
    - inv H.
      + inv H1. constructor; eauto. intros Hc.
        inv Hc; eauto.
      + exfalso; eauto.
  Qed.

  Lemma image'_feq_subdomain {A B} (f1 f2 : A -> option B) S :
    f_eq_subdomain S f1 f2 ->
    Same_set B (image' f1 S) (image' f2 S).
  Proof.
    intros Heq; split; intros x [y [Hin Heq']]; eexists; split; eauto.
    now rewrite <- Heq; eauto. now rewrite Heq; eauto.
  Qed.

  
  Lemma Add_functions_lifted_name_Same_set B fvs σ ζ S σ' ζ' S' P :
    unique_bindings_fundefs B ->
    Disjoint _ P (name_in_fundefs B) ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image' (lifted_name ζ') (Union _ P (name_in_fundefs B)))
             (Union _ (image' (lifted_name ζ) P) (Setminus _ S S')).
  Proof with now eauto with Ensembles_DB.
    intros Hun HD Hadd. revert P HD; induction Hadd; intros P HD.
    - inv Hun. rewrite lifted_name_extend. simpl.
      rewrite image'_extend_is_Some_In_P.
      rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
      rewrite (Setminus_Disjoint (name_in_fundefs B)).
      rewrite IHHadd, Setminus_Setminus_Same_set. 
      rewrite Setminus_Disjoint, Union_assoc...
      now eauto with typeclass_instances.
      apply Singleton_Included.
      now eapply Add_functions_free_set_Included; eauto.
      eassumption.
      eapply Disjoint_Included; [| | now apply HD ]...
      eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.
      eapply Disjoint_Singleton_r. eassumption.
      now eauto with Ensembles_DB.
    - simpl. rewrite Union_Empty_set_neut_r, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r...
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

  Lemma domain_extend_is_Some_Same_set {A} f x (y : A) :
    Same_set _ (domain (f {x ~> Some y})) (Union _ (domain f) (Singleton _ x)).
  Proof. 
    split; intros z H.
    - destruct H as [w H'].
      destruct (peq x z); subst; eauto.
      rewrite extend_gso in H'; eauto. left.
      eexists; eauto.
    - destruct (peq x z); subst; eauto.
      + eexists. rewrite extend_gss; eauto.
      + inv H. destruct H0.
        eexists. rewrite extend_gso; eauto.
        inv H0; congruence.
  Qed.

  Lemma Add_functions_Funs_Same_set B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (Funs ζ') (Union _ (Funs ζ) (name_in_fundefs B)).
  Proof with now eauto with Ensembles_DB.
    intros Hadd. induction Hadd.
    - unfold Funs. rewrite lifted_name_extend, domain_extend_is_Some_Same_set, IHHadd.
      simpl. unfold Funs...
    - rewrite Union_Empty_set_neut_r...
  Qed.

  Lemma Add_functions_LiftedFuns_Included_l B fvs σ ζ S σ' ζ' S' :
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    unique_bindings_fundefs B ->
    Disjoint _ (Funs ζ) (name_in_fundefs B) ->
    Included _ (LiftedFuns ζ)  (LiftedFuns ζ').
  Proof with now eauto  with Ensembles_DB.
    intros Hadd Hun HD. unfold LiftedFuns.
    rewrite Add_functions_Funs_Same_set with (ζ' := ζ'); eauto.
    rewrite Add_functions_lifted_name_Same_set; eauto.
    now eauto with Ensembles_DB.
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
    f_eq_subdomain (Complement _ (Union _ (name_in_fundefs B) (Setminus _ S S'))) σ σ'.
  Proof.
    intros Hadd. induction Hadd; simpl.
    - eapply f_eq_subdomain_extend_not_In_S_r.
      intros Hc; apply Hc.
      eapply Singleton_Included. right. constructor.
      eapply Add_functions_free_set_Included; eassumption.
      intros Hc'. inv Hc'. now eauto. now eauto.
      eapply f_eq_subdomain_extend_not_In_S_r.
      intros Hc; apply Hc. now eauto.
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
      eapply Add_functions_LiftedFuns_Included_r in Hin'; [| eassumption ].
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
    Disjoint _ (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S'))->
    map σ l = map σ' l.
  Proof.
    intros Hadd HD. induction l; eauto.
    simpl. rewrite FromList_cons in HD.
    erewrite Add_functions_σ_eq; [| eassumption |].
    rewrite IHl. reflexivity.
    now eauto with Ensembles_DB.
    intros Hc. eapply HD. constructor; eauto.
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

  (* Lemma Add_functions_injective_subdomain P B fvs σ ζ S σ' ζ' S'  : *)
  (*   Add_functions B fvs σ ζ S σ' ζ' S' -> *)
  (*   unique_bindings_fundefs B -> *)
  (*   injective_subdomain (Setminus _ P (name_in_fundefs B)) σ -> *)
  (*   Disjoint _ (image σ (Setminus _ P (name_in_fundefs B))) (name_in_fundefs B) -> *)
  (*   injective_subdomain P σ'. *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   intros Hadd. revert P; induction Hadd; intros P Hun Hinj HD. *)
  (*   - inv Hun. eapply injective_subdomain_extend'. *)
  (*     eapply IHHadd. eassumption. now rewrite Setminus_Union. *)
  (*     rewrite Setminus_Union... *)
  (*     intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ]. *)
  (*     inv Hc. eapply HD. *)
  (*     constructor; eauto. rewrite Setminus_Union in H0; eassumption. *)
  (*     left; eauto. *)
  (*     eapply H6. eapply name_in_fundefs_bound_var_fundefs. eassumption. *)
  (*   - simpl in Hinj. now rewrite Setminus_Empty_set_neut_r in Hinj. *)
  (* Qed. *)
  
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
    Disjoint positive (FromList l) (Union _ (name_in_fundefs B) (Setminus _ S S')) ->
    map f' l = map f l.
  Proof with now eauto with Ensembles_DB.
    intros Hadd HD. induction Hadd.
    - rewrite !map_extend_not_In. eapply IHHadd...
      intros Hc. eapply HD; eauto.
      constructor; eauto. left. left; eauto.
      intros Hc. eapply HD; eauto.
      constructor; eauto. right. constructor; eauto.
      eapply Add_functions_free_set_Included; eassumption.
      intros Hc'; inv Hc'; eauto.
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

  Lemma preord_env_P_inj_extend_not_In_P_r k P σ rho1 rho2 x y :
    preord_env_P_inj pr cenv P k σ rho1 rho2 -> 
    ~ In _ P x ->
    preord_env_P_inj pr cenv P k (σ {x ~> y}) rho1 rho2.
  Proof.
    intros Hpre Hnin z Hp v1 Hget.
    edestruct Hpre as [v2 [Hget2 Hpre2]]; eauto.
    repeat eexists; eauto. rewrite extend_gso; eauto.
    intros Hc. subst. contradiction.
  Qed.

  Lemma preord_env_P_inj_set_extend_not_In_P_r P k f rho1 rho2 x y v :
    preord_env_P_inj pr cenv P k f rho1 rho2 ->
    ~ In _ P x ->
    ~ In _ (image f P) y ->
    preord_env_P_inj pr cenv P k (f {x ~> y}) rho1 (M.set y v rho2).
  Proof.
    intros Henv Hnin Hnin' z Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto.
    rewrite extend_gso, M.gso. eassumption.
    intros Hc; subst. eapply Hnin'. now eexists; eauto.
    intros Hc. subst. contradiction.
  Qed.


  Lemma lifted_name_f_eq_subdomain S f1 f2 :
    f_eq_subdomain S f1 f2 ->
    f_eq_subdomain S (lifted_name f1) (lifted_name f2).
  Proof.
    intros Heq x Hin. unfold lifted_name. simpl; rewrite Heq; eauto.
  Qed.

  Lemma Add_functions_name_in_fundefs B1 fvs σ ζ S σ' ζ' S' :
    unique_bindings_fundefs B1 ->
    Add_functions B1 fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image' (lifted_name ζ') (name_in_fundefs B1))
             (Setminus var S S').
  Proof with now eauto with Ensembles_DB.
    intros Hun Hadd. induction Hadd; simpl in *.
    - rewrite lifted_name_extend, image'_Union, image'_Singleton_is_Some;
      [| now rewrite extend_gss; eauto ]. inv Hun.
      rewrite image'_extend_is_Some_not_In_P.
      rewrite IHHadd, Setminus_Setminus_Same_set; eauto.
      now eauto with Ensembles_DB.
      now eauto with typeclass_instances.
      eapply Singleton_Included.
      now eapply Add_functions_free_set_Included; eauto.
      intros Hc. eapply H6.
      now apply name_in_fundefs_bound_var_fundefs.
    - rewrite image'_Empty_set, Setminus_Same_set_Empty_set... 
  Qed.

    
  Lemma Fundefs_lambda_lift_name_in_fundefs_r B1 B2 σ ζ1 ζ2 S S' :
    Fundefs_lambda_lift ζ1 σ B1 S B2 S' ->
    unique_bindings_fundefs B1 ->
    f_eq_subdomain (name_in_fundefs B1) ζ1 ζ2 ->
    Same_set _ (name_in_fundefs B2)
             (Union _ (name_in_fundefs B1) (image' (lifted_name ζ2) (name_in_fundefs B1))).
  Proof with now eauto with Ensembles_DB.
    intros Hfuns Hun Hfeq. induction Hfuns; simpl in *.
    - inv Hun. rewrite IHHfuns; eauto. rewrite image'_Union.
      rewrite !(image'_feq_subdomain (lifted_name ζ2) (lifted_name ζ)).
      rewrite image'_Singleton_is_Some; [| erewrite lifted_name_eq; eauto ]...
      apply lifted_name_f_eq_subdomain. symmetry.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
      apply lifted_name_f_eq_subdomain. symmetry.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
      eapply f_eq_subdomain_antimon; [| eassumption ]...
    - rewrite image'_Empty_set...
  Qed.

  Lemma Add_functions_lifted_name_Disjoint_Same_set B fvs σ ζ S σ' ζ' S' P :
    Disjoint _ P (Union _ S (name_in_fundefs B)) ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image' (lifted_name ζ') P)
             (image' (lifted_name ζ) P).
  Proof with now eauto with Ensembles_DB.
    intros HD Hadd. induction Hadd.
    - rewrite lifted_name_extend. rewrite image'_extend_is_Some_not_In_P.
      eapply IHHadd. simpl in *...
      intros Hc. eapply HD. constructor; eauto.
      right; left; eauto.
    - reflexivity.
  Qed.
  
  Corollary Add_functions_Fundefs_lambda_lift_name_in_fundefs
        B1 B2 fvs σ ζ S σ1 σ2 ζ1 ζ2 S' S1 S2 :
    Add_functions B1 fvs σ ζ S σ1 ζ1 S' ->
    Fundefs_lambda_lift ζ2 σ2 B1 S1 B2 S2 ->
    f_eq_subdomain (name_in_fundefs B1) ζ1 ζ2 ->
    unique_bindings_fundefs B1 ->
    Same_set _ (name_in_fundefs B2)
             (Union _ (name_in_fundefs B1) (Setminus var S S')).
  Proof.
    intros. rewrite Fundefs_lambda_lift_name_in_fundefs_r; eauto.
    rewrite Add_functions_name_in_fundefs; eauto. reflexivity.
    symmetry; eauto.
  Qed.


  Lemma Add_functions_image_LiftedFuns_Same_set B fvs σ ζ S σ' ζ' S' :
    Disjoint _ S (name_in_fundefs B) ->
    unique_bindings_fundefs B ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image σ' (Setminus _ S S'))
             (Setminus _ S S').
  Proof with now eauto with Ensembles_DB.
    intros HD Hun Hadd. induction Hadd; simpl.
    - inv Hun.
      rewrite image_extend_In_S, image_extend_not_In_S, !Setminus_Setminus_Same_set,
      !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite !(Setminus_Disjoint (Setminus var S S')).
      rewrite IHHadd; eauto. reflexivity.
      now eauto with Ensembles_DB.
      eapply Disjoint_Singleton_r. now intros Hc; inv Hc; eauto.
      now eauto with typeclass_instances.
      eapply Singleton_Included.
      now eapply Add_functions_free_set_Included; eauto.
      intros Hc. inv Hc. inv H0.
      eapply HD; constructor; eauto. now left; eauto.
      constructor.
      now eapply Add_functions_free_set_Included; eauto.
      now intros Hc; inv Hc; eauto.
    - rewrite !Setminus_Same_set_Empty_set, image_Empty_set...
  Qed.

  Lemma Add_functions_image_Disjoint_Same_set B fvs σ ζ S σ' ζ' S' P :
    Disjoint _ P (Union _ S (name_in_fundefs B)) ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image σ' P) (image σ P).
  Proof with now eauto with Ensembles_DB.
    intros HD Hadd. induction Hadd.
    - rewrite !image_extend_not_In_S.
      eapply IHHadd. simpl in *...
      intros Hc; eapply HD. constructor; eauto.
      now right; left; eauto.
      intros Hc; eapply HD. constructor; eauto.
      left. now eapply Add_functions_free_set_Included; eauto.
    - reflexivity.
  Qed.
      
  Lemma Add_functions_image_Same_set B fvs σ ζ S σ' ζ' S' P :
    Disjoint _ S (name_in_fundefs B) ->
    Disjoint _ P (name_in_fundefs B) ->
    Disjoint _ (image' (lifted_name ζ) P) (Union var S (name_in_fundefs B)) ->
    unique_bindings_fundefs B ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    Same_set _ (image σ' (image' (lifted_name ζ') (Union _ P (name_in_fundefs B))))
             (Union _ (Setminus _ S S') (image σ (image' (lifted_name ζ) P))).
  Proof with now eauto with Ensembles_DB.
    intros. rewrite Add_functions_lifted_name_Same_set; eauto.
    rewrite image_Union, Union_commut. apply Same_set_Union_compat.
    rewrite Add_functions_image_LiftedFuns_Same_set...
    rewrite Add_functions_image_Disjoint_Same_set; eauto.
    reflexivity.  
  Qed.

  Lemma Add_functions_same_name B fvs σ ζ S σ' ζ' S' f :
    In _ (Union _ (name_in_fundefs B) (Setminus _ S S')) f ->
    Add_functions B fvs σ ζ S σ' ζ' S' ->
    σ' f = f.
  Proof.
    intros Hin Hadd. induction Hadd; eauto.
    - destruct (peq f f'); subst.
      + rewrite extend_gss; eauto.
      + rewrite extend_gso; eauto. destruct (peq f0 f); subst.
        * rewrite extend_gss; eauto.
        * rewrite extend_gso; eauto. eapply IHHadd.
          inv Hin. inv H0. inv H1; congruence. now eauto.
          right. inv H0. constructor; eauto.
          intros Hc. eapply H2. constructor; eauto.
          intros Hc'; inv Hc'; congruence.
    - inv Hin. inv H. rewrite Setminus_Same_set_Empty_set in H. inv H.
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
        Disjoint var (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ)))
                 (Union var S (bound_var e)) ->
        Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
        Disjoint var (LiftedFuns ζ) (Union _ S (bound_var e)) ->
        Disjoint var (Funs ζ) (Union _ S (bound_var e)) ->
        Disjoint var (FunsFVs ζ) (Union _ S (bound_var e)) ->
        Disjoint _ (bound_var e) (occurs_free e) ->
        binding_in_map (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ))) rho' ->
        preord_env_P_inj pr cenv (occurs_free e) m σ rho rho' ->
        Funs_inv m rho rho' σ ζ ->
        Exp_lambda_lift ζ σ e S e' S' ->
        preord_exp pr cenv m (e, rho) (e', rho')) ->

     (* Unique bindings *)
     unique_bindings_fundefs B1 ->
     unique_bindings_fundefs B2 ->

     (* The image of σ is neither in the free set nor in the set of bound variables *)
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs ζ) (LiftedFuns ζ))))
              (Union var S (bound_var_fundefs B1)) ->
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs ζ) (LiftedFuns ζ))))
              (Union var S (bound_var_fundefs B2)) ->

     (* The free set is disjoint from the set of bound and free variables *)
     Disjoint var S (Union var (bound_var_fundefs B1) (occurs_free (Efun B1 e))) ->
     Disjoint var S (Union var (bound_var_fundefs B2) (occurs_free_fundefs B2)) ->

     (* The names of lifted functions is neither in the free set nor in the set of bound variables*) 
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B1)) ->
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B2)) ->

     (* The domain of ζ is disjoint with the bound variables *)
     Disjoint var (Funs ζ) (Union _ S (bound_var_fundefs B1)) ->
     Disjoint var (Funs ζ) (Union _ S (bound_var_fundefs B2)) ->          

     (* The free variables of the funs in ζ are disjoint from the bound variables *) 
     Disjoint var (FunsFVs ζ) (Union _ S (bound_var_fundefs B1)) ->
     Disjoint var (FunsFVs ζ) (Union _ S (bound_var_fundefs B2)) ->

     (* The bound variables and the free variables are disjoint *)
     Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

     (* The free variables are in the environment *)
     binding_in_map (image σ (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs ζ) (LiftedFuns ζ))))
                    rho' ->

     (** ζ1 and ζ2 are equal in a [name_in_fundefs B2] *) 
     f_eq_subdomain (name_in_fundefs B2) ζ1 ζ2 ->

     (** The invariant hold for the initial environments **)
     preord_env_P_inj pr cenv (occurs_free (Efun B1 e)) k σ rho rho' ->
     Funs_inv k rho rho' σ ζ ->
     
     NoDup fvs ->
     Included _ (FromList fvs) (Union _ (occurs_free_fundefs B1) (Union _ (LiftedFuns ζ) (FunsFVs ζ))) ->
     Disjoint var (FromList fvs) (Union _ S (bound_var_fundefs B1)) ->
     Disjoint var (FromList fvs) (Union _ S (bound_var_fundefs B2)) ->

     Included _ (name_in_fundefs B2) (name_in_fundefs B1) ->
     
     Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
     Included _ S1'' S1' ->
     Fundefs_lambda_lift ζ1 σ1 B1 S1'' B1' S1''' ->
     
     Add_functions B2 fvs σ ζ S σ2 ζ2 S2' ->
     Included _ S2'' S2' ->
     Fundefs_lambda_lift ζ1 σ1 B2 S2'' B2' S2''' ->

     (** The invariants hold for the final environments **)
     preord_env_P_inj pr cenv (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B2))
                      k σ2 (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho') /\
     Funs_inv k (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho') σ2 ζ2.
  Proof with now eauto with Ensembles_DB.
    revert B2 rho rho' B1 B1' B2' σ ζ σ1 ζ1 σ2 ζ2 S S1' S1'' S1''' S2' S2'' S2''' fvs.
    induction k as [ k IH' ] using lt_wf_rec1.
    induction B2;
      intros rho rho' B1 B1' B2' σ ζ σ1 ζ1 σ2 ζ2 S S1' S1'' S1''' S2' S2'' S2''' fvs
             IHe Hun1 Hun2 Him1 Him2 Hf1 Hf2 Hlf1 Hlf2 Hfun1 Hfun2 Hfvs1 Hfvs2
             HD Hbin Hfeq Henv Hinv Hnd Hin HD1 HD2 Hinc Hadd1 Hinc1 Hll1 Hadd2 Hinc2 Hll2.
    - inv Hadd2. inv Hll2. inv Hun2. simpl.
      assert
        (HB1 : forall j, j < k ->
                    preord_env_P_inj pr cenv (Union var (occurs_free (Efun B1 e)) (name_in_fundefs B1))
                                     j σ1 (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') /\
                    Funs_inv j (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') σ1 ζ1).
      { intros j leq. eapply IH'; (try now apply Hll1); (try now apply Hnd);
                      (try now apply Hadd1); try eassumption.
        - intros. eapply IHe; eauto. omega.
        - eapply Disjoint_Included; [| | now apply Hf1 ].
          normalize_occurs_free... reflexivity.
        - reflexivity.
        - eapply preord_env_P_inj_monotonic; [| eassumption]. omega.
        - eapply Funs_inv_monotonic. eassumption. omega.
        - reflexivity. } clear IH'.
      assert (HB2 : preord_env_P_inj pr cenv (Union var (occurs_free (Efun B1 e)) (name_in_fundefs B2))
                                     k σ' (def_funs B1 B2 rho rho) (def_funs B1' B' rho' rho') /\
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
        eapply Disjoint_Included_r_sym. eapply Add_functions_LiftedFuns_Included_r. eassumption.
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

        assert (Hsub : Included _ S1'' S).
        { eapply Included_trans. eassumption.
          eapply Add_functions_free_set_Included. eassumption. }

        assert (Hsub' : Included _ S3 S).
        { eapply Included_trans. eassumption. eassumption. }

        assert (HDlfuns : Disjoint _ (LiftedFuns ζ1)
                                   (Union _ (Union _ S1'' (Union _ (bound_var e1) (FromList xs1)))
                                          (name_in_fundefs B1))).
        { eapply Disjoint_Included_l. 
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hlf1 ].
          rewrite <- Union_assoc. apply Included_Union_compat. eassumption.
          apply Union_Included.
          now eauto with Ensembles_DB. now apply name_in_fundefs_bound_var_fundefs.
          eapply Union_Disjoint_r. eapply Union_Disjoint_r. 
          eapply Disjoint_Included_r. now apply Hinc1.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [ | now apply Hf1 ].
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          eapply Disjoint_Included_r; [ | now apply Hf1 ].
          now eauto with Ensembles_DB. }
        
        assert (HD' : Disjoint var (Union var (FromList xs1) (FromList ys'))
                               (Union _ (Union _ (Union var S3 (bound_var e1)) (LiftedFuns ζ1))
                                      (name_in_fundefs B1))).
        { eapply Disjoint_Included_r. eapply Included_Union_compat.
          eapply Included_Union_compat. reflexivity.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          reflexivity.
          eapply Union_Disjoint_r. eapply Union_Disjoint_r. eapply Union_Disjoint_r.
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
          eassumption. now apply Hinc1. now eauto with Ensembles_DB.
          eapply Union_Disjoint_l. eassumption.
          eapply Disjoint_Included ; [ | | now apply Hf1 ].
          apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          eapply Included_trans; eassumption. }

        assert (HDim : Disjoint _ (image σ1
                                         (Union _
                                                (Union _ (occurs_free (Efun B1 e))
                                                       (Union _ (LiftedFuns ζ1) (FunsFVs ζ1)))
                                                (name_in_fundefs B1)))
                                (Union _ S1'' (Union _ (bound_var e1) (FromList xs1)))).
        { eapply Disjoint_Included_l. eapply Add_functions_image_Included.
          eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_Included; [| | now apply Him1 ].
          now eauto with Ensembles_DB.
          apply image_monotonic. apply Setminus_Included_Included_Union.
          apply Union_Included. apply Union_Included. now eauto with Ensembles_DB.
          apply Union_Included. eapply Included_trans.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          now eauto with Ensembles_DB.
          eapply Included_trans.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          apply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eassumption.
          normalize_occurs_free... now eauto with Ensembles_DB.
          eapply Union_Disjoint_l. eapply Disjoint_sym.
          eapply Union_Disjoint_l; [ | eapply Union_Disjoint_l]; try eassumption.
          eapply Disjoint_Included; [| | now apply Hf1].
          eapply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          eassumption.
          eapply Union_Disjoint_r. eapply Disjoint_Included_r. eapply Hinc1.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          clear Hf2. eapply Union_Disjoint_r... }

        assert (HDfuns : Disjoint _ (Funs ζ1) (Union _ S (Union _ (bound_var e1) (FromList xs1)))).
        { eapply Disjoint_Included_l.
          eapply Add_functions_Funs_Included. eassumption.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hfun1 ].
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_r. 
          apply Disjoint_sym. eapply Disjoint_Included_r.
          now apply name_in_fundefs_bound_var_fundefs.
          clear Hf2. now eauto with Ensembles_DB.
          eapply Union_Disjoint_r; eapply Disjoint_sym; eassumption. }

        assert (HDfunsfvs : Disjoint _ (FunsFVs ζ1)
                                     (Union _ S (Union _ (bound_var e1) (FromList xs1)))).
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
        assert (σ1 f'0 = f'0).
        { assert (Hin' := fun_in_fundefs_name_in_fundefs _ _ _ _ _ (find_def_correct _ _ _ _ _ Hfind2)).
          eapply Add_functions_Fundefs_lambda_lift_name_in_fundefs in Hin'; [ | | now eauto | | ]; eauto.
          eapply Add_functions_same_name; eauto. reflexivity.
        } rewrite H in Hget3. 
        rewrite def_funs_eq in Hget3;
        [| eapply fun_in_fundefs_name_in_fundefs; eapply find_def_correct; eassumption ].
        inv Hget3. rewrite Hfind3 in Hfind2. clear H. inv Hfind2.        
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
                apply Included_Union_compat. apply Included_Union_compat.
                eassumption. reflexivity. reflexivity.
                rewrite FromList_app. now eauto 15 with Ensembles_DB.
              * rewrite FromList_app. now eauto with Ensembles_DB.
          - (*  Disjoint _ S3 (Union _ (bound_var e1) (occurs_free e1)) *)
            eapply Disjoint_Included_l. eassumption.
            eapply Disjoint_Included_r; [| now apply Hf1 ].
            normalize_occurs_free. rewrite Union_assoc. eapply Included_Union_preserv_l.
            eapply bound_var_occurs_free_in_fun_Included.
            apply find_def_correct. eassumption.
          - (*  Disjoint var (LiftedFuns ζ1') (bound_var  e1) *)
            now eauto with Ensembles_DB.
          - (* Disjoint var (Funs ζ1') (bound_var e1) *)
            clear Hfun2. now eauto with Ensembles_DB.
          - (* Disjoint var (FunsFVs ζ1') (bound_var e1) *)
            eapply Disjoint_Included_r; [| eassumption ].
            now eauto with Ensembles_DB.
          - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free;
             [| | eassumption ]; eauto.
            eapply find_def_correct. eassumption.
          - eapply binding_in_map_antimon;
            [ | eapply binding_in_map_setlist;
                [ eapply binding_in_map_setlist;
                  [ eapply binding_in_map_def_funs; eassumption |  eassumption ] | eassumption ]].
            eapply Included_trans. eapply image_extend_lst_Included.
            rewrite !app_length. congruence.
            rewrite !FromList_app.
            apply Union_Included; [| now eauto with Ensembles_DB ]. 
            eapply Included_trans. eapply Add_functions_image_Included. eassumption.
            eapply Union_Included.
            + do 3 eapply Included_Union_preserv_r.
              eapply image_monotonic. do 2 apply Setminus_Included_Included_Union.
              eapply Included_trans. eapply Included_Union_compat.
              eapply Included_Union_compat. eassumption.
              eapply Add_functions_FunsFVs_Included_r; eauto.
              eapply Add_functions_LiftedFuns_Included_r; eauto.
              normalize_occurs_free. now eauto 20 with Ensembles_DB.
            + do 2 eapply Included_Union_preserv_r.
              eapply Included_Union_preserv_l.
              rewrite (Add_functions_Fundefs_lambda_lift_name_in_fundefs B1 B3); eauto.
              reflexivity. reflexivity.
          - (* preord_env_P_inj pr cenv (occurs_free e1) j (σ1' <{ xs1 ++ fvs ~> xs1 ++ ys' }>) rho1' rho3' *)
            rewrite extend_lst_app; [| reflexivity ].  
            eapply preord_env_P_inj_setlist_alt with (f := σ1 <{ fvs ~> ys' }>);
              [| eassumption | eassumption | eassumption | now eauto | | now eauto | now eauto ].
            + eapply preord_env_P_inj_resetlist; try eassumption.
              * eapply Disjoint_Included; [ | | now apply HDim ].
                eapply Included_trans. eassumption. now eauto with Ensembles_DB.
                apply image_monotonic. normalize_occurs_free.
                apply Setminus_Included_Included_Union.
                eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
              * now eauto.
              * eapply preord_env_P_inj_antimon. eassumption.
                normalize_occurs_free. apply Setminus_Included_Included_Union.
                eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
            + (* Disjoint var (image (σ1' <{ fvs ~> ys' }>)
                                       (Setminus var (occurs_free e1) (FromList xs1))) 
                            (FromList xs1) *)
              eapply Disjoint_Included_l. eapply image_extend_lst_Included.
              now eauto. eapply Union_Disjoint_l.
              * eapply Disjoint_Included;[| | now apply HDim ].
                now eauto with Ensembles_DB.
                apply image_monotonic. normalize_occurs_free.
                do 2 apply Setminus_Included_Included_Union.
                eapply Included_trans. eassumption.
                now eauto 10 with Ensembles_DB.
              * (* Disjoint var (FromList ys') (FromList xs1) *)
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_l; [ eassumption |].
                eapply Disjoint_Included_r; [| now apply Hf1 ].
                eapply Included_Union_preserv_l. eassumption.
          - rewrite extend_lst_app; [| reflexivity ].
            eapply Funs_inv_setlist; eauto.
            + eapply Funs_inv_setlist_getlist_r; eauto. 
              eapply Disjoint_Included ; [ | | eapply HDim ].
              eapply Included_trans. eassumption.
              now eauto with Ensembles_DB.
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
                apply image_monotonic.
                do 2 apply Setminus_Included_Included_Union.
                now eauto 10 with Ensembles_DB.
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
              eapply Add_functions_LiftedFuns_Included_r in H; [| eassumption ].
              inv H. eapply Hlf1. now constructor; eauto.
              now inv H0; eauto.
            + erewrite getlist_app. reflexivity.
              erewrite getlist_setlist. reflexivity. eassumption. eassumption.
              erewrite getlist_setlist_Disjoint; try eassumption.
              eapply Disjoint_Included_l. eassumption.
              rewrite FromList_map_image_FromList.
              eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply HDim ].
              now eauto with Ensembles_DB.
              apply image_monotonic. eapply Included_trans. eassumption.
              apply Union_Included. normalize_occurs_free...
              apply Union_Included. eapply Included_trans. 
              eapply Add_functions_LiftedFuns_Included_l with (ζ' := ζ1); eauto.
              eapply Disjoint_Included_r; [| eapply Hfun1 ].
              eapply Included_Union_preserv_r.
              now apply name_in_fundefs_bound_var_fundefs. now eauto with Ensembles_DB.
              eapply Included_trans. eapply Add_functions_FunsFVs_Included_l.
              now apply Hadd1. eassumption.
              eapply Disjoint_Included_r; [| now apply Hfun1 ].
              eapply Included_Union_preserv_r.
              now apply name_in_fundefs_bound_var_fundefs.
              now eauto with Ensembles_DB. } }
      split.
      + assert (Heq : f' = f'0).
         { rewrite Hfeq in H4. rewrite extend_gss in H4.
           now inv H4. now left; eauto. } subst.
        eapply preord_env_P_inj_set_extend_not_In_P_r;
          [ eapply preord_env_P_inj_set_alt | | ].
        * eapply preord_env_P_inj_antimon. eassumption.
          now eauto 10 with Ensembles_DB.
        * eassumption.
        * intros Hc. eapply Add_functions_image_Included in Hc; [| eassumption ].
          inv Hc. eapply Him2. constructor; eauto. eapply image_monotonic; [| eassumption ].
          do 2 apply Setminus_Included_Included_Union.
          apply Union_Included; now eauto 6 with Ensembles_DB.
          inv H. eapply H9. now apply name_in_fundefs_bound_var_fundefs.
          eapply Hf2. constructor; eauto. now eapply Setminus_Included; eauto.
        * intros Hc. inv Hc. eapply Hf1. constructor; eauto.
          now eapply Add_functions_free_set_Included; eauto.
          eapply Hf2. constructor. now eapply Add_functions_free_set_Included; eauto.
          left. rewrite bound_var_fundefs_Fcons. inv H; eauto.
          do 3 right. now apply name_in_fundefs_bound_var_fundefs.
        * assert (Heqlf := lifted_name_eq _ _ _ _ _ H4).
          assert (Hinlf : In var (LiftedFuns ζ1) f'0) by (repeat eexists; eauto).
          intros Hc. eapply image_extend_Included' in Hc. inv Hc. 
          eapply Add_functions_image_Included in H; [| eassumption ]. inv H.
          eapply Him2. constructor.
          eapply image_monotonic; [| eassumption ].
          do 2 apply Setminus_Included_Included_Union.
          now eauto 10 with Ensembles_DB.
          left. eapply Add_functions_free_set_Included; eassumption.
          inv H0. eapply Hf2. constructor.
          eapply Add_functions_free_set_Included; eassumption.
          left. normalize_bound_var. do 3 right.
          now apply name_in_fundefs_bound_var_fundefs. now inv H; eauto.
          inv H; subst. eapply Hf2.
          constructor; eauto. eapply Add_functions_free_set_Included; eassumption.
      + edestruct name_in_fundefs_find_def_is_Some as [ft1 [xs1 [e1 Hdef]]].
        apply Hinc. now left.
        edestruct Fundefs_lambda_lift_find_def with (B1 := B1)
          as (xs2 & ys' & e2 & S3 & S2 & Hfind1 & Hfind2 & Hnd1
                  & Hnd2 & Hlen1 & Hlen2 & Hinc1' & Hinc2' & Hinc3' & HD1' & HD2' & HD3' & Hll);
        try eassumption.
        eapply Disjoint_Included_r_sym. eapply Add_functions_LiftedFuns_Included_r. eassumption.
        eapply Union_Disjoint_l. eapply Disjoint_Included_r; [| now apply Hlf1 ]...
        eapply Disjoint_Included; [| | now apply Hf1]...
        eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
        assert (Hinc' : Included M.elt (FromList fvs0)
                                (Union var (occurs_free (Efun B1 e)) (Union _ (LiftedFuns ζ) (FunsFVs ζ)))).
        { eapply Included_trans with (s2 := FunsFVs ζ1).
          intros x Hx. now repeat eexists; eauto. 
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r. eassumption.
          eapply Included_trans. apply Included_Union_compat. reflexivity. eassumption.
          normalize_occurs_free. now eauto 10 with Ensembles_DB. }
        assert (HDfvs :  Disjoint var (FromList fvs0)
                                  (Union _  (name_in_fundefs B1) (Setminus var S S1'))).
        { clear Hlf2 Hfvs2.
          eapply Disjoint_Included_l with (s3 := (FunsFVs ζ1)).
          eexists; eauto.
          eapply Disjoint_Included_l. eapply Add_functions_FunsFVs_Included_r.
          eassumption.
          eapply Disjoint_Included_r.
          eapply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          now apply Setminus_Included.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_sym. eapply Union_Disjoint_l. eassumption.
          eapply Disjoint_Included; [| | eapply Hf1 ]. normalize_occurs_free...
          reflexivity.
          eapply Union_Disjoint_l; now eauto with Ensembles_DB. }
        assert (HDfvs' :  Disjoint var (FromList fvs0)
                                   (Union _  (name_in_fundefs B2) (Setminus var S S'))).
        { eapply Disjoint_Included_l with (s3 := (FunsFVs ζ1)).
          eexists; eauto.
          eapply Disjoint_Included_l. eapply Add_functions_FunsFVs_Included_r.
          eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_trans. apply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          now apply Setminus_Included. normalize_bound_var...
          eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_trans. apply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          now apply Setminus_Included. normalize_bound_var... }
        assert (Ha1 : @map var var  σ1 fvs0 = map σ fvs0).
        { symmetry. eapply Add_functions_map_eq; eassumption. }
        assert (Ha2 : @map var var σ' fvs0 = map σ fvs0).
        { symmetry. eapply Add_functions_map_eq; eassumption. }
        edestruct (@binding_in_map_getlist val) with (xs := (map σ1 fvs0)) as [vs Hget]; eauto.
        rewrite Ha1. rewrite FromList_map_image_FromList. eapply image_monotonic.
        eapply Included_trans. eassumption. now eauto with Ensembles_DB.
        rewrite Hfeq in H4. rewrite extend_gss in H4. inv H4.
        rewrite Ha1, <- Ha2 in Hfind1. 
        eapply Funs_inv_set_lifted; (try now apply H4); eauto.
        * rewrite (Add_functions_Fundefs_lambda_lift_name_in_fundefs B1 B1')...
        * rewrite Ha2.
          rewrite getlist_def_funs_Disjoint. rewrite <- Ha1. eassumption.
          simpl in Hfeq. rewrite Union_commut in Hfeq.
          apply f_eq_subdomain_extend_not_In_S_r' in Hfeq.
          rewrite (Add_functions_Fundefs_lambda_lift_name_in_fundefs B2 B'); [| now eauto | | | ]; eauto.
          rewrite FromList_map_image_FromList.
          eapply Disjoint_Included; [| | now apply Him2 ].
          eapply Included_trans. rewrite Union_commut.
          eapply Included_Union_compat. reflexivity.
          now apply name_in_fundefs_bound_var_fundefs.
          normalize_bound_var...
          apply image_monotonic. eapply Included_trans. eassumption.
          normalize_occurs_free... symmetry; eassumption.
          intros Hc. eapply H9. now apply name_in_fundefs_bound_var_fundefs.
        * congruence.
        * eapply Union_Disjoint_l.
          eapply Disjoint_Included_l.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          apply Union_Disjoint_l. clear Hfvs2. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. eapply Disjoint_sym. eassumption.
          clear Hlf2 Hfvs2. now eauto with Ensembles_DB.
          clear HD2. now eauto with Ensembles_DB.
        * clear Hlf2 Hf2. 
          eapply Disjoint_Included_l.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. now apply Setminus_Included.
          now eauto with Ensembles_DB.
        * unfold LiftedFuns. 
          rewrite Add_functions_Funs_Same_set; eauto.
          rewrite image'_Union, Add_functions_name_in_fundefs; eauto.
          rewrite Add_functions_lifted_name_Disjoint_Same_set; eauto.
          rewrite image_Union.
          rewrite Add_functions_image_Disjoint_Same_set, Add_functions_image_LiftedFuns_Same_set; eauto.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included; [| | now apply Him1 ]. 
          eapply Included_Union_preserv_r. now apply name_in_fundefs_bound_var_fundefs.
          eapply image_monotonic...
          eapply Disjoint_Included; [| | now apply Hf1 ].
          eapply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB.
          eapply Disjoint_Included_r; [| now apply Hf2 ].
          eapply Included_trans; [now apply name_in_fundefs_bound_var_fundefs | ].
          normalize_bound_var...
          eapply Disjoint_Included_r; [| now apply Hlf2 ].
          eapply Included_Union_compat. reflexivity.
          eapply Included_trans; [now apply name_in_fundefs_bound_var_fundefs | ].
          normalize_bound_var...
          eapply Disjoint_Included_r; [| now apply Hfun2 ].
          eapply Included_Union_compat. reflexivity.
          normalize_bound_var. do 3 eapply Included_Union_preserv_r.
          now apply name_in_fundefs_bound_var_fundefs.
        * rewrite image_Union.
          rewrite <- FromList_map_image_FromList, Ha2, FromList_map_image_FromList.
          rewrite (Add_functions_Fundefs_lambda_lift_name_in_fundefs B1 B1'); [ | now eauto | | | ]; eauto; try reflexivity.
          rewrite Add_functions_image_Disjoint_Same_set with (σ' := σ'); eauto.
          eapply Disjoint_Included_r with (s2 := Union var S (name_in_fundefs B1)).
          eapply Union_Included; [ eapply Union_Included |]; eauto with Ensembles_DB.
          eapply Included_trans. eassumption.
          eapply Included_trans. eassumption.
          eapply Included_trans. now eapply Add_functions_free_set_Included; eauto.
          now eauto with Ensembles_DB.
          rewrite <- image_Union. eapply Disjoint_Included; [| |  now apply Him1].
          eapply Included_Union_compat. reflexivity.
          now apply name_in_fundefs_bound_var_fundefs.
          eapply image_monotonic. eapply Union_Included.
          eapply Included_trans. eassumption. normalize_occurs_free...
          eapply Included_trans. eapply Add_functions_FunsFVs_Included_r.
          eassumption. eapply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eassumption. normalize_occurs_free...
          eapply Disjoint_Included_l. eapply Add_functions_FunsFVs_Included_r.
          eassumption. eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Union_compat. reflexivity.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
          normalize_bound_var...
          eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Union_compat. reflexivity.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
          normalize_bound_var...
        * eapply Disjoint_Included_r.
          eapply Included_trans.
          eapply Fundefs_lambda_lift_name_in_fundefs. eassumption.
          apply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Disjoint_Included_l.
          eapply Included_trans; eassumption.
          rewrite Union_assoc. apply Union_Disjoint_r.
          eapply Disjoint_Included_l.
          eapply Add_functions_free_set_Included. eassumption.
          clear Hf2...
          now eauto with Ensembles_DB.
        * eapply Disjoint_Included_l.
          now eapply Add_functions_FunsFVs_Included_r; eauto.
          rewrite Add_functions_Fundefs_lambda_lift_name_in_fundefs; [| | now eauto | | ]; eauto.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| now apply Hfvs1 ]. rewrite Union_commut.
          apply Included_Union_compat. now eauto with Ensembles_DB.
          now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_r; [| now apply HD1 ]. rewrite Union_commut.
          apply Included_Union_compat. now eauto with Ensembles_DB.
          now apply name_in_fundefs_bound_var_fundefs.
          reflexivity.
        * intros Hc. eapply Add_functions_LiftedFuns_Included_r in Hc; [| eassumption ].
          inv Hc. eapply Hlf1. constructor; eauto. left.
          now eapply Add_functions_free_set_Included; eauto.
          now inv H; eauto.
        * intros Hc. eapply HD1. constructor; eauto. left.
          now eapply Add_functions_free_set_Included; eauto.
        * intros Hc.
          eapply image_monotonic in Hc;
            [| eapply Add_functions_LiftedFuns_Included_r ; now eauto ].
          eapply Add_functions_image_Included in Hc; eauto. inv Hc.
          rewrite Setminus_Union_distr in H.
          rewrite (Setminus_Included_Empty_set (Setminus var S S')) in H;
            try eauto with Ensembles_DB.
          rewrite Union_Empty_set_neut_r in H. eapply Him2.
          constructor. eapply image_monotonic; [| eassumption ]...
          left. now eapply Add_functions_free_set_Included; eauto.
          inv H. eapply Hf2. constructor.
          now eapply Add_functions_free_set_Included; eauto.
          left. rewrite bound_var_fundefs_Fcons. do 3 right.
          now apply name_in_fundefs_bound_var_fundefs.
          now inv H0; eauto.
        * left; eauto.
    - inv Hll2. inv Hadd2. simpl. rewrite Union_Empty_set_neut_r.
      split; eauto. 
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
        Disjoint var (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ)))
                 (Union var S (bound_var e)) ->
        Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
        Disjoint var (LiftedFuns ζ) (Union _ S (bound_var e)) ->
        Disjoint var (Funs ζ) (Union _ S (bound_var e)) ->
        Disjoint var (FunsFVs ζ) (Union _ S (bound_var e)) ->
        Disjoint _ (bound_var e) (occurs_free e) ->
        binding_in_map (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ))) rho' ->
        preord_env_P_inj pr cenv (occurs_free e) m σ rho rho' ->
        Funs_inv m rho rho' σ ζ ->
        Exp_lambda_lift ζ σ e S e' S' ->
        preord_exp pr cenv m (e, rho) (e', rho')) ->

     (* Unique bindings *)
     unique_bindings_fundefs B1 ->

     (* The image of σ is neither in the free set nor in the set of bound variables *)
     Disjoint var (image σ (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs ζ) (LiftedFuns ζ))))
              (Union var S (bound_var_fundefs B1)) ->

     (* The free set is disjoint from the set of bound and free variables *)
     Disjoint var S (Union var (bound_var_fundefs B1) (occurs_free (Efun B1 e))) ->

     (* The names of lifted functions is neither in the free set nor in the set of bound variables*) 
     Disjoint var (LiftedFuns ζ) (Union _ S (bound_var_fundefs B1)) ->

     (* The domain of ζ is disjoint with the bound variables *)
     Disjoint var (Funs ζ) (Union _ S (bound_var_fundefs B1)) ->

     (* The free variables of the funs in ζ are disjoint from the bound variables *) 
     Disjoint var (FunsFVs ζ) (Union _ S (bound_var_fundefs B1)) ->

     (* The bound variables and the free variables are disjoint *)
     Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

     (* The free variables are in the environment *)
     binding_in_map (image σ (Union _ (occurs_free (Efun B1 e)) (Union _ (FunsFVs ζ) (LiftedFuns ζ))))
                    rho' ->

     (** The invariants hold for the initial environments **)
     preord_env_P_inj pr cenv (occurs_free (Efun B1 e)) k σ rho rho' ->
     Funs_inv k rho rho' σ ζ ->
     
     NoDup fvs ->
     Included _ (FromList fvs) (Union _ (occurs_free_fundefs B1) (Union _ (LiftedFuns ζ) (FunsFVs ζ))) ->
     Disjoint var (FromList fvs) (Union _ S (bound_var_fundefs B1)) ->
     
     Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
     Included _ S1'' S1' ->
     Fundefs_lambda_lift ζ1 σ1 B1 S1'' B1' S1''' ->

     (** The invariants hold for the final environments **)
     preord_env_P_inj pr cenv (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B1))
                      k σ1 (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') /\
     Funs_inv k (def_funs B1 B1 rho rho) (def_funs B1' B1' rho' rho') σ1 ζ1.
  Proof with now eauto with Ensembles_DB.
    intros. eapply Fundefs_lambda_lift_correct; eauto.
    eapply Disjoint_Included_r; [| eassumption ]. normalize_occurs_free...
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
    Disjoint var (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ)))
             (Union var S (bound_var e)) ->
    (* The fresh set is fresh *)
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    (* The new function names for lifted functions are fresh *)
    Disjoint _ (LiftedFuns ζ) (Union _ S (bound_var e)) ->
    (* The names of the (already defined) functions are disjoint from the bound variables of the expression *)
    Disjoint var (Funs ζ) (Union _ S (bound_var e)) ->
    (* The free variables of a function are disjoint from the bound variables of the expression *)
    Disjoint var (FunsFVs ζ) (Union _ S (bound_var e)) ->    
    (* The bound variables of the expression are disjoint from the free variables *)
    Disjoint _ (bound_var e) (occurs_free e) ->
    (* All the free variables are in the environment *)
    binding_in_map (image σ (Union _ (Union _ (occurs_free e) (FunsFVs ζ)) (LiftedFuns ζ))) rho' ->
    (* The environments are related *)
    preord_env_P_inj pr cenv (occurs_free e) k σ rho rho' ->
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
          apply image_monotonic.
          rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Singleton_l. intros Hc. now eauto.
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
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free...
          rewrite preord_val_eq. constructor. reflexivity.
          now apply Forall2_Forall2_asym_included.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
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
      + eapply Henv. eauto.
      + intros vs1 vs2 Hall. eapply IHe; [ eassumption | | | | | | | | | | eassumption ].
        * eapply Disjoint_Included_l. now eapply image_extend_Included'.
          eapply Union_Disjoint_l.
          rewrite occurs_free_Eproj in Him.
          eapply Disjoint_Included; [ | | now apply Him ].
          normalize_bound_var...
          apply image_monotonic. rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          now eapply Disjoint_Singleton_l.
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
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt.
          eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free... eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
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
      + eapply Disjoint_Included; [ | | now apply Him ].
        now eauto with Ensembles_DB.
        rewrite Union_assoc...
      + eapply Disjoint_Included; [| | now apply HD].
        normalize_occurs_free... now eauto with Ensembles_DB.
      + eapply binding_in_map_antimon ; [| eassumption ].
        rewrite Union_assoc...
      + eapply Included_trans; [ eassumption |]...
      + eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l.
        eapply Union_Disjoint_r.
        rewrite occurs_free_Efun in Hf...
        eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD ].
        normalize_occurs_free... now eauto with Ensembles_DB.
        eapply Union_Disjoint_l.
        eapply Disjoint_Included_r; [| eassumption ]...
        eapply Disjoint_Included_r; [| eassumption ]...
      + eapply IHe; eauto.
        * eapply Disjoint_Included_l. 
          eapply image_monotonic. eapply Included_Union_compat.
          eapply Included_Union_compat. reflexivity.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Disjoint_Included_l. eapply Add_functions_image_Included.
          eassumption.
          apply Union_Disjoint_l.
          eapply Disjoint_Included_r. eapply Included_Union_compat.
          eassumption. reflexivity.
          eapply Disjoint_Included; [| | now apply Him ].
          now eauto with Ensembles_DB.
          apply image_monotonic. rewrite !Setminus_Union_distr.
          rewrite (Setminus_Included_Empty_set (Setminus var S S'0)), Union_Empty_set_neut_r.
          eapply Union_Included. eapply Union_Included. 
          rewrite <- Setminus_Union. normalize_occurs_free...
          eapply Union_Included. now eauto with Ensembles_DB.
          eapply Included_trans. eapply Included_Setminus_compat.
          eassumption. reflexivity. rewrite !Setminus_Union_distr.
          eapply Union_Included. 
          rewrite <- Setminus_Union. normalize_occurs_free...
          now eauto with Ensembles_DB. now eauto with Ensembles_DB.
          now eauto with Ensembles_DB.
          eapply Union_Disjoint_l.
          eapply Disjoint_Included_l. now apply name_in_fundefs_bound_var_fundefs.                     
          apply Union_Disjoint_r.
          eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply Hf ].
          now eauto with Ensembles_DB. eassumption.
          now eapply Disjoint_sym.
          apply Union_Disjoint_r. eapply Disjoint_Setminus_l.
          eapply Fundefs_Lambda_lift_free_set_Included. eassumption.
          eapply Disjoint_Included; [| | now apply Hf ]...
        * eapply Disjoint_Included; [| | now apply Hf ].
          rewrite <- bound_var_Efun.
          now apply bound_var_occurs_free_Efun_Included.
          eassumption.
        * eapply Disjoint_Included_l.
          eapply Add_functions_LiftedFuns_Included_r. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          apply Union_Disjoint_r.
          eapply Disjoint_Included_r. eapply Fundefs_Lambda_lift_free_set_Included.
          eassumption. now eauto with Ensembles_DB.
          now eauto with Ensembles_DB.
        * eapply Disjoint_Included_l.
          eapply Add_functions_Funs_Included. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l_sym. 
          now apply name_in_fundefs_bound_var_fundefs.
          eapply Union_Disjoint_l; eauto.
          eapply Disjoint_Included; [| | now apply Hf ]...
        * eapply Disjoint_Included_l.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          apply Union_Disjoint_l. now eauto with Ensembles_DB.
          eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_r. eapply Union_Disjoint_l.
          eapply Disjoint_sym. eapply Disjoint_Included; [ | | now apply Hf ].
          normalize_occurs_free...  eassumption.
          eapply Union_Disjoint_l...
          eapply Union_Disjoint_l. eapply Disjoint_sym.
          eapply Disjoint_Included; [ | | now apply HD ].
          normalize_occurs_free... now eauto with Ensembles_DB.
          eapply Union_Disjoint_l...
        * eapply Disjoint_Included_r.
          now eapply occurs_free_Efun_Included.
          apply Union_Disjoint_r. now eauto with Ensembles_DB.
          eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
          eassumption. 
        * eapply binding_in_map_antimon;
          [| eapply binding_in_map_def_funs; eassumption ].
          eapply Included_trans. eapply Add_functions_image_Included. eassumption.
          rewrite (Union_commut (name_in_fundefs B')).
          eapply Included_Union_compat.
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          eapply Union_Included. eapply Union_Included.
          rewrite <- Setminus_Union. normalize_occurs_free...
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Add_functions_FunsFVs_Included_r; eauto. reflexivity.
          rewrite !Setminus_Union_distr. eapply Union_Included.
          now eauto with Ensembles_DB. eapply Setminus_Included_Included_Union.
          eapply Included_trans. eassumption. normalize_occurs_free.
          now eauto 15 with Ensembles_DB. 
          eapply Included_trans. eapply Included_Setminus_compat.
          eapply Add_functions_LiftedFuns_Included_r; eauto. reflexivity.
          rewrite !Setminus_Union_distr, (Setminus_Included_Empty_set (Setminus var S S'0)).
          rewrite Union_Empty_set_neut_r...
          now eauto with Ensembles_DB.
          rewrite Add_functions_Fundefs_lambda_lift_name_in_fundefs with (B2 := B'); eauto.
          now eauto with Ensembles_DB. reflexivity.
        * eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free. 
          rewrite Union_commut, Union_assoc, Union_Setminus_Included;
            now eauto with Ensembles_DB typeclass_instances.
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
      now eapply Henv.
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
          apply image_monotonic. rewrite !Setminus_Union_distr...
          eapply Union_Disjoint_r.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          now eapply Disjoint_Singleton_l.
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
          eapply Included_trans. eapply image_extend_Included'.
          eapply Included_Union_compat; [| reflexivity ].
          eapply image_monotonic. rewrite !Setminus_Union_distr.
          normalize_occurs_free...
        * eapply preord_env_P_inj_set_alt. 
          eapply preord_env_P_inj_antimon. eassumption.
          normalize_occurs_free...
          eassumption.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ].
          normalize_occurs_free...
        * eapply Funs_inv_set.
          intros Hc. eapply Hfun. now constructor; eauto.
          intros Hc. eapply Hlf. now constructor; eauto.
          intros Hc. eapply Hfvs. now constructor; eauto.
          intros Hc. eapply Him. constructor; eauto.
          eapply image_monotonic; [| eassumption ]...
          eassumption.
    - eapply preord_exp_halt_compat.
      eapply Henv; eauto.
  Qed.

End Lambda_lifting_correct.