(* Correctness proof for lambda lifting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.cps L6.cps_util L6.set_util L6.hoisting L6.identifiers L6.ctx
        L6.Ensembles_util L6.alpha_conv L6.List_util L6.functions L6.lambda_lifting
        L6.eval L6.logical_relations L6.hoare L6.tactics.
Require Import compcert.lib.Coqlib.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Section Lambda_lifting_correct.

  Variable pr : prims.
  Variable cenv : ctor_env.

  Variable (P : relation nat) (PG : nat -> relation (exp * env * nat)).
  
  
  (** The invariant that relates the original function definitions with the lifted ones *)
  Definition Funs_inv k (rho rho' : env) (σ : var -> var)
             (ζ : var -> option (var * fun_tag * list var)) : Prop :=
    forall f f' ft' fvs vs1 vs2 j ft1  rho1 rho1' B1 f1 xs1 e1,
      ζ f = Some (f', ft', fvs) ->
      M.get f rho = Some (Vfun rho1 B1 f1) ->
      length vs1 = length vs2 ->
      find_def f1 B1 = Some (ft1, xs1, e1) ->
      Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
      exists rho2 rho2' B2 f2 xs2 e2 vs2',
        M.get (σ f') rho' = Some (Vfun rho2 B2 f2) /\
        find_def f2 B2 = Some (ft', xs2, e2) /\
        get_list (map σ fvs) rho' = Some vs2' /\
        Some rho2' = set_lists xs2 (vs2 ++ vs2') (def_funs B2 B2 rho2 rho2) /\
        (j < k -> Forall2 (preord_val pr cenv j PG) vs1 vs2 ->
         preord_exp pr cenv j P PG (e1, rho1') (e2, rho2')).
  
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
    - rewrite map_extend_not_In. rewrite get_list_set_neq. eassumption.
      intros Hc. eapply in_map_iff in Hc. destruct Hc as [x' [Heq' HIn]].
      eapply Hnin5. eexists; split; eauto. left. now repeat eexists; eauto.
      intros Hc. eapply Hnin4. repeat eexists. eassumption. eassumption.
  Qed.

  Lemma Funs_inv_set_lists k rho rho' rho1 rho1' σ ζ vs1 vs2 xs ys :
    set_lists xs vs1 rho = Some rho1 ->
    set_lists ys vs2 rho' = Some rho1' ->
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
    erewrite <- set_lists_not_In in Hget2; eauto.
    edestruct Hinv as
        [rho3 [rho3' [B2 [f2 [xs2 [e2 [vs2'' [Hget' [Hdef' [Hgetl [Hset' Hpre]]]]]]]]]]]; eauto.
    do 8 eexists; repeat split; eauto.
    - rewrite extend_lst_gso. erewrite <- set_lists_not_In; eauto.
      intros Hc; subst. eapply HD4. constructor; eauto.
      eexists. split; eauto. constructor. right. now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
      intros Hc'; subst. eapply HD2. constructor; eauto.
      now repeat eexists; eauto.
    - erewrite get_list_set_lists_Disjoint; eauto.
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

  (* TODO move *)
  Lemma get_reset_lst σ xs ys (vs : list val) rho rho' z  : 
    set_lists ys vs rho = Some rho' ->
    get_list (map σ xs) rho = Some vs ->
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
      destruct (set_lists ys vs rho) eqn:Hset'; try discriminate.
      destruct (M.get (σ x) rho) eqn:Hget'; try discriminate.
      destruct (get_list (map σ xs) rho) eqn:Hgetl; try discriminate.
      inv Hget. inv Hset. inv Hnd1. inv Hnd2. rewrite !FromList_cons in HD.
      assert (H : M.get ((σ <{ xs ~> ys }> {x ~> e}) z) (M.set e v t) =
                  M.get (σ <{ xs ~> ys }> z) t).
      { destruct (peq x z); subst.
        - rewrite extend_gss, M.gss.
          rewrite extend_lst_gso; eauto.
          erewrite <- set_lists_not_In. symmetry. eassumption.
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


  Lemma Funs_inv_set_lists_get_list_r k rho rho' rho'' σ ζ vs xs ys :
    set_lists ys vs rho' = Some rho'' ->
    get_list (map σ xs) rho' = Some vs ->
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
    - erewrite <- get_list_reset_lst; try eassumption.
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
  
     

  (* TODO move *)
  Lemma preord_exp_app_r (P1 P2 : relation nat)
        (k : nat) (rho1 rho2 rhoc rho' : env) (f f' : var) (ft : fun_tag) (ys xs : list var) e1 e2 B vs :
    (forall c1 c2, P2 c1 c2 -> P1 c1 (c2 + 1 + length ys)) ->
    M.get f rho2 = Some (Vfun rhoc B f') ->
    get_list ys rho2 = Some vs ->
    find_def f' B = Some (ft, xs, e2) ->
    set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->
    preord_exp pr cenv k P2 PG (e1, rho1) (e2, rho') ->
    preord_exp pr cenv k P1 PG (e1, rho1) (Eapp f ft ys, rho2).
  Proof.
    intros Hypc Hget Hgetl Hf Hset Hexp v c1 Hleq Hstep.
    edestruct Hexp as (v2 & c2 & Hstep' & Hpost & Hval); eauto.
    do 2 eexists. split.
    now econstructor; eauto. split; [| eassumption ].
    now eauto.
  Qed. 

  Lemma Fundefs_lambda_lift_correct1 k rho rho' B1 B2 σ ζ σ1 ζ1 S
        S1' S1'' S1''' fvs e:
    (* The IH for expressions *)
    (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
               (ζ : var -> option (var * fun_tag * list var)) 
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
          preord_env_P_inj pr cenv PG (occurs_free e) m σ rho rho' ->
          Funs_inv m rho rho' σ ζ ->
          Exp_lambda_lift ζ σ e S e' S' ->
          preord_exp pr cenv m P PG (e, rho) (e', rho')) ->

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

    (** The invariant hold for the initial environments **)
    preord_env_P_inj pr cenv PG (occurs_free (Efun B1 e)) k σ rho rho' ->
    Funs_inv k rho rho' σ ζ ->
    
    NoDup fvs ->
    FromList fvs \subset (occurs_free_fundefs B1 :|: (LiftedFuns ζ :|: FunsFVs ζ)) ->
    (* Disjoint var (FromList fvs) (Union _ S (bound_var_fundefs B1)) -> *)    
    
    Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
    Included _ S1'' S1' ->
    Fundefs_lambda_lift1 ζ1 σ1 B1 S1'' B2 S1''' ->
    

    (** The invariants hold for the final environments **)
    preord_env_P_inj pr cenv PG (occurs_free (Efun B1 e) :|: name_in_fundefs B1)
                     k σ1 (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') /\
    Funs_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') σ1 ζ1.
  Proof with now eauto with Ensembles_DB.
    revert rho rho' B1 B2 σ ζ σ1 ζ1 S 
           S1' S1'' S1''' fvs e.
    induction k as [k IHk] using lt_wf_rec1;
      intros rho rho' B1 B2 σ ζ σ1 ζ1 S
             S1' S1'' S1''' fvs e IHe Hun Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hbin Henv Hfinv Hnd Hin1 Hadd Hin2 Hllfuns.
    assert 
      (HB1 : forall j, j < k ->
                       preord_env_P_inj pr cenv PG (Union var (occurs_free (Efun B1 e)) (name_in_fundefs B1))
                                        j σ1 (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') /\
                       Funs_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') σ1 ζ1).
    { intros j leq. eapply IHk; last (now apply Hllfuns); eauto.
      - intros. eapply IHe; eauto. omega.
      - eapply preord_env_P_inj_monotonic; [| eassumption]. omega.
      - eapply Funs_inv_monotonic. eassumption. omega. }
    (* ASSERTIONS *)
    assert (Hname : name_in_fundefs B1 \subset bound_var_fundefs B1).
    { eapply name_in_fundefs_bound_var_fundefs. }
    assert (HsubS: S1' \subset S).
    { eapply Add_functions_free_set_Included. eassumption. }
    assert (HDlfuns : Disjoint _ (LiftedFuns ζ1) (S1' :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l. 
      eapply Add_functions_LiftedFuns_Included_r. eassumption.
      eapply Union_Disjoint_l. eapply Disjoint_Included_r; [| eassumption ]...
      now eauto with Ensembles_DB. }
    assert (HDfuns : Disjoint _ (Funs ζ1) (S :|: (bound_var_fundefs B1 \\ name_in_fundefs B1))).
    { eapply Disjoint_Included_l.
      eapply Add_functions_Funs_Included. eassumption.
      eapply Union_Disjoint_l. now sets.
      eapply Union_Disjoint_r; [| now sets ].
      apply Disjoint_sym. eapply Disjoint_Included_r.
      now apply name_in_fundefs_bound_var_fundefs. now sets. }     
    assert (HDfunsfvs : Disjoint _ (FunsFVs ζ1) (S :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l.
      eapply Add_functions_FunsFVs_Included_r. eassumption.
      eapply Union_Disjoint_l. eassumption.
      eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l.
      eapply Union_Disjoint_r. eapply Disjoint_sym. eapply Disjoint_Included_r; [| now eapply Hd2 ].
      normalize_occurs_free... now sets.
      now sets. }
    assert (Himin : image σ1 (occurs_free (Efun B1 e) :|: (LiftedFuns ζ1 :|: FunsFVs ζ1)) \subset
                    image σ (occurs_free (Efun B1 e) :|: (FunsFVs ζ :|: LiftedFuns ζ)) :|: (name_in_fundefs B1 :|: (S \\ S1'))).
    { eapply Included_trans. eapply Add_functions_image_Included. eassumption.
      eapply Included_trans. eapply Included_Union_compat. 
      eapply image_monotonic. eapply Included_Setminus_compat. eapply Included_Union_compat. reflexivity.
      eapply Included_Union_compat.  eapply Add_functions_LiftedFuns_Included_r. eassumption.
      eapply Add_functions_FunsFVs_Included_r. eassumption. reflexivity. reflexivity.
      eapply Included_Union_compat; [| reflexivity ]. eapply image_monotonic.
      eapply Setminus_Included_Included_Union.
      do 3 (eapply Union_Included; sets). eapply Included_trans. eassumption. normalize_occurs_free. sets. }
    assert (Himdis : Disjoint _ (image σ1 (occurs_free (Efun B1 e) :|: (LiftedFuns ζ1 :|: FunsFVs ζ1))) (S1' :|: bound_var_fundefs B1 \\ name_in_fundefs B1)).
    { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now sets.
      rewrite Setminus_Union_distr. eapply Union_Disjoint_r. now sets. now sets. }

    split.
    - intros x Hxin v Hget. destruct (Decidable_name_in_fundefs B1) as [Hdec]. destruct (Hdec x); clear Hdec.
      + (* x is in B1 *)  
        edestruct name_in_fundefs_find_def_is_Some as (ft & xs1 & e1 & Hfdef1); [ eassumption | ].
        edestruct Add_functions_is_Some as (f' & ft' & Hzeq & Hnin); [ eassumption | eassumption | ].         
        edestruct Fundefs_lambda_lift_find_def1 as
            (xs2 & ys & e2 & S1 & S2 & Hf1 & Hf2 & Hnd1 & Hnd2 & Hleq1 & Hleq2 & Hsub1 & Hsub2 &
             Hsub3 & Hd1' & Hd2' & Hd3' & Hllexp); [ eassumption | eassumption | | | eassumption | ].
        * (* Disjoint var (bound_var_fundefs B1) (LiftedFuns ζ1) *)
          eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Union_Disjoint_r...
        * eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
        * assert (Hinxs : FromList xs1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
          { eapply Included_Setminus.
            eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
            eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
          assert (Hinxs' : FromList xs1 \subset bound_var_fundefs B1).
          { eapply Included_trans. eassumption. sets. } 
          assert (Hine : bound_var e1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
          { eapply Included_Setminus.
            eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
            eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
          assert (Hine' : bound_var e1 \subset bound_var_fundefs B1).
          { eapply Included_trans. eassumption. sets. } 
          assert (Hssub : S1 \subset S1').
          { eapply Included_trans. eassumption. sets. }
          assert (Hssub' : S1 \subset S).
          { eapply Included_trans. eassumption. sets. }
          assert (Hfree : occurs_free e1 \subset (FromList xs1 :|: (name_in_fundefs B1 :|: occurs_free_fundefs B1))).
          { eapply occurs_free_in_fun. apply find_def_correct. eassumption. }
          assert (Him : image σ1 (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1)) \subset
                              image σ (occurs_free (Efun B1 e) :|: (FunsFVs ζ :|: LiftedFuns ζ)) :|: (name_in_fundefs B1 :|: (S \\ S1'))).
          { eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
            eapply Included_Union_compat; [| reflexivity ]. eapply Included_Union_compat; [| reflexivity ].
            eassumption. rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            rewrite <- !Setminus_Union_distr. eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
            rewrite <- !Union_assoc. rewrite image_Union. 
            rewrite Add_functions_image_name_in_fundefs; [| | eassumption | eassumption ].
            eapply Union_Included. sets. eapply Included_trans; [| eapply Himin ].
            normalize_occurs_free. now sets. now sets. }
            
          assert (Himdis' : Disjoint _ (image σ1 (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1))) (S1' :|: bound_var_fundefs B1 \\ name_in_fundefs B1)).
          { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now sets.
            rewrite Setminus_Union_distr. eapply Union_Disjoint_r. now sets. now sets. } 

          erewrite Add_functions_same_name; [ | | eassumption ]. 2:{ now left. }
          erewrite def_funs_eq; [| now eapply find_def_name_in_fundefs; eauto ].
          eexists; split; [ reflexivity | ].
          assert (Hget' := Hget). rewrite def_funs_eq in Hget'; eauto. inv Hget'.
          rewrite preord_val_eq. intros vs1 vs2 j t xs1' e1' rhoc1 Hleq' Hfd Hset.
          repeat subst_exp. edestruct (set_lists_length3 (def_funs B2 B2 rho' rho') xs2 vs2) as [rho2 Hset2].
          rewrite <- Hleq'. symmetry in Hset. rewrite <- (set_lists_length_eq _ _ _ _ Hset). 
          symmetry. eassumption. 
          do 3 eexists. split. eassumption. split. now eauto.
          intros Hlt Hall.
          assert (Hgetf : M.get f' rho2 = Some (Vfun rho' B2 f')).
          { erewrite <- set_lists_not_In; eauto.
            erewrite def_funs_eq; [| now eapply find_def_name_in_fundefs; eauto ]. reflexivity.
            intros Hc. eapply Hnin. eapply Hin2. eapply Hsub3. eassumption. }
          assert (Ha : exists vsfv, get_list (map σ1 fvs) (def_funs B2 B2 rho' rho') = Some vsfv).
          { eapply binding_in_map_get_list. eapply binding_in_map_def_funs. eassumption. rewrite FromList_map_image_FromList.
            rewrite Add_functions_image_Disjoint_Same_set with (σ := σ) (σ' := σ1); try eassumption.
            eapply Included_Union_preserv_r. eapply image_monotonic.
            eapply Included_trans. eassumption. normalize_occurs_free...            
            eapply Disjoint_Included_l. eassumption. rewrite occurs_free_Efun in Hd2. xsets. } destruct Ha as [vsf Hgetfvs'].
          assert (Hgetfvs : get_list (map σ1 fvs) rho2 = Some vsf).
          { erewrite get_list_set_lists_Disjoint; [ eassumption | | eassumption ].
            rewrite FromList_map_image_FromList.
            eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Himdis ].
            eapply Included_trans. eassumption. eapply Included_trans. eassumption.
            rewrite Setminus_Union_distr. eapply Included_Union_preserv_l.
            eapply Included_Setminus. eapply Disjoint_Included_l. eassumption. sets. reflexivity. 
            eapply image_monotonic. eapply Included_trans. eassumption. normalize_occurs_free.
            eapply Union_Included. sets. eapply Union_Included. eapply Included_trans. eapply Add_functions_LiftedFuns_Included_l. eassumption. eassumption.
            eapply Disjoint_Included_r; [| eassumption ]. now sets. now sets.
            eapply Included_trans. eapply Add_functions_FunsFVs_Included_l. eassumption. eassumption. eapply Disjoint_Included_r; [| eassumption ]. now sets. now sets. }
          assert (Hfset : exists rho2', set_lists (xs1' ++ ys) (vs2 ++ vsf) (def_funs B2 B2 rho' rho') = Some rho2').
          { eapply set_lists_length3. rewrite !app_length, Hleq2. 
            eapply get_list_length_eq in Hgetfvs. rewrite list_length_map in Hgetfvs.
            eapply set_lists_length_eq in Hset2. rewrite Hleq1, <- Hset2, Hgetfvs. reflexivity. }
          destruct Hfset as [rho2' Hfset].
          { eapply preord_exp_app_r; [| eassumption  | | eassumption | | ].
            - admit. (* postcondition *)
            - eapply get_list_app. now erewrite get_list_set_lists; eauto. eassumption.
            - eassumption.
            - assert (Hfset' := Hfset). eapply set_lists_app in Hfset'. destruct Hfset' as (rho2'' & Hsetl1 & Hsetl2).  
              eapply IHe; last eassumption.
              + eassumption.
              + eapply unique_bindings_fun_in_fundefs.
                eapply find_def_correct. eassumption. eassumption.
              + eapply Disjoint_Included_l. eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq2. reflexivity.
                rewrite !FromList_app. eapply Union_Disjoint_l.
                * rewrite <- Setminus_Union. eapply Disjoint_Included_l.
                  eapply image_monotonic. eapply Setminus_Included. 
                  eapply Disjoint_Included; [| | eapply Himdis' ]. eapply Union_Included.
                  rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. eassumption.
                  eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                  rewrite Setminus_Union_distr... reflexivity.
                * eapply Union_Disjoint_l. eapply Union_Disjoint_r.
                  eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym. eapply Disjoint_Included_l. eassumption. now sets.
                  eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                  eapply Union_Disjoint_r. eassumption.  repeat (eapply Disjoint_Included_l; [ eassumption |]). sets.
              + eapply Disjoint_Included_r. eapply Included_Union_compat. eassumption. eassumption.
                eapply Disjoint_Included; [| | eapply Hd2 ].               
                normalize_occurs_free. now xsets. now sets.
              + now sets.
              + now sets.
              + now sets.
              + eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
                eassumption. eassumption.
              + eapply binding_in_map_antimon.
                eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq2. reflexivity.
                rewrite Union_commut. eapply binding_in_map_set_lists; [| eassumption ].
                rewrite FromList_app. rewrite <- Setminus_Union. 
                eapply binding_in_map_antimon. eapply image_monotonic. now eapply Setminus_Included.
                eapply binding_in_map_antimon. eassumption.
                rewrite <- Add_functions_Fundefs_lambda_lift_name_in_fundefs; [| eassumption | eassumption | reflexivity | eassumption ]. 
                rewrite Union_commut. eapply binding_in_map_def_funs. eassumption.
              + assert (Hnd1': NoDup xs1').
                { eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption.
                  eassumption. }
                eapply preord_env_P_inj_f_proper; [ reflexivity | reflexivity | | reflexivity | reflexivity | ].
                eapply extend_lst_app. reflexivity.
                eapply preord_env_P_inj_set_lists_alt with (f := σ1 <{ fvs ~> ys }>);
                  [| eassumption | eassumption | eassumption | now eauto | | now eauto | now eauto ].
                * eapply preord_env_P_inj_reset_lists; [ | | eassumption | | | ]; try eassumption.
                  -- eapply Disjoint_Included; [| | eapply Himdis' ].
                     eapply Included_trans. eassumption. sets.
                     rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. eassumption.
                     eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                     rewrite !Setminus_Union_distr. sets. 
                  -- symmetry. eassumption.
                  -- eapply preord_env_P_inj_antimon. eapply HB1.
                     eassumption.
                     eapply Setminus_Included_Included_Union. eapply Included_trans.
                     eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
                     normalize_occurs_free...
                * eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                  -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
                     eapply Disjoint_Included_r. eassumption. eapply Disjoint_Included; [| | eapply Himdis' ].
                     now sets. now sets.
                  -- eapply Disjoint_Included. eassumption. eassumption.
                     eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto.
              + rewrite extend_lst_app; [| reflexivity ].
                eapply Funs_inv_set_lists; try now eauto.
                * eapply Funs_inv_set_lists_get_list_r.
                  -- eassumption.
                  -- eassumption.
                  -- eapply HB1. eassumption.
                  -- eassumption.
                  -- eassumption.
                  -- now eauto.
                  -- eapply Disjoint_Included; [| | eapply Himdis ].
                     eapply Included_trans. eassumption. eapply Included_trans. eassumption.
                     rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. reflexivity.
                     eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                     now sets.
                * now sets.
                * now sets.
                * now sets.
                * eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                  -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
                     eapply Disjoint_Included_r. eassumption. eapply Disjoint_Included; [| | eapply Himdis' ].
                     now sets. now sets.
                  -- eapply Disjoint_Included. eassumption. eassumption.
                     eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto.
              + eapply set_lists_length_eq in Hset2. rewrite <- Hset2. eassumption. }
      + (* x is not in B1 *)
        inv Hxin; [| contradiction ].
        erewrite <- Add_functions_σ_eq; [ | eassumption | ].
        * rewrite def_funs_neq. eapply Henv.
          eassumption. rewrite def_funs_neq in Hget; eassumption.
          intros Hc. eapply Add_functions_Fundefs_lambda_lift_name_in_fundefs in Hc; [| | | reflexivity | ]; try eassumption.
          eapply Hd1 with (x := σ x). constructor. eapply In_image. now left.
          inv Hc; eauto. left. now inv H0.
        * rewrite Union_DeMorgan.
          constructor. now eauto.
          intros z. eapply Hd2. constructor. inv z; eassumption. now right.
    - intros f1 f2 ft fvs' vs1 vs2 j ft1 rho1 rho1' B1' f1' xs1 e1 Hzeq Hgetf1 Hleq Hfeq Hset.
      destruct (Decidable_name_in_fundefs B1) as [Hdec]. destruct (Hdec f1); clear Hdec.
      + (* f1 is in B1 *)
        rewrite def_funs_eq in Hgetf1; eauto. symmetry in Hgetf1. inv Hgetf1.
        edestruct Fundefs_lambda_lift_find_def1 as
            (xs2 & ys & e2 & S1 & S2 & Hf1 & Hf2 & Hnd1 & Hnd2 & Hleq1 & Hleq2 & Hsub1 & Hsub2 &
             Hsub3 & Hd1' & Hd2' & Hd3' & Hllexp); [ eassumption | eassumption | | | eassumption | ].
        * (* Disjoint var (bound_var_fundefs B1) (LiftedFuns ζ1) *)
          eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Union_Disjoint_r...
        * eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
        * assert (Hinxs : FromList xs1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
          { eapply Included_Setminus.
            eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
            eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
          assert (Hinxs' : FromList xs1 \subset bound_var_fundefs B1).
          { eapply Included_trans. eassumption. sets. } 
          assert (Hine : bound_var e1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
          { eapply Included_Setminus.
            eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
            eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
          assert (Hine' : bound_var e1 \subset bound_var_fundefs B1).
          { eapply Included_trans. eassumption. sets. } 
          assert (Hssub : S1 \subset S1').
          { eapply Included_trans. eassumption. sets. }
          assert (Hssub' : S1 \subset S).
          { eapply Included_trans. eassumption. sets. }
          assert (Hfree : occurs_free e1 \subset (FromList xs1 :|: (name_in_fundefs B1 :|: occurs_free_fundefs B1))).
          { eapply occurs_free_in_fun. apply find_def_correct. eassumption. }
          assert (Him : image σ1 (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1)) \subset
                              image σ (occurs_free (Efun B1 e) :|: (FunsFVs ζ :|: LiftedFuns ζ)) :|: (name_in_fundefs B1 :|: (S \\ S1'))).
          { eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
            eapply Included_Union_compat; [| reflexivity ]. eapply Included_Union_compat; [| reflexivity ].
            eassumption. rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
            rewrite <- !Setminus_Union_distr. eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
            rewrite <- !Union_assoc. rewrite image_Union. 
            rewrite Add_functions_image_name_in_fundefs; [| | eassumption | eassumption ].
            eapply Union_Included. sets. eapply Included_trans; [| eapply Himin ].
            normalize_occurs_free. now sets. now sets. }            
          assert (Himdis' : Disjoint _ (image σ1 (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1))) (S1' :|: bound_var_fundefs B1 \\ name_in_fundefs B1)).
          { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now sets.
            rewrite Setminus_Union_distr. eapply Union_Disjoint_r. now sets. now sets. } 

          erewrite Add_functions_same_name; [ | | eassumption ].
          2:{ right. eapply Add_functions_image_LiftedFuns_Included. eassumption. unfold lifted_name, liftM, bind.
              rewrite Hzeq. reflexivity. eassumption. }
          edestruct Add_functions_is_Some as (f1'' & ft'' & Hzeq' & Hin). eassumption. eassumption.
          rewrite Hzeq in Hzeq'. inv Hzeq'. 
          assert (Ha : exists vsfv, get_list (map σ1 fvs) (def_funs B2 B2 rho' rho') = Some vsfv).
          { eapply binding_in_map_get_list. eapply binding_in_map_def_funs. eassumption. rewrite FromList_map_image_FromList.
            rewrite Add_functions_image_Disjoint_Same_set with (σ := σ) (σ' := σ1); try eassumption.
            eapply Included_Union_preserv_r. eapply image_monotonic.
            eapply Included_trans. eassumption. normalize_occurs_free...
            rewrite occurs_free_Efun in Hd2. eapply Disjoint_Included_l. eassumption. xsets. }
          destruct Ha as [vfvs Hgetfvs].
          assert (Hfset : exists rho2', set_lists (xs1 ++ ys) (vs2 ++ vfvs) (def_funs B2 B2 rho' rho') = Some rho2').
          { eapply set_lists_length3. rewrite !app_length, Hleq2.
            eapply get_list_length_eq in Hgetfvs. rewrite list_length_map in Hgetfvs.
            symmetry in Hset. eapply set_lists_length_eq in Hset. rewrite Hgetfvs, <- Hleq. f_equal. eassumption. }
          destruct Hfset as [rho2' Hsetapp].
          do 7 eexists. split; [| split;  [| split; [| split ]]]; [| eassumption | eassumption | | ].
          -- rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. eassumption.
          -- now eauto.
          -- intros Hlt Hall.
             { assert (Hsetapp' := Hsetapp). eapply set_lists_app in Hsetapp. edestruct Hsetapp as (rho2'' & Hsetl1 & Hsetl2).
               2:{ rewrite <- Hleq. eapply set_lists_length_eq. now eauto. }
               eapply IHe; [ eassumption | | | | | | | | | | | eassumption ].
               - eapply unique_bindings_fun_in_fundefs.
                 eapply find_def_correct. eassumption. eassumption.
               - eapply Disjoint_Included_l. eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq2. reflexivity.
                 rewrite !FromList_app. eapply Union_Disjoint_l.
                 * rewrite <- Setminus_Union. eapply Disjoint_Included_l.
                   eapply image_monotonic. eapply Setminus_Included. 
                   eapply Disjoint_Included; [| | eapply Himdis' ]. eapply Union_Included.
                   rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. eassumption.
                   eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                   rewrite Setminus_Union_distr... reflexivity.
                 * eapply Union_Disjoint_l. eapply Union_Disjoint_r.
                   eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym. eapply Disjoint_Included_l. eassumption. now sets.
                   eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                   eapply Union_Disjoint_r. eassumption.  repeat (eapply Disjoint_Included_l; [ eassumption |]). sets.
               - eapply Disjoint_Included_r. eapply Included_Union_compat. eassumption. eassumption.
                 eapply Disjoint_Included; [| | eapply Hd2 ].               
                 normalize_occurs_free. now xsets. now sets.
               - sets.
               - sets.
               - sets.
               - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
                 eassumption. eassumption.
               - eapply binding_in_map_antimon.
                 eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq2. reflexivity.
                 rewrite Union_commut. eapply binding_in_map_set_lists; [| eassumption ].
                 rewrite FromList_app. rewrite <- Setminus_Union. 
                 eapply binding_in_map_antimon. eapply image_monotonic. now eapply Setminus_Included.
                 eapply binding_in_map_antimon. eassumption.
                 rewrite <- Add_functions_Fundefs_lambda_lift_name_in_fundefs; [| eassumption | eassumption | reflexivity | eassumption ]. 
                 rewrite Union_commut. eapply binding_in_map_def_funs. eassumption.                 
               - assert (Hnd1': NoDup xs1).
                 { eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption.
                  eassumption. }
                 eapply preord_env_P_inj_f_proper; [ reflexivity | reflexivity | | reflexivity | reflexivity | ].
                 eapply extend_lst_app. reflexivity.
                 eapply preord_env_P_inj_set_lists_alt with (f := σ1 <{ fvs ~> ys }>);
                   [| eassumption | eassumption | eassumption | now eauto | | now eauto | eassumption ].
                 + eapply preord_env_P_inj_reset_lists; [ | | eassumption | | | ]; try eassumption.
                   -- eapply Disjoint_Included; [| | eapply Himdis' ].
                      eapply Included_trans. eassumption. sets.
                      rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. eassumption.
                      eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                      rewrite !Setminus_Union_distr. sets. 
                   -- symmetry. eassumption.
                   -- eapply preord_env_P_inj_antimon. eapply HB1.
                      eassumption.
                      eapply Setminus_Included_Included_Union. eapply Included_trans.
                      eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
                      normalize_occurs_free...
                 + eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.                   
                   -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
                      eapply Disjoint_Included_l. eapply Included_trans; [| eapply Him ]. now sets.
                      eapply Union_Disjoint_l. now sets.
                      eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                      eapply find_def_correct. eassumption. eassumption.
                  -- eapply Disjoint_Included. eassumption. eassumption.
                     eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto.
               - rewrite extend_lst_app; [| reflexivity ].
                 eapply Funs_inv_set_lists; try now eauto.
                 + eapply Funs_inv_set_lists_get_list_r.
                   -- eassumption.
                   -- eassumption.
                   -- eapply HB1. eassumption.
                   -- eassumption.
                   -- eassumption.
                   -- now eauto.
                   -- eapply Disjoint_Included; [| | eapply Himdis ].
                      eapply Included_trans. eassumption. eapply Included_trans. eassumption.
                      rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. reflexivity.
                      eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                      now sets.
                 + sets.
                 + sets.
                 + sets.
                 + eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                   -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included.
                      eapply Disjoint_Included_l. eapply Included_trans; [| eapply Him ]. now sets.
                      eapply Union_Disjoint_l. now sets.
                      eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                      eapply find_def_correct. eassumption. eassumption.
                   -- eapply Disjoint_Included. eassumption. eassumption.
                      eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto. }
      + rewrite def_funs_neq in Hgetf1; [| eassumption ].
        erewrite Add_functions_eq in Hzeq; [| eassumption | eassumption ].
        edestruct Hfinv as (rho2 & rho2' & B2' & f2' & xs2 & e2 & cs2 & Hgetf2 & Hf2 & Hgetl & Hset2 & Hyp).
        * eassumption.
        * eassumption.
        * eapply Hleq.
        * eassumption.
        * eassumption.
        * do 7 eexists. split; [| split; [| split; [| split ]]].
          --  assert (Hnin : ~ f2 \in name_in_fundefs B1 :|: (S \\ S1')).
              { intros Hc.
                eapply Hd3. constructor; eauto.  
                eexists f1. split.
                eexists. unfold lifted_name. rewrite Hzeq. reflexivity.
                unfold lifted_name. rewrite Hzeq. reflexivity. simpl. 
                eapply Included_trans; [| reflexivity | eassumption ]. xsets. }
              erewrite <- Add_functions_σ_eq; [ | eassumption | ].
              rewrite def_funs_neq. eassumption.
              ++ intros Hc. eapply Add_functions_Fundefs_lambda_lift_name_in_fundefs in Hc; [| eassumption | eassumption | reflexivity |  eassumption ]. 
                 eapply Hd1. constructor. eexists f2. split; [| reflexivity ]. do 2 right.
                 eexists. split. eexists. unfold lifted_name. rewrite Hzeq. reflexivity.
                 unfold lifted_name. rewrite Hzeq. reflexivity.
                 inv Hc; eauto. inv H; eauto.
              ++ eassumption.
          -- eassumption.
          -- erewrite <- Add_functions_map_eq; [| eassumption |]. eapply get_list_fundefs. eassumption.
             ++ intros y Hin Hin'. eapply FromList_map_image_FromList in Hin. 
                eapply Fundefs_lambda_lift_name_in_fundefs_r in Hin'; [| eassumption | eassumption | reflexivity ].
                rewrite Add_functions_name_in_fundefs in Hin'; [| eassumption | eassumption ].
                eapply Hd1. constructor. eapply image_monotonic; [| eassumption ].
                eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
                intros x Hinx. do 4 eexists. split; eassumption.
                inv Hin'. right. eapply name_in_fundefs_bound_var_fundefs. eassumption.
                inv H. now left. 
             ++ eapply Disjoint_Included; [| | eapply Hd5 ]; sets.
                intros z Hin. do 4 eexists. eauto.
          -- eassumption.
          -- eassumption.
  Admitted. 



  Lemma Make_wrappers_f_eq_subdomain Q ζ σ B S C S' σ' :
    Make_wrappers ζ σ B S C S' σ' ->
    Disjoint _ Q (name_in_fundefs B) ->
    f_eq_subdomain Q σ σ'.
  Proof.
    intros Hw Hd. induction Hw.
    - reflexivity.
    - rewrite <- IHHw. symmetry. eapply f_eq_subdomain_extend_not_In_S_l.
      intros Hc. eapply Hd. constructor. eassumption. now left. reflexivity.
      sets.
  Qed.

  Lemma Make_wrapper_image_name_in_fundefs ζ σ B S C S' σ' :
    Make_wrappers ζ σ B S C S' σ' ->
    unique_bindings_fundefs B ->
    image σ' (name_in_fundefs B) \subset S \\ S'.
  Proof.
    intros Hw Hun. induction Hw.
    - rewrite image_Empty_set, Setminus_Same_set_Empty_set. reflexivity.
    - inv Hun. simpl. rewrite image_Union, image_Singleton.
      eapply Union_Included.
      + erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set f]); [| eassumption | |]. rewrite extend_gss.
        eapply Singleton_Included. constructor. now inv H1. eauto.
        intros Hc. eapply Make_wrappers_free_set_Included in Hc; [| eassumption ]. inv Hc. now eauto.
        eapply Disjoint_Singleton_l. intros Hc. eapply H8. eapply name_in_fundefs_bound_var_fundefs. eassumption. reflexivity.
      + eapply Included_trans. eapply IHHw. eassumption. sets.
  Qed.

  Lemma Make_wrapper_ctx_to_rho ζ σ B S C S' σ' rho :
    Make_wrappers ζ σ B S C S' σ' ->
    exists rho',
      ctx_to_rho C rho rho'.
  Proof.
    intros Hw. revert rho. induction Hw; intros rho.
    - eexists rho. now constructor.
    - edestruct IHHw with (rho := def_funs (Fcons g ft xs' (Eapp f' ft' (xs' ++ map σ fvs)) Fnil)
                                           (Fcons g ft xs' (Eapp f' ft' (xs' ++ map σ fvs)) Fnil) rho rho) as [rho' Hctx]. eexists.
      simpl. constructor. eassumption. 
  Qed.

  (* TODO move *)
  Lemma ctx_to_rho_binding_in_map Q C rho1 rho2 :
    ctx_to_rho C rho1 rho2 ->
    binding_in_map Q rho1 ->
    binding_in_map Q rho2. 
  Proof.
    intros Hctx. revert Q.
    induction Hctx; intros Q Hbin;
      (try eassumption);
      try (eapply IHHctx; eapply binding_in_map_antimon; [| eapply binding_in_map_set ]; [| eassumption ]; now sets).
    eapply IHHctx; eapply binding_in_map_antimon; [| eapply binding_in_map_def_funs ]; [| eassumption ]; now sets.
  Qed.
  
  Lemma binding_in_map_Empty_set A (rho : M.t A) :
    binding_in_map (Empty_set _) rho.
  Proof.
    intros x Hin. inv Hin.
  Qed.
     
  Lemma Make_wrapper_binding_in_map ζ σ B S C S' σ' rho rho' Q :
    Make_wrappers ζ σ B S C S' σ' ->
    unique_bindings_fundefs B -> 
    ctx_to_rho C rho rho' ->
    binding_in_map Q rho ->
    binding_in_map (image σ' (name_in_fundefs B) :|: Q) rho'.
  Proof.
    intros Hw. revert rho rho'. induction Hw; intros rho rho' Hun Hctx Hb.
    - rewrite image_Empty_set, Union_Empty_set_neut_l. inv Hctx. eassumption.
    - inv Hun. inv Hctx. simpl.
      rewrite image_Union, image_Singleton.
      erewrite <- Make_wrappers_f_eq_subdomain with (Q := [set f]); [| eassumption | | reflexivity ]. 
      rewrite extend_gss. simpl in H6. rewrite <- Union_assoc. eapply binding_in_map_Union.
      eapply ctx_to_rho_binding_in_map. eassumption.
      rewrite <- (Union_Empty_set_neut_l _ [set g]). eapply binding_in_map_set.
      now eapply binding_in_map_Empty_set. 
      eapply IHHw. eassumption. eassumption. 
      eapply binding_in_map_antimon; [| eapply binding_in_map_set ]; [| eassumption ]. now sets.
      eapply Disjoint_Singleton_l. intros Hc. eapply H8. now eapply name_in_fundefs_bound_var_fundefs.
  Qed.

  
  Lemma Fundefs_lambda_lift_correct2 k rho rho' B1 B2 σ ζ σ1 ζ1 S S1' S1'' S1''' fvs :
    (* The IH for expressions *)
    (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env)
               (ζ : var -> option (var * fun_tag * list var)) 
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
          preord_env_P_inj pr cenv PG (occurs_free e) m σ rho rho' ->
          Funs_inv m rho rho' σ ζ ->
          Exp_lambda_lift ζ σ e S e' S' ->
          preord_exp pr cenv m P PG (e, rho) (e', rho')) ->

    (* Unique bindings *)
    unique_bindings_fundefs B1 ->

    (* The image of σ is neither in the free set nor in the set of bound variables *)
    Disjoint var (image σ (occurs_free_fundefs B1 :|: (FunsFVs ζ :|: LiftedFuns ζ))) (S :|: bound_var_fundefs B1) ->

    (* The free set is disjoint from the set of bound and free variables *)
    Disjoint var S (bound_var_fundefs B1 :|: occurs_free_fundefs B1) ->

    (* The names of lifted functions is neither in the free set nor in the set of bound variables*) 
    Disjoint var (LiftedFuns ζ) (S :|: bound_var_fundefs B1) ->

    (* The domain of ζ is disjoint with the bound variables *)
    Disjoint var (Funs ζ) (S :|: bound_var_fundefs B1) ->

    (* The free variables of the funs in ζ are disjoint from the bound variables *) 
    Disjoint var (FunsFVs ζ) (S :|: bound_var_fundefs B1) ->

    (* The bound variables and the free variables are disjoint *)
    Disjoint _ (bound_var_fundefs B1) (occurs_free_fundefs B1) ->

    (* The free variables are in the environment *)
    binding_in_map (image σ (occurs_free_fundefs B1 :|: (FunsFVs ζ :|: LiftedFuns ζ))) rho' ->
    
    (** The invariant hold for the initial environments **)
    preord_env_P_inj pr cenv PG (occurs_free_fundefs B1) k σ rho rho' ->
    Funs_inv k rho rho' σ ζ ->
    
    NoDup fvs ->
    FromList fvs \subset (occurs_free_fundefs B1 :|: (LiftedFuns ζ :|: FunsFVs ζ)) ->
    
    Add_functions B1 fvs σ ζ S σ1 ζ1 S1' ->
    Included _ S1'' S1' ->
    Fundefs_lambda_lift2 ζ1 σ1 B1 B1 S1'' B2 S1''' ->
    
    (** The invariants hold for the final environments **)
    Funs_inv k (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') σ1 ζ1.
  Proof with now eauto with Ensembles_DB.
    revert rho rho' B1 B2 σ ζ σ1 ζ1 S S1' S1'' S1''' fvs.
    induction k as [k IHk] using lt_wf_rec1;
      intros rho rho' B1 B2 σ ζ σ1 ζ1 S
             S1' S1'' S1''' fvs IHe Hun Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hbin Henv Hfinv Hnd Hin1 Hadd Hin2 Hllfuns.
    assert 
      (HB1 : forall j, j < k -> Funs_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') σ1 ζ1).
    { intros j leq. eapply IHk; last (now apply Hllfuns); eauto.
      - intros. eapply IHe; eauto. omega.
      - eapply preord_env_P_inj_monotonic; [| eassumption]. omega.
      - eapply Funs_inv_monotonic. eassumption. omega. }
    (* ASSERTIONS *)
    assert (Hname : name_in_fundefs B1 \subset bound_var_fundefs B1).
    { eapply name_in_fundefs_bound_var_fundefs. }
    assert (HsubS: S1' \subset S).
    { eapply Add_functions_free_set_Included. eassumption. }
    assert (HDlfuns : Disjoint _ (LiftedFuns ζ1) (S1' :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l. 
      eapply Add_functions_LiftedFuns_Included_r. eassumption. xsets. }
    assert (HDfuns : Disjoint _ (Funs ζ1) (S :|: (bound_var_fundefs B1 \\ name_in_fundefs B1))).
    { eapply Disjoint_Included_l.
      eapply Add_functions_Funs_Included. eassumption. xsets. }
    assert (HDfunsfvs : Disjoint _ (FunsFVs ζ1) (S :|: bound_var_fundefs B1)).
    { eapply Disjoint_Included_l.
      eapply Add_functions_FunsFVs_Included_r. eassumption. 
      eapply Union_Disjoint_l. eassumption. 
      eapply Disjoint_Included_l. eassumption. xsets. }

    intros f1 f2 ft fvs' vs1 vs2 j ft1 rho1 rho1' B1' f1' xs1 e1 Hzeq Hgetf1 Hleq Hfeq Hset.
    destruct (Decidable_name_in_fundefs B1) as [Hdec]. destruct (Hdec f1); clear Hdec.
    + (* f1 is in B1 *)
      rewrite def_funs_eq in Hgetf1; eauto. symmetry in Hgetf1. inv Hgetf1.
      edestruct Fundefs_lambda_lift_find_def2 as
          (ys & e2 & S1 & S2 & S3 & σ' & C & Hf1 & Hnd1 & Hleq1 & Hsub1 & Hsub2 & Hd1' & Hw & Hllexp);
        [ eassumption | eassumption | | | eassumption | ].
      * (* Disjoint var (bound_var_fundefs B1) (LiftedFuns ζ1) *)
        eapply Disjoint_Included_r. eapply Add_functions_LiftedFuns_Included_r. eassumption.
        eapply Union_Disjoint_r...
      * eapply Add_functions_injective_subdomain_LiftedFuns. eassumption.
      * assert (Himin : image σ' (occurs_free_fundefs B1 :|: (LiftedFuns ζ1 :|: FunsFVs ζ1)) \subset
                        image σ (occurs_free_fundefs B1 :|: (FunsFVs ζ :|: LiftedFuns ζ)) :|: (name_in_fundefs B1 :|: (S \\ S1'))).
        { eapply Included_trans. eapply image_monotonic. eapply Included_Union_compat. reflexivity.
          eapply Included_Union_compat.  eapply Add_functions_LiftedFuns_Included_r. eassumption.
          eapply Add_functions_FunsFVs_Included_r. eassumption.
          rewrite <- Make_wrapper_image; [| eassumption |].
          2:{ eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now xsets. 
              eapply Union_Disjoint_l. now sets. eapply Disjoint_Included_l. eassumption. now xsets. } 
          eapply Included_trans. eapply Add_functions_image_Included. eassumption.
          eapply Included_Union_compat; [| reflexivity ]. eapply image_monotonic.
          eapply Setminus_Included_Included_Union.
          do 3 (eapply Union_Included; sets). eapply Included_trans. eassumption. sets. }
        
        assert (Himdis : Disjoint _ (image σ' (occurs_free_fundefs B1 :|: (LiftedFuns ζ1 :|: FunsFVs ζ1))) (S1' :|: bound_var_fundefs B1 \\ name_in_fundefs B1)).
        { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now sets.
          rewrite Setminus_Union_distr. eapply Union_Disjoint_r. now sets. now sets. }

        assert (Hinxs : FromList xs1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
        { eapply Included_Setminus.
          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
        assert (Hinxs' : FromList xs1 \subset bound_var_fundefs B1).
        { eapply Included_trans. eassumption. sets. } 
        assert (Hine : bound_var e1 \subset bound_var_fundefs B1 \\ name_in_fundefs B1).
        { eapply Included_Setminus.
          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption.
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets. }
        assert (Hine' : bound_var e1 \subset bound_var_fundefs B1).
        { eapply Included_trans. eassumption. sets. } 
        assert (Hssub : S2 \subset S1').
        { eapply Included_trans. eapply Make_wrappers_free_set_Included. eassumption.
          eapply Included_trans. eassumption. sets. }
        assert (Hssub' : S2 \subset S).
        { eapply Included_trans. eassumption. sets. }
        assert (Hfree : occurs_free e1 \subset (FromList xs1 :|: (name_in_fundefs B1 :|: occurs_free_fundefs B1))).
        { eapply occurs_free_in_fun. apply find_def_correct. eassumption. }
         
        assert (Him : image σ' (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1)) \subset
                      image σ (occurs_free_fundefs B1 :|: (FunsFVs ζ :|: LiftedFuns ζ)) :|: (name_in_fundefs B1 :|: (S \\ S2))).
        { eapply Included_trans. eapply image_monotonic. eapply Included_Setminus_compat; [| reflexivity ].
          eapply Included_Union_compat; [| reflexivity ]. eapply Included_Union_compat; [| reflexivity ].
          eassumption. rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          rewrite <- !Setminus_Union_distr. eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
          rewrite <- !Union_assoc. rewrite image_Union. eapply Union_Included. 
          rewrite Make_wrapper_image_name_in_fundefs; [| eassumption | eassumption ]. 
          eapply Included_Union_preserv_r. admit. 
          (* eapply Included_trans. eassumption. eapply Included_trans. eassumption. sets.  *)
          eapply Included_trans. rewrite (Union_commut (FunsFVs _)). eapply Himin. now xsets. }
        
        assert (Himdis' : Disjoint _ (image σ' (occurs_free e1 :|: FunsFVs ζ1 :|: LiftedFuns ζ1 \\ FromList (xs1))) (S2 :|: bound_var_fundefs B1 \\ name_in_fundefs B1)).
        { eapply Disjoint_Included_l. eassumption. eapply Union_Disjoint_l. now sets. eapply Union_Disjoint_l. now sets.
          rewrite Setminus_Union_distr. eapply Union_Disjoint_r. now sets. now sets. } 

        erewrite Add_functions_same_name; [ | | eassumption ].
        2:{ right. eapply Add_functions_image_LiftedFuns_Included. eassumption. unfold lifted_name, liftM, bind.
            rewrite Hzeq. reflexivity. eassumption. }
        edestruct Add_functions_is_Some as (f1'' & ft'' & Hzeq' & Hin). eassumption. eassumption.
        rewrite Hzeq in Hzeq'. inv Hzeq'. 
        assert (Ha : exists vsfv, get_list (map σ1 fvs) (def_funs B2 B2 rho' rho') = Some vsfv).
        { eapply binding_in_map_get_list. eapply binding_in_map_def_funs. eassumption. rewrite FromList_map_image_FromList.
          rewrite Add_functions_image_Disjoint_Same_set with (σ := σ) (σ' := σ1); try eassumption.
          eapply Included_Union_preserv_r. eapply image_monotonic.
          eapply Included_trans. eassumption. now sets. eapply Disjoint_Included_l. eassumption. xsets. }
        destruct Ha as [vfvs Hgetfvs].
        
        assert (Hfset : exists rho2', set_lists (xs1 ++ ys) (vs2 ++ vfvs) (def_funs B2 B2 rho' rho') = Some rho2').
        { eapply set_lists_length3. rewrite !app_length, Hleq1.
          eapply get_list_length_eq in Hgetfvs. rewrite list_length_map in Hgetfvs.
          symmetry in Hset. eapply set_lists_length_eq in Hset. rewrite Hgetfvs, <- Hleq. f_equal. eassumption. }
        destruct Hfset as [rho2' Hsetapp].
        do 7 eexists. split; [| split;  [| split; [| split ]]]; [| eassumption | eassumption | | ].
        -- rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. eassumption.
        -- now eauto.
        -- intros Hlt Hall.
           (* evaluate context from Make_wrappers *)
           eapply preord_exp_post_monotonic. admit. (* postcondition *)
           eapply ctx_to_rho_preord_exp. admit. (* postcondition *)
           ++ admit.
           ++ { eapply preord_exp_post_monotonic. admit. (* postcondition *)
                assert (Hsetapp' := Hsetapp). eapply set_lists_app in Hsetapp. edestruct Hsetapp as (rho2'' & Hsetl1 & Hsetl2).
                2:{ rewrite <- Hleq. eapply set_lists_length_eq. now eauto. }
                eapply IHe; [ eassumption | | | | | | | | | | | eassumption ].
               - eapply unique_bindings_fun_in_fundefs.
                 eapply find_def_correct. eassumption. eassumption.
               - eapply Disjoint_Included_l. eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq1. reflexivity.
                 rewrite !FromList_app. eapply Union_Disjoint_l.
                 * rewrite <- Setminus_Union. eapply Disjoint_Included_l.
                   eapply image_monotonic. eapply Setminus_Included.
                   eapply Disjoint_Included; [| | eapply Himdis' ]. eapply Union_Included. 
                   rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. reflexivity.
                   eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                   rewrite Setminus_Union_distr... reflexivity.
                 * eapply Union_Disjoint_l. eapply Union_Disjoint_r.
                   eapply Disjoint_Included_l. eassumption. eapply Disjoint_sym. eapply Disjoint_Included_l. eassumption. now sets.
                   eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
                   eapply Union_Disjoint_r. eapply Disjoint_Included_r; [| eassumption ]. eapply Make_wrappers_free_set_Included.  eassumption.
                   repeat (eapply Disjoint_Included_l; [ eassumption |]). sets.
               - eapply Disjoint_Included_r. eapply Included_Union_compat. eassumption. eassumption.
                 eapply Disjoint_Included; [| | eapply Hd2 ]. now xsets. now sets. 
               - sets.
               - sets.
               - sets.
               - eapply fun_in_fundefs_Disjoint_bound_Var_occurs_free. eapply find_def_correct. eassumption.
                 eassumption. eassumption.
               - admit.
                 (* eapply binding_in_map_antimon. *)
                 (* eapply image_extend_lst_Included. rewrite !app_length. rewrite <- Hleq1. reflexivity. *)
                 (* rewrite Union_commut. eapply binding_in_map_set_lists; [| eassumption ]. *)
                 (* rewrite FromList_app. rewrite <- Setminus_Union. *)
                 (* eapply binding_in_map_antimon. eapply image_monotonic. now eapply Setminus_Included. *)
                 (* eapply binding_in_map_antimon. eassumption. *)
                 (* eapply binding_in_map_antimon. eapply Included_Union_compat. reflexivity. eapply Included_Union_compat. reflexivity. *)
                 (* eapply Included_Setminus_compat. reflexivity. *)
                 (* rewrite <- Add_functions_Fundefs_lambda_lift_name_in_fundefs; *)
                 (*   [| eassumption | eassumption | reflexivity | eassumption ]. *)
                 (* rewrite Union_commut. eapply binding_in_map_def_funs. eassumption. *)
               - assert (Hnd1': NoDup xs1).
                 { eapply unique_bindings_fun_in_fundefs. eapply find_def_correct; eassumption. eassumption. }
                 eapply preord_env_P_inj_f_proper; [ reflexivity | reflexivity | | reflexivity | reflexivity | ].
                 eapply extend_lst_app. reflexivity. 
                 eapply preord_env_P_inj_set_lists_alt with (f := σ' <{ fvs ~> ys }>);
                   [| eassumption | eassumption | eassumption | now eauto | | now eauto | eassumption ].
                 + eapply preord_env_P_inj_reset_lists; [ | | eassumption | | | ]; try eassumption.
                   -- admit. (* getlist σ' *)
                   -- eapply Disjoint_Included; [| | eapply Himdis' ].
                      eapply Included_trans. eassumption. sets.
                      rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint.
                      eassumption.
                      eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                      rewrite !Setminus_Union_distr. sets.
                   -- symmetry. eassumption.
                   -- admit. (* make_wrappers lemma *)
                      (* eapply preord_env_P_inj_antimon. eapply HB1. *)
                      (* eassumption. *)
                      (* eapply Setminus_Included_Included_Union. eapply Included_trans. *)
                      (* eapply occurs_free_in_fun. eapply find_def_correct. eassumption. *)
                      (* normalize_occurs_free... *)
                 + eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l.
                   -- admit. (* image σ' *)
                      (* eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included. *)
                      (* eapply Disjoint_Included_l. eapply Included_trans; [| eapply Him ]. now sets. *)
                      (* eapply Union_Disjoint_l. now sets. *)
                      (* eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. *)
                      (* eapply find_def_correct. eassumption. eassumption. *)
                   -- eapply Disjoint_Included. eassumption. eassumption.
                      eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto.
               - rewrite extend_lst_app; [| reflexivity ]. eapply Funs_inv_set_lists; try now eauto.
                 + eapply Funs_inv_set_lists_get_list_r.
                   -- eassumption.
                   -- (* eassumption. *) admit. (* Make_wrappers getlist *)
                   -- admit. (* make_wrappers preserves Funs_inv *)
                      (* eapply HB1. eassumption. *)
                   -- eassumption.
                   -- eassumption.
                   -- now eauto.
                   -- eapply Disjoint_Included; [| | eapply Himdis ].
                      eapply Included_trans. eassumption. eapply Included_trans. eassumption.
                      rewrite Setminus_Union_distr. eapply Included_Union_preserv_l. rewrite Setminus_Disjoint. reflexivity.
                      eapply Disjoint_sym. eapply Disjoint_Included; [ eassumption | eassumption | ]. sets.
                      admit. (* image σ' *)
                 (* now sets. *)
                 + sets.
                 + sets.
                 + sets.
                 + admit. (* image σ'*)
                   (* eapply Disjoint_Included_l. eapply image_extend_lst_Included. now eauto. eapply Union_Disjoint_l. *)
                   (* -- eapply Disjoint_Included_l. eapply image_monotonic. eapply Setminus_Included. *)
                   (*    eapply Disjoint_Included_l. eapply Included_trans; [| eapply Him ]. now sets. *)
                   (*    eapply Union_Disjoint_l. now sets. *)
                   (*    eapply Union_Disjoint_l; [| now sets ]. eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs. *)
                   (*    eapply find_def_correct. eassumption. eassumption. *)
                   (* -- eapply Disjoint_Included. eassumption. eassumption. *)
                   (*    eapply Disjoint_Included; [| | eapply Hd2 ]. sets. eapply Included_trans; eauto. *) }
    + rewrite def_funs_neq in Hgetf1; [| eassumption ].
      erewrite Add_functions_eq in Hzeq; [| eassumption | eassumption ].
      edestruct Hfinv as (rho2 & rho2' & B2' & f2' & xs2 & e2 & cs2 & Hgetf2 & Hf2 & Hgetl & Hset2 & Hyp).
      * eassumption.
      * eassumption.
      * eapply Hleq.
      * eassumption.
      * eassumption.
      * do 7 eexists. split; [| split; [| split; [| split ]]].
        --  assert (Hnin : ~ f2 \in name_in_fundefs B1 :|: (S \\ S1')).
            { intros Hc.
              eapply Hd3. constructor; eauto.  
              eexists f1. split.
              eexists. unfold lifted_name. rewrite Hzeq. reflexivity.
              unfold lifted_name. rewrite Hzeq. reflexivity. simpl. 
              eapply Included_trans; [| reflexivity | eassumption ]. xsets. }
            erewrite <- Add_functions_σ_eq; [ | eassumption | ].
            rewrite def_funs_neq. eassumption.
            ++ intros Hc.
               eapply Fundefs_lambda_lift_name_in_fundefs2 in Hc; [| eassumption ].
               eapply Add_functions_name_in_fundefs in Hc; [| eassumption | eassumption ].
               eapply Hd1. constructor. eexists f2. split; [| reflexivity ]. do 2 right.
               eexists. split. eexists. unfold lifted_name. rewrite Hzeq. reflexivity.
               unfold lifted_name. rewrite Hzeq. reflexivity. inv Hc; eauto.
            ++ eassumption.
        -- eassumption.
        -- erewrite <- Add_functions_map_eq; [| eassumption |]. eapply get_list_fundefs. eassumption.
           ++ intros y Hin Hin'. eapply FromList_map_image_FromList in Hin.
              eapply Fundefs_lambda_lift_name_in_fundefs2 in Hin'; [| eassumption ].
              rewrite Add_functions_name_in_fundefs in Hin'; [| eassumption | eassumption ].
              eapply Hd1. constructor. eapply image_monotonic; [| eassumption ].
              eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
              intros x Hinx. do 4 eexists. split; eassumption. left. now inv Hin'. 
           ++ eapply Disjoint_Included; [| | eapply Hd5 ]; sets.
              intros z Hin. do 4 eexists. eauto.
        -- eassumption.
        -- eassumption.



  Lemma Exp_lambda_lift_Ecase ζ σ x P S e S' :
    Exp_lambda_lift ζ σ (Ecase x P) S e S' ->
    exists P', e = Ecase (σ x) P' /\
          Forall2 (fun p p' : ctor_tag * exp => fst p = fst p') P P'.
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
      edestruct preord_env_P_inj_get_list_l as [vs' [Hgetl' Hprevs]]; try eassumption.
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
      erewrite get_list_app; try eassumption. reflexivity.
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
