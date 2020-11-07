Require Import L6.cps L6.size_cps L6.cps_util L6.eval L6.logical_relations L6.set_util L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.alpha_conv L6.functions L6.uncurry L6.uncurry_rel
        L6.shrink_cps_correct L6.algebra.
Require Import FunInd.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Require Import Common.compM.
Require Import Lia.

Require L6.Prototype L6.cps_proto L6.proto_util L6.uncurry_proto.

Import ListNotations MonadNotation.

Section uncurry_correct.

  Variable (pr : prims).
  Variable (cenv : ctor_env).
  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.
  (* Context (P1 : nat -> @PostT fuel trace) (PG : @PostGT fuel trace). *)
  Variable (Post : @PostT fuel trace).
  Variable (PostG : @PostGT fuel trace).

  Ltac easy_post :=
    assumption ||
    match goal with
    | |- inclusion _ ?R ?R => now unfold inclusion
    end.

  Context (Hpost_prop : Post_properties cenv Post Post PostG)
          (Hpost_propG : Post_properties cenv PostG PostG PostG).

  Context (Hpost_curry :
             forall e rho rho' rho'' c1 c2 cout1 cout2 f1 ft1 fv1 gv1, 
               Post (e, rho, c1, cout1) (e, rho'', c2, cout2) ->
               PostG (e, rho, c1, cout1)
                     (Eapp f1 ft1 (gv1 ++ fv1), rho', plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1))), plus cout2 (one (Eapp f1 ft1 (gv1 ++ fv1))))). 
  
  Context (Hpost_idemp : inclusion _ (comp Post Post) Post).
  Context (Hpost_inclusion' : inclusion _ PostG Post).

  Lemma preord_val_fundefs Post' k rho rho1 fds f
        (Hpost_prop' : Post_properties cenv Post' Post' Post'):
    preord_env_P cenv Post' (occurs_free_fundefs fds) k rho rho1 ->
    preord_val cenv Post' k (Vfun rho fds f) (Vfun rho1 fds f).
  Proof.
    rewrite preord_val_eq. simpl; intros.
    pose (Hlen := H2). apply set_lists_length in Hlen. rewrite <- Hlen in H0.
    rename rho1' into rho'.
    eapply length_exists_set_lists in H0. destruct H0 as [rho1' Hrho1'].
    do 3 eexists. split; [eassumption|split]; [eassumption|].

    intros Hj Hvs. apply preord_exp_refl. eassumption.
    
    assert (preord_env_P cenv Post' (occurs_free_fundefs fds :|: name_in_fundefs fds) j
                         (def_funs fds fds rho rho)
                         (def_funs fds fds rho1 rho1)). {
      apply preord_env_P_monotonic with (k := k). omega.
      apply preord_env_P_def_funs_cor. eassumption.
      eapply preord_env_P_antimon; [eassumption|].
      auto with Ensembles_DB.
    }
    clear H.
    eapply preord_env_P_set_lists_l; [eassumption| |eassumption|eauto|eauto].
    
    
    apply find_def_correct in H1.
    assert (occurs_free e1 \\ FromList xs1 \subset occurs_free_fundefs fds :|: name_in_fundefs fds). {
      apply occurs_free_in_fun in H1.
      apply Setminus_Included_Included_Union.
      rewrite Union_commut.
      now rewrite Union_commut with (s1 := occurs_free_fundefs fds).
    }

    intros. assert ((occurs_free e1 \\ FromList xs1) x) by (now split).
    now apply H.
  Qed.

  Lemma preord_env_P_union_converse : forall A B k rho rho1,
    preord_env_P cenv Post (A :|: B) k rho rho1 ->
    preord_env_P cenv Post A k rho rho1 /\
    preord_env_P cenv Post B k rho rho1.
  Proof.
    split; intros a Hin; apply H; [now left|now right].
  Qed.

  Lemma preord_env_P_set_lists_extend: forall cenv Post k vs vs1 vs2 P rho1 rho2 rho1' rho2',
    preord_env_P cenv Post (P \\ FromList vs) k rho1 rho2 ->
    Some rho1' = set_lists vs vs1 rho1 ->
    Some rho2' = set_lists vs vs2 rho2 ->
    Forall2 (preord_val cenv Post k) vs1 vs2 ->
    preord_env_P cenv Post P k rho1' rho2'.
  Proof.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply set_lists_length in Hrho1'; discriminate].
      destruct vs2; [|apply set_lists_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a Ha; split; [apply Ha|inversion 1].
    - destruct vs1; [apply set_lists_length in Hrho1'; discriminate|].
      destruct vs2; [apply set_lists_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (set_lists vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (set_lists vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a' Ha'; split; [inv Ha'; now inv H|];
        intros contra; inv contra;
        [inv Ha'; inv H; contradiction H2; easy|inv Ha'; inv H0; contradiction].
  Qed.

  Lemma preord_env_P_set_lists_extend': forall cenv Post k vs vs1 vs2 P rho1 rho2 rho1' rho2',
    preord_env_P cenv Post P k rho1 rho2 ->
    Some rho1' = set_lists vs vs1 rho1 ->
    Some rho2' = set_lists vs vs2 rho2 ->
    Forall2 (preord_val cenv Post k) vs1 vs2 ->
    preord_env_P cenv Post P k rho1' rho2'.
  Proof with eauto with Ensembles_DB.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply set_lists_length in Hrho1'; discriminate].
      destruct vs2; [|apply set_lists_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon...
    - destruct vs1; [apply set_lists_length in Hrho1'; discriminate|].
      destruct vs2; [apply set_lists_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (set_lists vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (set_lists vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon...
  Qed.

  Lemma preord_env_P_subst : forall cenv Post P k rho rho1 rho' rho1',
    preord_env_P cenv Post P k rho rho1 ->
    (forall a, P a -> M.get a rho = M.get a rho') ->
    (forall a, P a -> M.get a rho1 = M.get a rho1') ->
    preord_env_P cenv Post P k rho' rho1'.
  Proof.
    intros cenv' Post' P k rho rho1 rho' rho1' Heq Hrho Hrho1 a Ha v1 Hv1.
    rewrite <- Hrho in Hv1; [|apply Ha].
    rewrite <- Hrho1; [|apply Ha].
    now apply Heq.
  Qed.

  Lemma Forall2_preord_val_monotonic : forall cenv Post k k1 l1 l2,
    k1 <= k ->
    Forall2 (preord_val cenv Post k) l1 l2 ->
    Forall2 (preord_val cenv Post k1) l1 l2.
  Proof.
    induction l1; [now inversion 2|intros].
    destruct l2; inv H0.
    constructor; [|now apply IHl1].
    eapply preord_val_monotonic; eassumption.
  Qed.

  Lemma preord_var_env_extend_neq_r : forall cenv Post k rho rho1 a b v,
    preord_var_env cenv Post k rho rho1 a a ->
    a <> b ->
    preord_var_env cenv Post k rho (M.set b v rho1) a a.
  Proof.
    unfold preord_var_env; intros.
    rewrite M.gso; auto.
  Qed.
  Lemma def_funs_get_neq : forall B' B B1 rho a,
    ~ In _ (name_in_fundefs B') a ->
    M.get a (def_funs B1 (fundefs_append B' B) rho rho) =
    M.get a (def_funs B1 B rho rho).
  Proof.
    induction B'.
    - intros; simpl.
      rewrite M.gso.
      apply IHB'; intros contra; contradiction H; now right.
      intros contra; subst; contradiction H; now left.
    - auto.
  Qed.
  Lemma preord_var_env_def_funs_neq : forall cenv Post k B' B B1 B2 B3 rho rho1 a,
    preord_var_env cenv Post k
                   (def_funs B2 B rho rho)
                   (def_funs B3 B1 rho1 rho1) a a ->
    ~ In _ (name_in_fundefs B') a ->
    preord_var_env cenv Post k
                   (def_funs B2 (fundefs_append B' B) rho rho)
                   (def_funs B3 (fundefs_append B' B1) rho1 rho1) a a.
  Proof.
    intros.
    unfold preord_var_env.
    do 2 (rewrite def_funs_get_neq; auto).
  Qed.

  Lemma preord_var_env_extend' : forall cenv Post rho1 rho2 k x y v1 v2,
    (y <> x -> preord_var_env cenv Post k rho1 rho2 y y) ->
    preord_val cenv Post k v1 v2 ->
    preord_var_env cenv Post k (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros.
    unfold preord_var_env.
    split_var_eq y x; subst.
    do 2 rewrite M.gss; intros v0 Hv0; inv Hv0; eexists; split; eauto.
    do 2 (rewrite M.gso; auto).
    now apply H.
  Qed.



  (* unnesting fundefs_curried case of uncurry_step_correct *)
  Lemma uncurry_step_correct_fundefs_curried :
    forall k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1 already_uncurried,
    let curried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds) in
    let uncurried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv1)
                (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k0 kt [g]))
                (Fcons f1 ft1 (gv ++ fv) ge fds)) in
    (used_vars e :|: used_vars_fundefs curried \subset s) ->
    (used_vars e :|: used_vars_fundefs uncurried \subset
       s :|: FromList gv1 :|: FromList fv1 :|: [set f1]) ->
    (match M.get g already_uncurried with
         | Some true => true | Some false => false | None => false end
     = false) ->
    (occurs_in_exp g ge = false) ->
    (occurs_in_exp k0 ge = false) ->
    (unique_bindings_fundefs curried) ->
    (used_vars_fundefs curried \subset s) ->
    (unique_bindings_fundefs uncurried) ->
    (fresh_copies s gv1) ->
    (length gv1 = length gv) ->
    (fresh_copies (s :|: FromList gv1) fv1) ->
    (length fv1 = length fv) ->
    (~ In var (s :|: FromList gv1 :|: FromList fv1) f1) ->
    (preord_env_P cenv PostG (occurs_free (Efun curried e)) k rho rho1) ->
    preord_exp cenv Post PostG k (Efun curried e, rho) (Efun uncurried e, rho1).
  Proof with unfold used_vars in *; eauto 15 with Ensembles_DB.
    intros k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1
           already_uncurried curried uncurried
           Hcurried_used Huncurried_used Halready_uncurried
           Hg_nonrec Hk0_nonrec Hcurried_unique_fundefs Hcurried_used_fundefs
           Huncurried_unique_fundefs Hgv1_fresh Hgv_gv1 Hfv1_fresh Hfv_fv1 Hf1_fresh Henv.
    eapply preord_exp_fun_compat. now eapply Hpost_prop. now eapply Hpost_prop.
    apply preord_exp_refl. eassumption.
    intros h Hh; unfold preord_var_env.

    (* useful facts for later *)
    assert (Hf1_gv1 : ~ List.In f1 gv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      assumption.
    }
    assert (Hf1_k0fv1 : ~ List.In f1 (k0 :: fv1)). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      intros contra; inv contra; [|contradiction].
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H7. contradiction (H f1).
      split.
      constructor; now left.
      now left.
    }
    assert (Hg_f1 : g <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H8.
      contradiction (H f1).
      split.
      constructor; constructor; now left.
      constructor; now left.
    }
    assert (f_f1 : f <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. contradiction H5; constructor; now left.
    }
    assert (Hk0_fv1 : ~ List.In k0 fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. now inv H10.
    }
    assert (Hg_fv1 : ~ List.In g fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6.
      contradiction (H g).
      split.
      constructor; constructor; now left.
      now right.
    }
    assert (Hk0_g : k0 <> g). {
      intros contra; subst.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6. contradiction (H g).
      split.
      constructor; constructor; now left.
      now left.
    }
    assert (Hf1_pre_fds : ~ name_in_fundefs pre_fds f1). {
      intros contra.
      apply fundefs_append_unique_l with (f := f1) in Huncurried_unique_fundefs; auto.
      contradiction Huncurried_unique_fundefs.
      right; now left.
    }
    assert (Hf_pre_fds : ~ name_in_fundefs pre_fds f). {
      intros contra.
      apply fundefs_append_unique_l with (f := f) in Hcurried_unique_fundefs; auto.
      contradiction Hcurried_unique_fundefs.
      now left.
    }
    assert (Hcurried_uncurried : name_in_fundefs curried \subset name_in_fundefs uncurried). {
      intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      split_var_in_fundefs a pre_fds Ha_pre_fds.
      now left.
      split_var_eq a f; subst.
      right; now left.
      split_var_in_fundefs a fds Ha_fds.
      right; right; now right.
      rewrite fundefs_append_name_in_fundefs in Ha; [|reflexivity].
      inv Ha; try contradiction.
      inv H; try contradiction.
      inv H0; contradiction.
    }
    assert (Hgv_g : ~ List.In g gv). {
      intros contra.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H11.
      now inv H2.
    }
    assert (Hpre_fds_curried : name_in_fundefs pre_fds \subset name_in_fundefs curried). {
      subst curried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hpre_fds_uncurried : name_in_fundefs pre_fds \subset name_in_fundefs uncurried). {
      subst uncurried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hf1_ge : ~ In _ (occurs_free ge) f1). {
      intros contra1.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; right.
      subst curried; apply occurs_free_fundefs_append; auto.
      constructor; auto.
      inversion 1; subst.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H8; contradiction (H0 f1).
        split; [constructor; now left|now left].
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H14.
        contradiction H20.
        apply Ensemble_In; rewrite FromList_app.
        now right.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros contra; contradiction H14; now apply name_in_fundefs_bound_var_fundefs.
      - apply Free_Efun2.
        constructor; auto; [|inversion 1].
        intros contra.
        apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        contradiction H18; apply Ensemble_In; rewrite FromList_app; now left.
    }
    assert (Hf1_curried : ~ In _ (name_in_fundefs curried) f1). {
      intros contra.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; left.
      now apply name_in_fundefs_bound_var_fundefs.
    }
    assert (Hf_curried : In _ (name_in_fundefs curried) f). {
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      right; now left.
    }
    assert (Hf_uncurried : In _ (name_in_fundefs uncurried) f) by now apply Hcurried_uncurried.

    split_var_in_fundefs
      h
      curried 
      Hfds; clear Hfds; rename n into Hfds; simpl in Hfds.
    - (* h\in pre_fds ++ f |: fundefs(fds) *)
      rewrite def_funs_eq; auto.
      rewrite def_funs_eq; [|now apply Hcurried_uncurried].
      intros v1 Hv1; inv Hv1.
      eexists; split; [reflexivity|].
      generalize dependent h. generalize dependent e.
      induction k as [k IHk] using lt_wf_rec1.
      (* Opaque preord_exp. *)
      intros e Hcurried_used Huncurried_used Henv h Hh Hfds.
      split_var_eq h f; subst; rewrite preord_val_eq; simpl.
      + (* h = f *)
        rename curried into curried'; pose (curried := curried').
        rename uncurried into uncurried'; pose (uncurried := uncurried').
        subst curried'; subst uncurried'.
        do 2 (rewrite find_def_fundefs_append_neq; auto; simpl).
        destruct (M.elt_eq f f) as [Heq|]; [clear Heq|contradiction].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hsome Hrho'; inv Hsome.
        assert (Hrho1' : length (k0 :: fv1) = length vs2). {
          apply set_lists_length in Hrho'.
          rewrite <- Hlen_vs1_vs2.
          rewrite <- Hrho'.
          simpl; rewrite Hfv_fv1.
          reflexivity.
        }
        eapply length_exists_set_lists in Hrho1'.
        destruct Hrho1' as [rho1' Hrho1'].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk1 Hvs1_vs2].
        eapply preord_exp_fun_compat.
        now eapply Hpost_propG.
        now eapply Hpost_propG.
        
        apply preord_exp_refl. eassumption.

        (* wrt k0 and g, the environments
             rho'' = g + [k0 :: fv -> vs1] + curried f + fds + rho
             rho1'' = uncurried g + [k0 :: fv1 -> vs2] + uncurried f + f1 + fds + rho1
           agree. *)
        destruct vs1 as [|hvs1 tvs1]; [apply set_lists_length in Hrho'; inv Hrho'|].
        destruct vs2 as [|hvs2 tvs2]; [apply set_lists_length in Hrho1'; inv Hrho1'|].
        intros a Ha.
        inv Ha; [rename a into k0|inv H3]; [|rename a into g|inv H].
        * (* k0: hvs1 == hvs2 *)
          unfold preord_var_env; simpl.
          do 2 (rewrite M.gso; [|assumption]).
          apply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]].
          apply set_set_lists in Hrho1'; destruct Hrho1' as [rho1'k0 [Hrho1' Hrho1'k0]].
          subst rho'; subst rho1'; do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|inv Hvs1_vs2].
          eapply preord_val_monotonic; eauto; omega.
        * (* g *)
          unfold preord_var_env; simpl.
          do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
          rewrite preord_val_eq; simpl.
          destruct (M.elt_eq g g) as [Heq|]; [clear Heq|contradiction].
          intros vs3 vs4 k2 t0 xs1 e1 rho'' Hlen_vs3_vs4 Hsome Hrho''.
          inversion Hsome; subst t0; subst xs1; subst e1; clear Hsome.
          assert (Hrho1'' : length gv1 = length vs4). {
            apply set_lists_length in Hrho''.
            rewrite <- Hlen_vs3_vs4.
            rewrite <- Hrho''.
            assumption.
          }
          eapply length_exists_set_lists in Hrho1''; destruct Hrho1'' as [rho1'' Hrho1''].
          do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk2 Hvs3_vs4].
          assert (Hrho''' : length (gv ++ fv) = length (vs4 ++ tvs2)). {
            do 2 rewrite app_length.
            apply set_lists_length in Hrho1''.
            rewrite <- Hrho1''.
            rewrite <- Hgv_gv1.
            apply set_lists_length in Hrho1'.
            inv Hrho1'.
            rewrite <- Hfv_fv1.
            reflexivity.
          }
          (* Transparent preord_exp. *) intros v1 c1 cout Hc1 Hv1. 
          apply length_exists_set_lists with
            (rho0 := (def_funs uncurried uncurried rho1 rho1)) in Hrho'''.
          destruct Hrho''' as [rho''' Hrho'''].
          assert (Hgoal : preord_exp cenv Post PostG k2 (ge, rho'') (ge, rho''')). {
            apply preord_exp_refl. eassumption.

            (* wrt free variables of ge, the environments
                 rho'' = [gv -> vs3] + g + [k0 :: fv -> vs1] + curried f + fds + rho
                 rho''' = [gv ++ fv -> vs4 ++ tvs2] + uncurried f + f1 + fds + rho1
               agree. 
             *)

            (* rho''g := rho'' \ g *)
            eapply set_lists_set_permut in Hgv_g; [|apply Hrho''].
            destruct Hgv_g as [rho''g [Hrho''g Hrho''_rho''g]].
            eapply preord_env_P_subst; [|intros a Ha;symmetry; apply Hrho''_rho''g|reflexivity]. 
            apply preord_env_P_set_not_in_P_l;
              [|apply Disjoint_Union_r with (s1 := bound_var ge);
                replace (bound_var ge :|: occurs_free ge) with (used_vars ge) by reflexivity;
                now rewrite <- occurs_in_exp_correct].

            (* split [gv ++ fv -> vs4 ++ tvs2] into [gv -> vs4] + [fv -> tvs2] *)
            symmetry in Hrho'''; eapply set_lists_app in Hrho''';
              [|apply set_lists_length in Hrho1''; now rewrite <- Hrho1''].
            destruct Hrho''' as [rho'''fv [Hrho'''fv Hrho''']].

            (* [[gv]](rho''g) ==_k2 [[gv]](rho''') *)
            eapply preord_env_P_set_lists_extend; eauto.

            (* rho'k0 := rho' \ k0 *)
            eapply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]]; subst rho'.
            apply preord_env_P_set_not_in_P_l;
              [|eapply Disjoint_Included_l;
                  [|rewrite <- occurs_in_exp_correct];
                  [|apply Hk0_nonrec];
                apply Setminus_Included_preserv;
                eapply Included_Union_r].

            (* [[fv]](rho'k0) ==_k2 [[gv]](rho''') *)
            inv Hvs1_vs2.
            eapply preord_env_P_set_lists_extend; eauto;
              [|eapply Forall2_preord_val_monotonic];
              [| |eassumption];
              [|omega].

            intros a Ha.
            (* remove pre_fds from (pre_fds + curried f + fds + rho),
                                   (pre_fds + f + f1 + fds + rho1) *)
            split_var_in_fundefs a pre_fds Hpre_fds. {
              unfold preord_var_env.
              rewrite def_funs_eq; [|now apply Hpre_fds_curried].
              rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
                [omega| | | |constructor| |omega].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; omega.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
                now apply Free_Efun2.
              * apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            }
            rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            apply preord_var_env_def_funs_neq; auto.

            (* remove curried f, uncurried f *)
            simpl; apply preord_var_env_extend'. intros Ha_f.

            (* remove f1 *)
            apply preord_var_env_extend_neq_r.

            (* remove fds *) {
            rename Hfds into Hname_fds.
            split_var_in_fundefs a fds Hfds.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_eq; [|assumption]).
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
                [omega| | | |constructor| |omega].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; do 2 apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; omega.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
                now apply Free_Efun2.
              * apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_neq; auto).
              assert ((occurs_free ge
                                   \\ FromList gv
                                   \\ FromList fv
                                   \\ [set f]
                                   \\ name_in_fundefs pre_fds
                                   \\ name_in_fundefs fds) a). {
                do 3 (split; auto).
                intros contra; now inv contra.
              }
              clear Ha; clear n; clear Ha_f; clear n0; generalize dependent a.
              eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|apply Henv]; omega.
              intros a Ha; inv Ha; inv H; inv H1; inv H.
              apply Free_Efun2.
              apply occurs_free_fundefs_append; auto.
              apply Free_Fcons1;
                [intros contra; subst; now contradiction H5| |assumption|].
              * intros contra; inv contra; [|contradiction].
                rewrite occurs_in_exp_correct in Hk0_nonrec.
                rewrite Disjoint_Singleton_In in Hk0_nonrec; auto with Decidable_DB.
                contradiction Hk0_nonrec; inv H1; now right.
              * inv H1.
                apply Free_Efun2; apply Free_Fcons1; [|assumption|inversion 1|assumption].
                intros contra; subst.
                rewrite occurs_in_exp_correct in Hg_nonrec.
                rewrite Disjoint_Singleton_In in Hg_nonrec; auto with Decidable_DB. 
                contradiction Hg_nonrec; now right.
            }

            (* f1 not in (occurs_free ge) *) {
              intros contra; subst; inv Ha; inv H.
              contradiction.
            }

            (* [[curried f]](f + fds + rho) ==_k2 [[uncurried f]](f + f1 + fds + rho1) *) {
              eapply preord_val_monotonic; [eapply IHk with (m := k1); eauto|]; try omega.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
            }
          }
          unfold preord_exp' in Hgoal.
          specialize Hgoal with (v1 := v1) (cin := c1) (cout := cout); destruct Hgoal; [apply Hc1|apply Hv1|].
          rename x into v2; destruct H as [c2 [cout' [Hv2 [Hvpost Hv1_v2]]]].
          eexists; exists (plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))),
                   (plus cout' (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))); split; [|split; [|eassumption]].
          2: { eapply Hpost_curry. eassumption. }
          
          apply BStepf_run.
          eapply BStept_app; eauto.
          { erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
            rewrite M.gso; [|auto].
            erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
            rewrite def_funs_get_neq; auto.
            simpl; rewrite M.gso; auto.
            now rewrite M.gss. }
          { apply get_list_app.
            eapply get_list_set_lists; [now inv Hgv1_fresh|symmetry; eassumption].
            erewrite get_list_set_lists_Disjoint;
              [|inv Hfv1_fresh; apply Disjoint_Union_r in H; apply H|symmetry; eassumption].
            rewrite get_list_set_neq; [|assumption].
            apply set_set_lists in Hrho1'.
            destruct Hrho1' as [rho1'k0 [Hrho1'k0 Hrho1']]; subst rho1'.
            rewrite get_list_set_neq; [|assumption].
            eapply get_list_set_lists; [now inv Hfv1_fresh|symmetry; eassumption]. }
          { rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            rewrite find_def_fundefs_append_neq; auto.
            simpl; destruct (M.elt_eq f1 f) as [|Heq]; [now subst|clear Heq].
            destruct (M.elt_eq f1 f1) as [Heq|]; [clear Heq|contradiction].
            reflexivity. }
      + (* h \in pre_fds ++ fds *)
        assert (Hf' : h <> f). {
          intros contra; subst; inv Hcurried_unique_fundefs.
          now apply name_in_fundefs_bound_var_fundefs in Hfds.
          contradiction. }
        assert (Hf1: h <> f1). {
          (* f1 is not in curried (freshly generated by uncurrier) *)
          intros contra; subst; contradiction. }
        destruct (M.elt_eq h f) as [|Heq]; [contradiction|clear Heq].
        destruct (M.elt_eq h f1) as [|Heq]; [contradiction|clear Heq].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hfind_def Hrho'.
        assert (Hrho1' : length xs1 = length vs2). {
          apply set_lists_length in Hrho'.
          now rewrite <- Hlen_vs1_vs2. }
        eapply length_exists_set_lists in Hrho1'; destruct Hrho1' as [rho1' Hrho1'].
        exists xs1, e1; eexists; split; [|split]; [|eassumption|intros Hk1 Hvs1_vs2].
        (* only f is uncurried, so h in uncurried = h in curried (Hfind_def) *)
        assert (HLR : In _ (name_in_fundefs curried) h) by auto.
        rewrite fundefs_append_name_in_fundefs in HLR; [|reflexivity].
        split_var_in_fundefs h pre_fds Hh_pre_fds.
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_eq; auto.
        rewrite find_def_fundefs_append_eq in Hfind_def; auto.
        inv HLR; [contradiction|]; inv H; [inv H0; contradiction|].
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_neq; auto.
        rewrite find_def_fundefs_append_neq in Hfind_def; auto.
        simpl; simpl in Hfind_def.
        destruct (M.elt_eq h f); try contradiction.
        destruct (M.elt_eq h f1); try contradiction; auto.
        apply preord_exp_refl. eassumption.

        (* wrt free variables of e1, the environments
             rho' = [xs1 -> vs1] + f + fds + rho
             rho1' = [xs1 -> vs2] + f + f1 + fds + rho1
           agree. 
         *)

        (* [[xs1]](rho') ==_k1 [[xs1]](rho1') *)
        eapply preord_env_P_set_lists_extend; eauto.

        (* remove pre_fds *)
        intros a Ha.
        split_var_in_fundefs a pre_fds Hpre_fds. {
          unfold preord_var_env.
          rewrite def_funs_eq; [|now apply Hpre_fds_curried].
          rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
          intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
          eapply preord_val_monotonic;
          [apply IHk with (m := k - 1) (e := Ehalt a)|]; [omega| | | |constructor| |omega].
          * rewrite Union_Same_set; [assumption|].
            unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a' Ha'; inv Ha'.
            inv H3; contradiction H1.
            apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            now apply Free_Efun2.
          * apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
        }
        rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
        apply preord_var_env_def_funs_neq; auto.

        (* remove f and f1 *)
        simpl; apply preord_var_env_extend'. intros Ha_f.
        apply preord_var_env_extend_neq_r.

        (* remove fds *) {
          split_var_in_fundefs a fds Hfds'; unfold preord_var_env; simpl.
          - do 2 (rewrite def_funs_eq; [|assumption]).
            intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
            (* todo: basically a duplicate with the previous application of IH *)
            eapply preord_val_monotonic;
            [apply IHk with (m := k - 1) (e := Ehalt a)|]; [omega| | | |constructor| |omega].
            + rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            + apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free e1
                                 \\ FromList xs1
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n1; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            subst curried.
            split_var_in_fundefs h pre_fds Hh_pre_fds.
            + apply occurs_free_fundefs_append_l.
              intros contra; inv contra; auto.
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq_l
                with (B1 := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds); auto.
              apply Hfind_def.
              intros contra; inv contra.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              now inv H.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              right; now right.
            + apply occurs_free_fundefs_append; auto.
              apply Free_Fcons2; [|intros contra; subst; now contradiction H3].
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq
                with (B := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) Fnil); auto.
              rewrite <- find_def_fundefs_append_neq with (B := pre_fds); auto.
              apply Hfind_def.
              auto.
              intros contra; inv contra; now inv H.
        }

        (* f1 never occurs in the definition of h *)
        {
          intros contra; subst.
          rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
          rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
          contradiction Hf1_fresh1.
          apply Hcurried_used_fundefs.
          right.
          eapply find_def_is_Some_occurs_free_fundefs; eauto; now inv Ha.
        }

        (* [[curried f]](rho') ==_k1 [[uncurried f]](rho1') *)
        eapply preord_val_monotonic;
        [apply IHk with (m := k - 1) (e := Ehalt f)|omega]; [omega| | | |constructor|assumption].
        (* todo: basically a duplicate with the previous application of IH,
           but with left instaed of right soemtimes *)
        * rewrite Union_Same_set; [assumption|].
          unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
          rewrite occurs_free_Ehalt.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [|eassumption]; omega.
          repeat normalize_occurs_free.
          intros b Hb; inv Hb.
          now left.
          inv H.
          contradiction H1.
          now inv H0.
    - (* h\not\in pre_fds ++ f |: fundefs(fds) *)
      assert (h <> f). {
        intros contra; subst.
        contradiction Hfds.
      }
      assert (h <> f1). {
        intros contra; subst.
        rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
        rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
        contradiction Hf1_fresh1.
        apply Hcurried_used.
        now left; right.
      }
      simpl.
      rename curried into curried'; pose (curried := curried'); subst curried'.
      rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
      assert (~ name_in_fundefs fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        right; now right.
      }
      assert (~ name_in_fundefs pre_fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        now left.
      }
      do 2 (rewrite def_funs_get_neq; auto).
      simpl; do 3 (rewrite M.gso; auto).
      do 2 (rewrite def_funs_neq; [|assumption]).
      unfold preord_env_P, preord_var_env in Henv.
      intros v1 Hv1.
      edestruct Henv as [v2 [Hv2 Hv12]]; try eassumption.
      + constructor; [simpl|assumption]; auto.
      + eexists; split; eapply preord_val_monotonic in Hv12; eauto; omega.
  Qed.

  (* the same thing, but for anf uncurrying *)
  Lemma uncurry_step_correct_fundefs_curried_anf :
    forall k e f ft fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1 already_uncurried,
    let curried := fundefs_append pre_fds
        (Fcons f ft fv (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds) in
    let uncurried := fundefs_append pre_fds
        (Fcons f ft fv1
                (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Ehalt g))
                (Fcons f1 ft1 (gv ++ fv) ge fds)) in
    (used_vars e :|: used_vars_fundefs curried \subset s) ->
    (used_vars e :|: used_vars_fundefs uncurried \subset
       s :|: FromList gv1 :|: FromList fv1 :|: [set f1]) ->
    (match M.get g already_uncurried with
         | Some true => true | Some false => false | None => false end
     = false) ->
    (occurs_in_exp g ge = false) ->
    (unique_bindings_fundefs curried) ->
    (used_vars_fundefs curried \subset s) ->
    (unique_bindings_fundefs uncurried) ->
    (fresh_copies s gv1) ->
    (length gv1 = length gv) ->
    (fresh_copies (s :|: FromList gv1) fv1) ->
    (length fv1 = length fv) ->
    (~ In var (s :|: FromList gv1 :|: FromList fv1) f1) ->
    (preord_env_P cenv PostG (occurs_free (Efun curried e)) k rho rho1) ->
    preord_exp cenv Post PostG k (Efun curried e, rho) (Efun uncurried e, rho1).
  Proof with unfold used_vars in *; eauto 15 with Ensembles_DB.
    intros k e f ft fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1
           already_uncurried curried uncurried
           Hcurried_used Huncurried_used Halready_uncurried
           Hg_nonrec Hcurried_unique_fundefs Hcurried_used_fundefs
           Huncurried_unique_fundefs Hgv1_fresh Hgv_gv1 Hfv1_fresh Hfv_fv1 Hf1_fresh Henv.
    eapply preord_exp_fun_compat. now eapply Hpost_prop. now eapply Hpost_prop.
    apply preord_exp_refl. eassumption.
    intros h Hh; unfold preord_var_env.

    (* useful facts for later *)
    assert (Hf1_gv1 : ~ List.In f1 gv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      assumption.
    }
    assert (Hf1_k0fv1 : ~ List.In f1 fv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      intros contra.
      inv HR. inv H7. contradiction (H f1).
      split.
      constructor; now left.
      apply contra.
    }
    assert (Hg_f1 : g <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H8.
      contradiction (H f1).
      split.
      constructor; constructor; now left.
      constructor; now left.
    }
    assert (f_f1 : f <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. contradiction H5; constructor; now left.
    }
    assert (Hg_fv1 : ~ List.In g fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6.
      contradiction (H g).
      split.
      constructor; constructor; now left.
      apply contra.
    }
    assert (Hf1_pre_fds : ~ name_in_fundefs pre_fds f1). {
      intros contra.
      apply fundefs_append_unique_l with (f := f1) in Huncurried_unique_fundefs; auto.
      contradiction Huncurried_unique_fundefs.
      right; now left.
    }
    assert (Hf_pre_fds : ~ name_in_fundefs pre_fds f). {
      intros contra.
      apply fundefs_append_unique_l with (f := f) in Hcurried_unique_fundefs; auto.
      contradiction Hcurried_unique_fundefs.
      now left.
    }
    assert (Hcurried_uncurried : name_in_fundefs curried \subset name_in_fundefs uncurried). {
      intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      split_var_in_fundefs a pre_fds Ha_pre_fds.
      now left.
      split_var_eq a f; subst.
      right; now left.
      split_var_in_fundefs a fds Ha_fds.
      right; right; now right.
      rewrite fundefs_append_name_in_fundefs in Ha; [|reflexivity].
      inv Ha; try contradiction.
      inv H; try contradiction.
      inv H0; contradiction.
    }
    assert (Hgv_g : ~ List.In g gv). {
      intros contra.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H11.
      now inv H2.
    }
    assert (Hpre_fds_curried : name_in_fundefs pre_fds \subset name_in_fundefs curried). {
      subst curried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hpre_fds_uncurried : name_in_fundefs pre_fds \subset name_in_fundefs uncurried). {
      subst uncurried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hf1_ge : ~ In _ (occurs_free ge) f1). {
      intros contra1.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; right.
      subst curried; apply occurs_free_fundefs_append; auto.
      constructor; auto.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros Hin.
        contradiction H18.
        apply Ensemble_In; rewrite FromList_app.
        now right.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros contra; contradiction H14; now apply name_in_fundefs_bound_var_fundefs.
      - apply Free_Efun2.
        constructor; auto; [|inversion 1].
        intros contra.
        apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        contradiction H18; apply Ensemble_In; rewrite FromList_app; now left.
    }
    assert (Hf1_curried : ~ In _ (name_in_fundefs curried) f1). {
      intros contra.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; left.
      now apply name_in_fundefs_bound_var_fundefs.
    }
    assert (Hf_curried : In _ (name_in_fundefs curried) f). {
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      right; now left.
    }
    assert (Hf_uncurried : In _ (name_in_fundefs uncurried) f) by now apply Hcurried_uncurried.

    split_var_in_fundefs
      h
      curried 
      Hfds; clear Hfds; rename n into Hfds; simpl in Hfds.
    - (* h\in pre_fds ++ f |: fundefs(fds) *)
      rewrite def_funs_eq; auto.
      rewrite def_funs_eq; [|now apply Hcurried_uncurried].
      intros v1 Hv1; inv Hv1.
      eexists; split; [reflexivity|].
      generalize dependent h. generalize dependent e.
      induction k as [k IHk] using lt_wf_rec1.
      (* Opaque preord_exp. *)
      intros e Hcurried_used Huncurried_used Henv h Hh Hfds.
      split_var_eq h f; subst; rewrite preord_val_eq; simpl.
      + (* h = f *)
        rename curried into curried'; pose (curried := curried').
        rename uncurried into uncurried'; pose (uncurried := uncurried').
        subst curried'; subst uncurried'.
        do 2 (rewrite find_def_fundefs_append_neq; auto; simpl).
        destruct (M.elt_eq f f) as [Heq|]; [clear Heq|contradiction].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hsome Hrho'; inv Hsome.
        assert (Hrho1' : length fv1 = length vs2). {
          apply set_lists_length in Hrho'.
          rewrite <- Hlen_vs1_vs2.
          rewrite <- Hrho'.
          simpl; rewrite Hfv_fv1.
          reflexivity.
        }
        eapply length_exists_set_lists in Hrho1'.
        destruct Hrho1' as [rho1' Hrho1'].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk1 Hvs1_vs2].
        eapply preord_exp_fun_compat. now eapply Hpost_propG.
        now eapply Hpost_propG.
        apply preord_exp_refl. eassumption.
        (* wrt g, the environments
             rho'' = g + [fv -> vs1] + curried f + fds + rho
             rho1'' = uncurried g + [fv1 -> vs2] + uncurried f + f1 + fds + rho1
           agree. *)
        (* destruct vs1 as [|hvs1 tvs1]; [apply set_lists_length in Hrho'; inv Hrho'|]. *)
        (* destruct vs2 as [|hvs2 tvs2]; [apply set_lists_length in Hrho1'; inv Hrho1'|]. *)
        rename vs1 into tvs1, vs2 into tvs2.
        intros a Ha.
        inv Ha; rename a into g.
        unfold preord_var_env; simpl.
        do 2 rewrite M.gss.
        intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
        rewrite preord_val_eq; simpl.
        destruct (M.elt_eq g g) as [Heq|]; [clear Heq|contradiction].
        intros vs3 vs4 k2 t0 xs0 e1 rho'' Hlen_vs3_vs4 Hsome Hrho''.
        inversion Hsome; subst t0; subst xs0; subst e1; clear Hsome.
        assert (Hrho1'' : length gv1 = length vs4). {
          apply set_lists_length in Hrho''.
          rewrite <- Hlen_vs3_vs4.
          rewrite <- Hrho''.
          assumption.
        }
        eapply length_exists_set_lists in Hrho1''; destruct Hrho1'' as [rho1'' Hrho1''].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk2 Hvs3_vs4].
        rename xs1 into fv.
        assert (Hrho''' : length (gv ++ fv) = length (vs4 ++ tvs2)). {
          do 2 rewrite app_length.
          apply set_lists_length in Hrho1''.
          rewrite <- Hrho1''.
          rewrite <- Hgv_gv1.
          apply set_lists_length in Hrho1'.
          inv Hrho1'.
          rewrite <- Hfv_fv1.
          reflexivity.
        }
        (* Transparent preord_exp. *) intros v1 c1 cout Hc1 Hv1. 
        apply length_exists_set_lists with
          (rho0 := (def_funs uncurried uncurried rho1 rho1)) in Hrho'''.
        destruct Hrho''' as [rho''' Hrho'''].
        assert (Hgoal : preord_exp cenv Post PostG k2 (ge, rho'') (ge, rho''')). {
          apply preord_exp_refl. eassumption.
          (* wrt free variables of ge, the environments
               rho'' = [gv -> vs3] + g + [k0 :: fv -> vs1] + curried f + fds + rho
               rho''' = [gv ++ fv -> vs4 ++ tvs2] + uncurried f + f1 + fds + rho1
             agree. 
           *)

          (* rho''g := rho'' \ g *)
          eapply set_lists_set_permut in Hgv_g; [|apply Hrho''].
          destruct Hgv_g as [rho''g [Hrho''g Hrho''_rho''g]].
          eapply preord_env_P_subst; [|intros a Ha;symmetry; apply Hrho''_rho''g|reflexivity]. 
          apply preord_env_P_set_not_in_P_l;
            [|apply Disjoint_Union_r with (s1 := bound_var ge);
              replace (bound_var ge :|: occurs_free ge) with (used_vars ge) by reflexivity;
              now rewrite <- occurs_in_exp_correct].

          (* split [gv ++ fv -> vs4 ++ tvs2] into [gv -> vs4] + [fv -> tvs2] *)
          symmetry in Hrho'''; eapply set_lists_app in Hrho''';
            [|apply set_lists_length in Hrho1''; now rewrite <- Hrho1''].
          destruct Hrho''' as [rho'''fv [Hrho'''fv Hrho''']].

          (* [[gv]](rho''g) ==_k2 [[gv]](rho''') *)
          eapply preord_env_P_set_lists_extend; eauto.

          (* rho'k0 := rho' *)
          (* eapply set_set_lists in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]]; subst rho'. *)
          rename rho' into rho'k0, Hrho' into Hrho'k0.
          
          (*
          apply preord_env_P_set_not_in_P_l;
            [|eapply Disjoint_Included_l;
                [|rewrite <- occurs_in_exp_correct];
                [|apply Hk0_nonrec];
              apply Setminus_Included_preserv;
              eapply Included_Union_r].*)

          (* [[fv]](rho'k0) ==_k2 [[gv]](rho''') *)
          (* inv Hvs1_vs2. *)
          eapply preord_env_P_set_lists_extend; eauto;
            [|eapply Forall2_preord_val_monotonic];
            [| |eassumption];
            [|omega].

          intros a Ha.
          (* remove pre_fds from (pre_fds + curried f + fds + rho),
                                 (pre_fds + f + f1 + fds + rho1) *)
          split_var_in_fundefs a pre_fds Hpre_fds. {
            unfold preord_var_env.
            rewrite def_funs_eq; [|now apply Hpre_fds_curried].
            rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
            intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
            eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
              [omega| | | |constructor| |omega].
            * rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity]; left.
              now apply name_in_fundefs_bound_var_fundefs.
            * unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity]; left.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In.
              rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
              now apply Free_Efun2.
            * apply Ensemble_In.
              rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
          }
          rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
          apply preord_var_env_def_funs_neq; auto.

          (* remove curried f, uncurried f *)
          simpl; apply preord_var_env_extend'. intros Ha_f.

          (* remove f1 *)
          apply preord_var_env_extend_neq_r.

          (* remove fds *) {
          rename Hfds into Hname_fds.
          split_var_in_fundefs a fds Hfds.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_eq; [|assumption]).
            intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
            eapply preord_val_monotonic; [apply IHk with (m := k1) (e := Ehalt a)|];
              [omega| | | |constructor| |omega].
            * rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            * unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            * apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free ge
                                 \\ FromList gv
                                 \\ FromList fv
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|apply Henv]; omega.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            apply occurs_free_fundefs_append; auto.
            apply Free_Fcons1;
              [intros contra; subst; now contradiction H3| |assumption|].
            * assumption.
            * inv H1.
              apply Free_Efun2; apply Free_Fcons1; [|assumption|inversion 1|assumption].
              intros contra; subst.
              rewrite occurs_in_exp_correct in Hg_nonrec.
              rewrite Disjoint_Singleton_In in Hg_nonrec; auto with Decidable_DB. 
              contradiction Hg_nonrec; now right.
          }

          (* f1 not in (occurs_free ge) *) {
            intros contra; subst; inv Ha; inv H.
            contradiction.
          }

          (* [[curried f]](f + fds + rho) ==_k2 [[uncurried f]](f + f1 + fds + rho1) *) {
            eapply preord_val_monotonic; [eapply IHk with (m := k1); eauto|]; try omega.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
          }
        }
        unfold preord_exp' in Hgoal.
        specialize Hgoal with (v1 := v1) (cin := c1) (cout := cout); destruct Hgoal; [apply Hc1|apply Hv1|].
        rename x into v2; destruct H as [c2 [cout' [Hv2 [Hvpost Hv1_v2]]]].
        eexists; exists (plus c2 (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))),
                 (plus cout' (one (Eapp f1 ft1 (gv1 ++ fv1) : exp))); split; [|split; [|eassumption]].
        2: { eapply Hpost_curry. eassumption. }
        apply BStepf_run.
        eapply BStept_app; eauto.
        { erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
          rewrite M.gso; [|auto].
          erewrite <- set_lists_not_In; [|symmetry; eassumption|assumption].
          rewrite def_funs_get_neq; auto.
          simpl; rewrite M.gso; auto.
          now rewrite M.gss. }
        { apply get_list_app.
          eapply get_list_set_lists; [now inv Hgv1_fresh|symmetry; eassumption].
          erewrite get_list_set_lists_Disjoint;
            [|inv Hfv1_fresh; apply Disjoint_Union_r in H; apply H|symmetry; eassumption].
          rewrite get_list_set_neq; [|assumption].
          rename rho1' into rho1'k0, Hrho1' into Hrho1'k0.
          eapply get_list_set_lists; [now inv Hfv1_fresh|symmetry; eassumption]. }
        { rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
          rewrite find_def_fundefs_append_neq; auto.
          simpl; destruct (M.elt_eq f1 f) as [|Heq]; [now subst|clear Heq].
          destruct (M.elt_eq f1 f1) as [Heq|]; [clear Heq|contradiction].
          reflexivity. }
      + (* h \in pre_fds ++ fds *)
        assert (Hf' : h <> f). {
          intros contra; subst; inv Hcurried_unique_fundefs.
          now apply name_in_fundefs_bound_var_fundefs in Hfds.
          contradiction. }
        assert (Hf1: h <> f1). {
          (* f1 is not in curried (freshly generated by uncurrier) *)
          intros contra; subst; contradiction. }
        destruct (M.elt_eq h f) as [|Heq]; [contradiction|clear Heq].
        destruct (M.elt_eq h f1) as [|Heq]; [contradiction|clear Heq].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hfind_def Hrho'.
        assert (Hrho1' : length xs1 = length vs2). {
          apply set_lists_length in Hrho'.
          now rewrite <- Hlen_vs1_vs2. }
        eapply length_exists_set_lists in Hrho1'; destruct Hrho1' as [rho1' Hrho1'].
        exists xs1, e1; eexists; split; [|split]; [|eassumption|intros Hk1 Hvs1_vs2].
        (* only f is uncurried, so h in uncurried = h in curried (Hfind_def) *)
        assert (HLR : In _ (name_in_fundefs curried) h) by auto.
        rewrite fundefs_append_name_in_fundefs in HLR; [|reflexivity].
        split_var_in_fundefs h pre_fds Hh_pre_fds.
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_eq; auto.
        rewrite find_def_fundefs_append_eq in Hfind_def; auto.
        inv HLR; [contradiction|]; inv H; [inv H0; contradiction|].
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_neq; auto.
        rewrite find_def_fundefs_append_neq in Hfind_def; auto.
        simpl; simpl in Hfind_def.
        destruct (M.elt_eq h f); try contradiction.
        destruct (M.elt_eq h f1); try contradiction; auto.
        apply preord_exp_refl. eassumption.

        (* wrt free variables of e1, the environments
             rho' = [xs1 -> vs1] + f + fds + rho
             rho1' = [xs1 -> vs2] + f + f1 + fds + rho1
           agree. 
         *)

        (* [[xs1]](rho') ==_k1 [[xs1]](rho1') *)
        eapply preord_env_P_set_lists_extend; eauto.

        (* remove pre_fds *)
        intros a Ha.
        split_var_in_fundefs a pre_fds Hpre_fds. {
          unfold preord_var_env.
          rewrite def_funs_eq; [|now apply Hpre_fds_curried].
          rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
          intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
          eapply preord_val_monotonic;
          [apply IHk with (m := k - 1) (e := Ehalt a)|]; [omega| | | |constructor| |omega].
          * rewrite Union_Same_set; [assumption|].
            unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a' Ha'; inv Ha'.
            inv H3; contradiction H1.
            apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            now apply Free_Efun2.
          * apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
        }
        rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
        apply preord_var_env_def_funs_neq; auto.

        (* remove f and f1 *)
        simpl; apply preord_var_env_extend'. intros Ha_f.
        apply preord_var_env_extend_neq_r.

        (* remove fds *) {
          split_var_in_fundefs a fds Hfds'; unfold preord_var_env; simpl.
          - do 2 (rewrite def_funs_eq; [|assumption]).
            intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
            (* todo: basically a duplicate with the previous application of IH *)
            eapply preord_val_monotonic;
            [apply IHk with (m := k - 1) (e := Ehalt a)|]; [omega| | | |constructor| |omega].
            + rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            + apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free e1
                                 \\ FromList xs1
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n1; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            subst curried.
            split_var_in_fundefs h pre_fds Hh_pre_fds.
            + apply occurs_free_fundefs_append_l.
              intros contra; inv contra; auto.
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq_l
                with (B1 := Fcons f ft fv
                                 (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) fds); auto.
              apply Hfind_def.
              intros contra; inv contra.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              now inv H.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              right; now right.
            + apply occurs_free_fundefs_append; auto.
              apply Free_Fcons2; [|intros contra; subst; now contradiction H3].
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq
                with (B := Fcons f ft fv
                                 (Efun (Fcons g gt gv ge Fnil) (Ehalt g)) Fnil); auto.
              rewrite <- find_def_fundefs_append_neq with (B := pre_fds); auto.
              apply Hfind_def.
              auto.
              intros contra; inv contra; now inv H.
        }

        (* f1 never occurs in the definition of h *)
        {
          intros contra; subst.
          rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
          rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
          contradiction Hf1_fresh1.
          apply Hcurried_used_fundefs.
          right.
          eapply find_def_is_Some_occurs_free_fundefs; eauto; now inv Ha.
        }

        (* [[curried f]](rho') ==_k1 [[uncurried f]](rho1') *)
        eapply preord_val_monotonic;
        [apply IHk with (m := k - 1) (e := Ehalt f)|omega]; [omega| | | |constructor|assumption].
        (* todo: basically a duplicate with the previous application of IH,
           but with left instaed of right soemtimes *)
        * rewrite Union_Same_set; [assumption|].
          unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
          rewrite occurs_free_Ehalt.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [|eassumption]; omega.
          repeat normalize_occurs_free.
          intros b Hb; inv Hb.
          now left.
          inv H.
          contradiction H1.
          now inv H0.
    - (* h\not\in pre_fds ++ f |: fundefs(fds) *)
      assert (h <> f). {
        intros contra; subst.
        contradiction Hfds.
      }
      assert (h <> f1). {
        intros contra; subst.
        rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
        rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
        contradiction Hf1_fresh1.
        apply Hcurried_used.
        now left; right.
      }
      simpl.
      rename curried into curried'; pose (curried := curried'); subst curried'.
      rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
      assert (~ name_in_fundefs fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        right; now right.
      }
      assert (~ name_in_fundefs pre_fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        now left.
      }
      do 2 (rewrite def_funs_get_neq; auto).
      simpl; do 3 (rewrite M.gso; auto).
      do 2 (rewrite def_funs_neq; [|assumption]).
      unfold preord_env_P, preord_var_env in Henv.
      intros v1 Hv1.
      edestruct Henv as [v2 [Hv2 Hv12]]; try eassumption.
      + constructor; [simpl|assumption]; auto.
      + eexists; split; eapply preord_val_monotonic in Hv12; eauto; omega.
  Qed.

  Lemma preord_exp_eq_compat :
    forall (cenv : ctor_env) (P1 : PostT) (PG : PostGT)
           (Hprop1 : Post_properties cenv P1 P1 PG)
           (Hprop1 : Post_properties cenv PG PG PG)

           (k : nat) (rho1 rho2 : env) (c : exp_ctx) (e1 e2 e1' e2' : exp),
      (forall (m : nat) (rho3 rho4 : env),
          m <= k ->
          preord_env_P cenv PG (occurs_free e1) m rho3 rho4 ->
          preord_exp' cenv (preord_val cenv) P1 PG m (e1, rho3) (e2, rho4)) ->
      c |[ e1 ]| = e1' -> c |[ e2 ]| = e2' ->
      preord_env_P cenv PG (occurs_free e1') k rho1 rho2 ->
      preord_exp' cenv (preord_val cenv) P1 PG k (e1', rho1) (e2', rho2).
  Proof.
    intros.
    rewrite <- H0, <- H1; apply preord_exp_compat; auto.
    now rewrite H0.
  Qed.

  Definition ctx_preord_exp (k : nat) (e e1 : exp) := forall rho rho1,
    preord_env_P cenv PostG (occurs_free e) k rho rho1 ->
    preord_exp cenv Post PostG k (e, rho) (e1, rho1).

  Lemma uncurry_step_correct' :
    let P := (fun e s _ e1 s1 _ => forall k,
                  unique_bindings e ->
                  unique_bindings e1 -> (* TODO: remove this assumption *)
                  used_vars e \subset s ->
                  used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k e e1) in
    let Q := (fun f s (m : localMap) f1 s1 (m1 : localMap) => forall f' k e,
                  unique_bindings (Efun (fundefs_append f' f) e) ->
                  unique_bindings (Efun (fundefs_append f' f1) e) -> (* TODO: remove this assumption *)
                  used_vars (Efun (fundefs_append f' f) e) \subset s ->
                  used_vars (Efun (fundefs_append f' f1) e) \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k (Efun (fundefs_append f' f) e) (Efun (fundefs_append f' f1) e)) in
    forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1.
  Proof with eauto 10 with Ensembles_DB.
    intros P Q.
    uncurry_step_induction P Q IHuncurry IH;
      subst P; subst Q; simpl in *;
      [ intros k .. | intros f' k' e' | intros f' k' e' | intros f' k' e' | intros f' k' e' ];
      intros Hunique Hunique1 Hused Hused1 rho rho1 Henv.
    - (* uncurry_letapp *)
      eapply preord_exp_letapp_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + unfold preord_env_P in Henv.
        intros a Hin.
        apply Henv; [|easy].
        constructor; now left.
      + unfold preord_env_P in Henv.
        apply Forall2_same.
        intros a Hin.
        apply Henv.
        apply Free_Eletapp1; now right.
      + intros k' args1 args2 Hargs Hk'.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Eletapp in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eletapp in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_extend.
        * intros x1 Hx1.
          apply preord_var_env_monotonic with (k := k); [|omega].
          apply Henv.
          inversion Hx1. apply Free_Eletapp2; [|assumption].
          intros contra. subst. intuition.
        * assumption.
    - (* uncurry_constr *)      
      eapply preord_exp_constr_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + unfold preord_env_P in Henv.
        apply Forall2_same.
        intros a Hin.
        apply Henv.
        now apply Free_Econstr1.
      + intros k' args1 args2 Hargs Hk'.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Econstr in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Econstr in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_extend.
        * intros x1 Hx1.
          apply preord_var_env_monotonic with (k := k); [|omega].
          apply Henv.
          inversion Hx1. apply Free_Econstr2; [|assumption].
          intros contra. subst. intuition.
        * rewrite preord_val_eq. split; [trivial|]. eassumption.
    - (* uncurry_case_expr *)
      eapply preord_exp_case_cons_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + now apply List_util.Forall2_refl.
      + now apply Henv.
      + intros k' Hk'; apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_monotonic with (k := k); [omega|].
        eapply preord_env_P_antimon; [eassumption|].
        eapply occurs_free_Ecase_Included; simpl; eauto.
      + apply preord_exp_refl. eassumption.
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_case_arms *)
      destruct arm.
      eapply preord_exp_case_cons_compat; try eassumption; try easy_post.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply Hpost_prop.
      + eapply uncurry_step_preserves_ctag; eauto.
      + now apply Henv.
      + intros k' Hk'; apply preord_exp_refl. eassumption.
        apply preord_env_P_monotonic with (k := k); [omega|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
      + apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_monotonic with (k := k); [omega|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_proj *)
      eapply preord_exp_proj_compat; try eassumption; try easy_post.
      now eapply Hpost_prop.
      now eapply Hpost_prop. 
      now apply Henv.
      intros k' v1 v2 Hk' Hv1_v2.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Eproj in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Eproj in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_eq a x; subst; unfold preord_var_env.
      + do 2 rewrite M.gss.
        intros v0 Hv0; inv Hv0; eauto.
      + do 2 (rewrite M.gso; [|assumption]).
        apply preord_env_P_monotonic with (j := k') in Henv; [|omega].
        apply Henv; auto.
    - (* uncurry_prim *)
      apply preord_exp_prim_compat.
      now eapply Hpost_prop.
      + induction args; constructor.
        apply Henv; constructor; now left.
        inv Hunique; inv Hunique1.
        apply IHargs; try constructor; auto.
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        eapply preord_env_P_antimon; [eassumption|].
        intros a' Ha'; inv Ha'.
        constructor; now right.
        apply Free_Eprim2; assumption.
      (*
      + intros v1 v2 Hv1_v2.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Eprim in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eprim in Hused1.
        eapply Included_trans; [|eassumption]...
        intros a Ha; split_var_eq a x; subst; unfold preord_var_env.
        * do 2 rewrite M.gss.
          intros v0 Hv0; inv Hv0; eauto.
        * do 2 (rewrite M.gso; [|assumption]).
          apply Henv; auto.*)
    - (* uncurry_fun_expr *)
      eapply preord_exp_fun_compat; try eassumption.
      now eapply Hpost_prop. now eapply Hpost_prop.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Efun in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Efun in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_in_fundefs a fds Hfds; unfold preord_var_env.
      + do 2 (rewrite def_funs_eq; [|assumption]).
        intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
        apply preord_val_fundefs; try easy_post.
        apply preord_env_P_monotonic with (k := k); [omega|].
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Efun...
      + do 2 (rewrite def_funs_neq; [|assumption]).
        apply preord_env_P_monotonic with (j := k - 1) in Henv; [|omega].
        apply Henv; auto.
    - (* uncurry_fun_fds *)
      apply IH with (f' := Fnil); eauto.
    - (* uncurry_fundefs_fds *)
      replace (fundefs_append f' (Fcons f t args e fds))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds)
        by now rewrite <- fundefs_append_assoc.
      replace (fundefs_append f' (Fcons f t args e fds1))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds1)
        by now rewrite <- fundefs_append_assoc.
      apply IH with (f' := fundefs_append f' (Fcons f t args e Fnil));
        rewrite <- fundefs_append_assoc; auto.
    - (* uncurry_fundefs_e *)
      edestruct fundefs_append_ctx_exists
        with (f' := f') (c' := Fcons1_c f t args Hole_c fds) as [c Hc].
      eapply preord_exp_eq_compat with (c := Efun2_c c e') (e1 := e) (e2 := e1); eauto.
      unfold ctx_preord_exp in IH.
      inv Hunique; inv Hunique1.
      apply fundefs_append_unique_and in H2; destruct H2.
      apply fundefs_append_unique_and in H5; destruct H5.
      inv H0; inv H5.
      intros k rho0 rho2 Hk; eapply IH; auto.
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      all: simpl; now rewrite Hc.
    - (* uncurry_fundefs_curried *)
      eapply uncurry_step_correct_fundefs_curried; eauto...
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      rewrite H7 in Hused1.
      eapply Included_trans; [|apply Hused1].
      rewrite used_vars_Efun...
      now inv Hunique.
      eapply Union_Included_l.
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      now inv Hunique1.
    - (* anf uncurrying *)
      eapply uncurry_step_correct_fundefs_curried_anf; eauto...
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      rewrite H6 in Hused1.
      eapply Included_trans; [|apply Hused1].
      rewrite used_vars_Efun...
      now inv Hunique.
      eapply Union_Included_l.
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      now inv Hunique1.
  Qed.

  Lemma uncurry_step_correct : forall k e s m e1 s1 m1,
    unique_bindings e ->
    unique_bindings e1 -> (* TODO: remove this assumption *)
    used_vars e \subset s ->
    used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
    uncurry_step e s m e1 s1 m1 -> ctx_preord_exp k e e1.
  Proof. intros. intros rho rho1 Henv. eapply uncurry_step_correct'; eauto. Qed.


  Lemma uncurry_rel_correct : forall n k e s m e1 s1 m1,
    unique_bindings e ->
    unique_bindings e1 -> (* TODO: remove this assumption *)
    used_vars e \subset s ->
    used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
    uncurry_rel n e s m e1 s1 m1 -> ctx_preord_exp k e e1.
  Proof.
    induction n; intros; intros rho rho1 Henv; inv H3; [now apply preord_exp_refl|].
    assert (unique_bindings e2) by (eapply uncurry_step_preserves_unique_bindings; eauto).
    assert (used_vars e2 \subset s2) by (eapply uncurry_step_preserves_used_vars; eauto).
    eapply preord_exp_post_monotonic; [apply Hpost_idemp|..].
    eapply preord_exp_trans. eassumption.
    - unfold inclusion; intros.
      destruct Hpost_prop. eapply HGPost. eapply Hpost_idemp. eassumption.
    - now eauto.
    - now eauto. 
    - eapply uncurry_step_correct; [| | | |apply H5|apply Henv]; auto.
    - intros; eapply IHn; [| | | |apply H6|apply preord_env_P_refl]; auto.
  Qed.

(* uncurry_proto corresp *)

Import L6.Prototype L6.cps_proto L6.proto_util L6.uncurry_proto.

Lemma uncurry_fundefs_step_app pre f1 s1 m1 f2 s2 m2 :
  uncurry_fundefs_step f1 s1 m1 f2 s2 m2 ->
  uncurry_fundefs_step (fundefs_append pre f1) s1 m1 (fundefs_append pre f2) s2 m2.
Proof. induction pre; auto; intros Hstep; simpl; now constructor. Qed.

Lemma uncurry_proto_corresp_step e1 s1 e2 :
  s1 <--> used_vars e1 ->
  uncurry_proto.uncurry_step e1 e2 -> exists m1 s2 m2,
  uncurry_rel.uncurry_step e1 s1 m1 e2 s2 m2.
Proof.
  intros Hused Hstep; destruct Hstep.
  - (* CPS uncurrying *)
    destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    unfold Rec; decompose [and] H; clear H; subst.
    exists (M.empty _); do 2 eexists. apply app_ctx_uncurry_step; [destruct Hused; auto|].
    simpl; constructor.
    unfold fresh_copies, proto_util.fresh_copies in *.
    rewrite <- !Hused in *.
    apply uncurry_fundefs_step_app, uncurry_fundefs_curried; auto.
    + now rewrite M.gempty.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + reflexivity.
  - (* ANF uncurrying *)
    destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    unfold Rec; decompose [and] H; clear H; subst.
    exists (M.empty _); do 2 eexists. apply app_ctx_uncurry_step; [destruct Hused; auto|].
    simpl; constructor.
    unfold fresh_copies, proto_util.fresh_copies in *.
    rewrite <- !Hused in *.
    apply uncurry_fundefs_step_app, uncurry_fundefs_curried_anf; auto.
    + now rewrite M.gempty.
    + now apply occurs_in_exp_correct, Disjoint_Singleton_r.
    + reflexivity.
Qed.

Lemma uncurry_step_proto_bvs e1 e2 :
  uncurry_proto.uncurry_step e1 e2 ->
  bound_var e2 \subset bound_var e1 :|: Complement _ (used_vars e1).
Proof.
  clear; inversion 1; subst.
  - clear H; destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    rewrite !bound_var_app_ctx in *.
    decompose [and] H0; subst; clear H0.
    match goal with |- context [used_vars ?e] => remember e as original end.
    rename H1 into Hg', H3 into Hk', H7 into Hgv1, H9 into Hfv1, H11 into Hf1.
    clear - Hg' Hk' Hgv1 Hfv1 Hf1.
    apply Union_Included; [eauto with Ensembles_DB|].
    simpl. normalize_bound_var.
    rewrite fundefs_append_bound_vars by reflexivity.
    normalize_bound_var.
    repeat match goal with
    | |- context [bound_var_fundefs (fundefs_append ?B1 ?B2)] =>
      rewrite (fundefs_append_bound_vars B1 B2 _ eq_refl)
    end.
    apply Union_Included; [|eauto with Ensembles_DB].
    apply Union_Included; [eauto with Ensembles_DB|].
    unfold Rec.
    do 10 normalize_bound_var. repeat normalize_sets.
    repeat match goal with
           | |- _ :|: _ \subset _ => apply Union_Included
           | |- bound_var_fundefs Fnil \subset _ => 
             eapply Included_trans; [apply bound_var_fundefs_Fnil|]; eauto with Ensembles_DB
           end; eauto 10 with Ensembles_DB.
    + intros x Hx; right; intros Hoops. destruct Hfv1 as [[HC] _]. specialize (HC x).
      apply HC; constructor; auto.
    + intros x Hx; right; intros Hoops. destruct Hgv1 as [[HC] _]. specialize (HC x).
      apply HC; constructor; auto.
    + intros x Hx; right; intros Hoops. inv Hx; now apply Hf1.
  - clear H; destruct (decompose_fd_c C) as [[[D pre] e] HC]; subst C.
    rewrite !frames_compose_law, !framesD_cons, !ctx_of_fds_app, !app_exp_c_eq in *.
    rewrite !bound_var_app_ctx in *.
    decompose [and] H0; subst; clear H0.
    match goal with |- context [used_vars ?e] => remember e as original end.
    rename H2 into Hg', H5 into Hgv1, H7 into Hfv1, H9 into Hf1.
    clear - Hg' Hgv1 Hfv1 Hf1.
    apply Union_Included; [eauto with Ensembles_DB|].
    simpl. normalize_bound_var.
    normalize_bound_var.
    repeat match goal with
    | |- context [bound_var_fundefs (fundefs_append ?B1 ?B2)] =>
      rewrite (fundefs_append_bound_vars B1 B2 _ eq_refl)
    end.
    apply Union_Included; [|eauto with Ensembles_DB].
    apply Union_Included; [eauto with Ensembles_DB|].
    unfold Rec.
    do 10 normalize_bound_var. repeat normalize_sets.
    repeat match goal with
           | |- _ :|: _ \subset _ => apply Union_Included
           | |- bound_var_fundefs Fnil \subset _ => 
             eapply Included_trans; [apply bound_var_fundefs_Fnil|]; eauto with Ensembles_DB
           end; eauto 10 with Ensembles_DB.
    + intros x Hx; right; intros Hoops. destruct Hfv1 as [[HC] _]. specialize (HC x).
      apply HC; constructor; auto.
    + intros x Hx; right; intros Hoops. destruct Hgv1 as [[HC] _]. specialize (HC x).
      apply HC; constructor; auto.
    + intros x Hx; right; intros Hoops. inv Hx; now apply Hf1.
Qed.

Lemma uncurry_step_proto_dis e1 e2 :
  unique_bindings e1 ->
  Disjoint _ (bound_var e1) (occurs_free e1) ->
  uncurry_proto.uncurry_step e1 e2 ->
  Disjoint _ (bound_var e2) (occurs_free e2).
Proof.
  intros Huniq Hdis Hstep.
  assert (Hfv : occurs_free e1 <--> occurs_free e2). {
    edestruct (uncurry_proto_corresp_step e1 (used_vars e1)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
    eapply uncurry_step_preserves_occurs_free; eauto; eauto with Ensembles_DB. }
  rewrite <- Hfv.
  eapply Disjoint_Included_l; [apply uncurry_step_proto_bvs; eauto|].
  apply Union_Disjoint_l; eauto.
  apply Complement_Disjoint; unfold used_vars; eauto with Ensembles_DB.
Qed.

Lemma uncurry_step_proto_correct e1 e2 k :
  unique_bindings e1 ->
  uncurry_step e1 e2 ->
  ctx_preord_exp k e1 e2.
Proof.
  intros Hbind Hstep.
  edestruct (uncurry_proto_corresp_step e1 (used_vars e1)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
  eapply uncurry_step_correct with (s := used_vars e1); eauto; eauto with Ensembles_DB.
  - eapply uncurry_step_preserves_unique_bindings; eauto with Ensembles_DB.
  - eapply uncurry_step_preserves_used_vars; eauto with Ensembles_DB.
Qed.

Lemma uncurry_step_star_proto_correct e1 e2 k :
  unique_bindings e1 ->
  clos_refl_trans _ uncurry_step e1 e2 ->
  ctx_preord_exp k e1 e2.
Proof.
  intros Huniq Hsteps; revert k.
  apply clos_rt_rt1n in Hsteps.
  induction Hsteps; intros k.
  - unfold ctx_preord_exp; intros; apply preord_exp_refl; auto.
  - unfold ctx_preord_exp.
    intros rho rho1 Hrho.
    edestruct (uncurry_proto_corresp_step x (used_vars x)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
    assert (unique_bindings y) by (eapply uncurry_step_preserves_unique_bindings; eauto; eauto with Ensembles_DB).
    assert (used_vars y \subset s2) by (eapply uncurry_step_preserves_used_vars; eauto; eauto with Ensembles_DB).
    eapply preord_exp_post_monotonic; [apply Hpost_idemp|..].
    eapply preord_exp_trans; auto.
    + intro; intros. destruct Hpost_prop. eapply HGPost.
      eapply Hpost_idemp. eassumption.
    + apply uncurry_step_proto_correct; eauto. 
    + intros m; apply IHHsteps; auto.
      apply preord_env_P_refl. eassumption.
Qed.

Lemma uncurry_proto_step_ub e e' :
  unique_bindings e ->
  uncurry_step e e' ->
  unique_bindings e'.
Proof.
  intros Huniq Hstep.
  edestruct (uncurry_proto_corresp_step e (used_vars e)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
  eapply uncurry_step_preserves_unique_bindings; eauto; eauto with Ensembles_DB.
Qed.

Lemma uncurry_proto_steps_ub e e' :
  unique_bindings e ->
  clos_refl_trans _ uncurry_step e e' ->
  unique_bindings e'.
Proof.
  intros Huniq Hsteps; apply clos_rt_rt1n in Hsteps; induction Hsteps; eauto with Ensembles_DB.
  edestruct (uncurry_proto_corresp_step x (used_vars x)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
  apply IHHsteps.
  eapply uncurry_step_preserves_unique_bindings; eauto; eauto with Ensembles_DB.
Qed.

Lemma uncurry_proto_step_fv e e' :
  unique_bindings e ->
  uncurry_step e e' ->
  occurs_free e <--> occurs_free e'.
Proof.
  intros Huniq Hstep.
  edestruct (uncurry_proto_corresp_step e (used_vars e)) as [m1 [s2 [m2 Hrel]]]; eauto with Ensembles_DB.
  eapply uncurry_step_preserves_occurs_free; eauto; eauto with Ensembles_DB.
Qed.

Lemma uncurry_proto_steps_fv e e' :
  unique_bindings e ->
  clos_refl_trans _ uncurry_step e e' ->
  occurs_free e <--> occurs_free e'.
Proof.
  intros Huniq Hsteps; apply clos_rt_rt1n in Hsteps; induction Hsteps; eauto with Ensembles_DB.
  rewrite <- IHHsteps by (eapply uncurry_proto_step_ub; eauto).
  apply uncurry_proto_step_fv; auto.
Qed.

Lemma uncurry_proto_steps_dis e1 e2 :
  unique_bindings e1 ->
  Disjoint _ (bound_var e1) (occurs_free e1) ->
  clos_refl_trans _ uncurry_proto.uncurry_step e1 e2 ->
  Disjoint _ (bound_var e2) (occurs_free e2).
Proof.
  intros Huniq Hdis Hsteps; apply clos_rt_rt1n in Hsteps; induction Hsteps; eauto with Ensembles_DB.
  apply IHHsteps.
  - eapply uncurry_proto_step_ub; eauto.
  - eapply uncurry_step_proto_dis; eauto.
Qed.

Lemma uncurry_correct_top cps c e :
  unique_bindings e ->
  Disjoint _ (bound_var e) (occurs_free e) ->
  (max_var e 1 < state.next_var c)%positive ->
  exists e' c', uncurry_top cps e c = (Ret e', c') /\
  (max_var e' 1 < state.next_var c')%positive /\
  unique_bindings e' /\
  occurs_free e' \subset occurs_free e /\
  Disjoint _ (bound_var e') (occurs_free e') /\
  (forall k rho1 rho2,
    preord_env_P cenv PostG (occurs_free e) k rho1 rho2 ->
    preord_exp cenv Post PostG k (e, rho1) (e', rho2)).
Proof.
  intros Huniq Hdis Hmax.
  unfold uncurry_top.
  destruct (Pos.ltb_spec0 (max_var e 1) (state.next_var c)) as [Hlt|Hge]; [|easy].
  match goal with
  | |- context [run_rewriter' rw_uncurry ?e ?r ?s] =>
    destruct (run_rewriter' rw_uncurry e r s) as [e' s' Hrel]
  end.
  destruct s' as [[[[misc s] c'] fresh] Hfresh].
  do 2 eexists; split; [reflexivity|]; split; [|split; [|split; [|split]]].
  - clear - Hfresh; simpl; unerase; destruct Hfresh as [[] Hfresh]; unfold I_S_fresh in Hfresh.
    unfold fresher_than in Hfresh.
    enough (fresh > max_var e' 1)%positive by lia.
    apply Hfresh, max_var_subset.
  - eapply uncurry_proto_steps_ub; eauto.
  - eapply uncurry_proto_steps_fv; eauto.
  - eapply uncurry_proto_steps_dis; eauto.
  - intros k. eapply uncurry_step_star_proto_correct; eauto.
Qed.

End uncurry_correct.
