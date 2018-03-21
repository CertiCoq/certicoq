(* Syntactic properties of closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From L6 Require Import cps cps_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions eval.
From L6.Heap Require Import closure_conversion compat heap.

Require Import compcert.lib.Coqlib.
Require Import Coq.ZArith.Znumtheory ArithRing Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


(** * Syntactic Properties of the closure conversion relation *)


Module CCUtil (H : Heap).

  Module C := Compat H.

  Import H C C.LR C.LR.Sem C.LR.Sem.Equiv C.LR.Sem.Equiv.Defs.

  Variable clo_tag : cTag.

  (** ** Proof that after closure conversion all functions are closed *)

  Lemma project_var_occurs_free_ctx_Included Scope c Γ FVs S x x' C S' F e:
    project_var Scope c Γ FVs S x x' C S' ->
    (occurs_free e) \subset (Union _ F (Singleton _ x')) ->
    (FV_cc Scope Γ) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption. 
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eassumption ].
      eauto with Ensembles_DB.
    - simpl. normalize_occurs_free.
      eapply Union_Included. 
      + eapply Included_trans; [| now apply Hinc2 ]...
      + eauto with Ensembles_DB.
  Qed.
  
  (* TODO : do this with autorewrites *)
  Ltac normalize_sets :=
    match goal with
      | [|- context[FromList []]] => rewrite FromList_nil
      | [|- context[FromList(_ :: _)]] => rewrite FromList_cons
      | [|- context[FromList(_ ++ _)]] => rewrite FromList_app
      | [|- context[FromList [_ ; _]]] => rewrite FromList_cons
      | [|- context[Union _ _ (Empty_set _)]] =>
        rewrite Union_Empty_set_neut_r
      | [|- context[Union _ (Empty_set _) _]] =>
        rewrite Union_Empty_set_neut_l
      | [|- context[Setminus _ (Empty_set _) _]] =>
        rewrite Setminus_Empty_set_abs_r
      | [|- context[Setminus _ _ (Empty_set _)]] =>
        rewrite Setminus_Empty_set_neut_r
      | [ H : context[FromList []] |- _] => rewrite FromList_nil in H
      | [ H : context[FromList(_ :: _)] |- _] => rewrite FromList_cons in H
      | [ H : context[FromList(_ ++ _)] |- _] => rewrite FromList_app in H
      | [ H : context[FromList [_ ; _]] |- _] => rewrite FromList_cons in H
      | [ H : context[Union _ _ (Empty_set _)] |- _ ] =>
        rewrite Union_Empty_set_neut_r in H
      | [ H : context[Union _ (Empty_set _) _] |- _] =>
        rewrite Union_Empty_set_neut_l in H
      | [ H : context[Setminus _ (Empty_set _) _] |- _] =>
        rewrite Setminus_Empty_set_abs_r in H
      | [ H : context[Setminus _ _ (Empty_set _)] |- _] =>
        rewrite Setminus_Empty_set_neut_r in H
    end.
  
  Lemma project_vars_occurs_free_ctx_Included Scope c Γ
    FVs S xs xs' C S' F e:
    project_vars Scope c Γ FVs S xs xs' C S' ->
    Included _ (occurs_free e)  (Union _ F (FromList xs')) ->
    Included _ (FV_cc Scope Γ) F ->
    Included _ (occurs_free (C |[ e ]|)) F. 
  Proof. 
    intros Hproj. revert F.
    induction Hproj; intros F Hinc1 Hinc2; repeat normalize_sets.
    - eassumption.
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_Included; [ eassumption | | eassumption ].
      eapply IHHproj. rewrite <- Union_assoc. eassumption.
      eapply Included_trans. eassumption. now apply Included_Union_l.
  Qed.
  
  Lemma make_closures_occurs_free_ctx_Included B Γ C F S e:
    unique_functions B ->
    make_closures clo_tag B S Γ C ->
    Included _ (occurs_free e) (Union _ F (name_in_fundefs B)) ->
    Included _ (Union _ (name_in_fundefs B) (Singleton _ Γ)) F ->
    Included _ (occurs_free (C |[ e ]|)) F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hun Hmc. revert F e.
    induction Hmc; intros F e' Hinc1 Hinc2;
    simpl in *; repeat normalize_sets; (repeat normalize_occurs_free).
    - eassumption.
    - repeat normalize_sets.
      rewrite <- app_ctx_f_fuse. simpl. eapply IHHmc.
      inv Hun; eassumption.
      simpl. normalize_occurs_free. repeat normalize_sets.
      apply Union_Included.
      eapply Included_Union_preserv_l. 
      eapply Included_trans; [| eassumption ]...
      eapply Setminus_Included_Included_Union.
      eapply Included_trans; [ eassumption |]...
      eapply Included_trans; [| eassumption ]...
    - inv Hun. eapply IHHmc.
      eassumption.
      eapply Included_trans; [ eassumption |].
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans; [| eapply Included_Union_compat; [| reflexivity ]; eassumption ]...
      eapply Included_trans; [| eassumption ]... 
  Qed.

  Lemma project_var_free_funs_in_exp Scope c Γ FVs S x x' C S' B e:
    project_var Scope c Γ FVs S x x' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; inv Hvar; [ split; now eauto | ].
    (split; intros Hf; [ now inv Hf | now constructor ]).
  Qed.

  Lemma project_vars_free_funs_in_exp Scope c Γ FVs S xs xs' C S' B e:
    project_vars Scope c Γ FVs S xs xs' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.

  Lemma make_closures_funs_in_exp B S Γ C B' e:
    make_closures clo_tag B S Γ C  ->
    (funs_in_exp B' (C |[ e ]|) <-> funs_in_exp B' e).
  Proof.
    intros Hmc; revert e; induction Hmc; intros e';
    [ split; now eauto | | ].
    rewrite <- app_ctx_f_fuse.
    rewrite IHHmc. split; eauto; intros Hf; [ now inv Hf | now constructor ].
    eapply IHHmc; eauto.
  Qed.

  Lemma closure_conversion_fundefs_Same_set c Funs FVs B1 B2  :
    Closure_conversion_fundefs clo_tag Funs c FVs B1 B2 ->
    Same_set _ (name_in_fundefs B1) (name_in_fundefs B2).
  Proof. 
    intros Hcc. induction Hcc.  
    - simpl. rewrite IHHcc. reflexivity.
    - simpl. reflexivity.
  Qed.
  
  Lemma Closure_conversion_occurs_free_Included_mut :
    (forall e Scope c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       occurs_free (C |[ e' ]|) \subset FV_cc Scope Γ) /\
    (forall B c Funs FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (Hun: fundefs_names_unique_fundefs B) (Hun': fundefs_names_unique_fundefs Funs),
       (occurs_free_fundefs B') \subset (name_in_fundefs Funs) \\ (name_in_fundefs B')).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Econstr.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor.
      unfold FV_cc. eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Included_trans. eapply Included_Intersection_l...
      now eauto 20 with Ensembles_DB. 
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      inv H9.
      rewrite occurs_free_Ecase_nil. now apply Included_Union_r.
    - inv H9. destruct y as [c' e'].
      inv H2. simpl in H; subst. destruct H0 as [C' [e'' [Heq Hcce]]]. simpl in Heq; subst. 
      eapply Included_trans. now eapply occurs_free_Ecase_ctx_app.
      apply Union_Included. 
      + eapply project_var_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
        eapply Included_trans. eapply IHe. eassumption.
        intros f Hunf. eapply Hun. econstructor. eassumption. now constructor.
        now apply Included_Union_l.
      + eapply IHl. econstructor; eauto.
        intros f Hunf. eapply Hun. inv Hunf. econstructor 2. eassumption.
        econstructor 2. eassumption. 
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Eproj.
      rewrite Union_commut.
      apply Included_Union_compat; [| now apply Included_refl ].
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor.      
      unfold FV_cc.
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Included_trans. eapply Included_Intersection_l...
      now eauto 20 with Ensembles_DB. 
    - rewrite <- app_ctx_f_fuse. simpl. 
      eapply project_vars_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
      normalize_occurs_free. eapply Union_Included.
      now eauto with Ensembles_DB. normalize_occurs_free.
      rewrite Setminus_Union_distr. eapply Union_Included.
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply IHB. eassumption.
      intros f Hunf. eapply Hun. now inv Hunf; eauto.
      intros f Hunf. eapply Hun. now inv Hunf; eauto.
      reflexivity. rewrite closure_conversion_fundefs_Same_set; [| eassumption ]. 
      now eauto with Ensembles_DB.
      do 2 eapply Setminus_Included_Included_Union.
      eapply make_closures_occurs_free_ctx_Included; [| eassumption | | ].
      eapply Hun. now constructor.
      rewrite <- closure_conversion_fundefs_Same_set; [| eassumption ]. 
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor. 
      unfold FV_cc.
      eapply Union_Included; [ | now eauto with Ensembles_DB ].
      eapply Union_Included ; [ | now eauto with Ensembles_DB ].
      eapply Included_trans. eapply Included_Intersection_l...
      now eauto with Ensembles_DB.
      eapply Union_Included ; [ | now eauto with Ensembles_DB ].
      rewrite closure_conversion_fundefs_Same_set; [| eassumption ]...
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      unfold AppClo. repeat normalize_occurs_free. repeat normalize_sets.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      apply Union_Included. eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eauto 7 with Ensembles_DB.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Eprim.
      apply Union_Included; [ now eauto with Ensembles_DB |]. 
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor.
      unfold FV_cc.
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included ; [ | now eauto with Ensembles_DB ].
      eapply Included_trans. eapply Included_Intersection_l...
      now eauto with Ensembles_DB.
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Ehalt...
    - eapply Included_Setminus.
      constructor. intros v' Hc. inv Hc.
      now eapply fun_names_not_free_in_fundefs; eauto.
      rewrite occurs_free_fundefs_Fcons.
      apply Union_Included.
      + apply Setminus_Included_Included_Union.
        eapply make_closures_occurs_free_ctx_Included;[| eassumption | | ].
        eapply Hun'. now eauto.
        eapply Included_trans. eapply IHe. eassumption.
        intros f Hunf. eapply Hun. left. now constructor. 
        unfold FV_cc. simpl.
        rewrite FromList_cons.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Included_trans. eapply Included_Intersection_l...
        now eauto with Ensembles_DB.
        normalize_sets...
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHB. eassumption.
        intros f Hunf. inv Hunf; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)).
        now inv Hun; eauto.
        eapply Hun'; eauto. simpl. eapply Setminus_Included_Included_Union...
    - rewrite occurs_free_fundefs_Fnil. now apply Included_Empty_set.
  Qed.
  
  Corollary Closure_conversion_occurs_free_Included :
    (forall e Scope c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       occurs_free (C |[ e' ]|) \subset (FV_cc Scope Γ)).
  Proof.
    now eapply Closure_conversion_occurs_free_Included_mut.
  Qed.
  
  Corollary Closure_conversion_occurs_free_fundefs_Included :
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (Hun: fundefs_names_unique_fundefs B) (Hun': fundefs_names_unique_fundefs Funs),
       Included _ (occurs_free_fundefs B') (Setminus _ (name_in_fundefs Funs) (name_in_fundefs B'))).
  Proof.
    intros. 
    eapply Closure_conversion_occurs_free_Included_mut; eauto.
  Qed.
  
  Lemma Closure_conversion_closed_fundefs_mut :
    (forall e Scope c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       closed_fundefs_in_exp (C |[ e' ]|)) /\
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
       closed_fundefs_in_fundefs B').
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; [ eassumption | | eassumption ]. 
      intros B' H. eapply Hun. now constructor. 
    - inv H9. 
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H4.
    - inv H9. destruct H2 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
      simpl in *; subst.
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H5.
      + inv H. eapply IHe; [ eassumption | | eassumption ].
        intros B' H. eapply Hun. econstructor. eassumption. now constructor. 
      + eapply IHl. now econstructor; eauto.
        intros B' HB'. eapply Hun. inv HB'. econstructor. eassumption.
        constructor 2. eassumption. 
        rewrite project_var_free_funs_in_exp.
        econstructor; eassumption. eassumption.
    - intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; [ eassumption | | eassumption ]. 
      intros B' H. eapply Hun. now constructor. 
    - rewrite <- app_ctx_f_fuse. intros B HB.
      rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      simpl in HB. inv HB. inv H7.
      + split; [| now apply Included_Empty_set ].
        eapply Included_trans.
        eapply Closure_conversion_occurs_free_Included_mut. eassumption.
        intros B HB. eapply Hun. inv HB; eauto.
        intros B HB. eapply Hun. inv HB; eauto.
        rewrite closure_conversion_fundefs_Same_set; [| eassumption ].
        rewrite Setminus_Same_set_Empty_set. now apply Included_Empty_set.
      + rewrite make_closures_funs_in_exp in H8; [| eassumption ].
        eapply IHe; [ eassumption | | eassumption ].
        intros B1 HB1. eapply Hun. now constructor.
      + eapply IHB; [ eassumption | | eassumption ].
        intros B1 HB1. now inv HB1; eauto.
    - intros B HB.  rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H1. inv H4.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; [ eassumption | | eassumption ]. 
      intros B' H. eapply Hun. now constructor.
    - intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB.
    - intros B HB. inv HB.
      + rewrite make_closures_funs_in_exp in H1; [| eassumption ].
        eapply IHe; [ eassumption | | eassumption ].  
        intros B' H. eapply Hun. left. now constructor. 
      + eapply IHB; [ eassumption | | eassumption ].
        intros B' H. inv H; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)). now inv Hun; eauto.
    - intros B HB. inv HB.
  Qed.

  (** * Lemmas about [project_var] and [project_vars] *)

  Lemma project_var_free_set_Included Scope c Γ FVs x x' C S S' :
    project_var Scope c Γ FVs S x x' C S' ->
    Included _ S' S.
  Proof with now eauto with Ensembles_DB.
    intros Hproj. inv Hproj...
  Qed.

  Lemma project_vars_free_set_Included Scope c Γ FVs xs xs' C S S' :
    project_vars Scope c Γ FVs S xs xs' C S' ->
    Included _ S' S.
  Proof.
    intros Hproj. induction Hproj.
    - now apply Included_refl.
    - eapply Included_trans. eassumption.
      eapply project_var_free_set_Included. eassumption. 
  Qed.

  Lemma project_var_not_In_free_set Scope c Γ FVs x x' C S S'  :
    project_var Scope c Γ FVs S x x' C S' ->
    Disjoint _ S Scope ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. constructor; eauto.
    - inv Hc. exfalso. eauto.    
  Qed.
  
  Lemma project_vars_not_In_free_set Scope c Γ FVs xs xs' C S S'  :
    project_vars Scope c Γ FVs S xs xs' C S' ->
    Disjoint _ S Scope  ->
    Disjoint _ S' (FromList xs').
  Proof.
    intros Hproj Hd. induction Hproj.
    - constructor. intros x Hc. inv Hc. rewrite FromList_nil in H0.
      eapply not_In_Empty_set. eassumption. 
    - rewrite FromList_cons. eapply Disjoint_sym.
      eapply Union_Disjoint_l.
      + eapply Disjoint_Included_r_sym.
        eapply project_vars_free_set_Included; eassumption.
        eapply Disjoint_Singleton_r.
        eapply project_var_not_In_free_set; eassumption. 
      + eapply Disjoint_sym. eapply IHHproj.
        eapply Disjoint_Included_l.
        eapply project_var_free_set_Included. eassumption.
        eassumption.
  Qed.

  Lemma project_var_In_Union Scope c Γ FVs S x x' C S' :
    project_var Scope c Γ FVs S x x' C S' ->
    x \in (FV Scope FVs).
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    right. constructor; eauto. eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_In_Union Scope c Γ FVs S xs xs' C S' :
    project_vars Scope c Γ FVs S xs xs' C S' ->
    (FromList xs) \subset (FV Scope FVs).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - rewrite FromList_nil. now apply Included_Empty_set.
    - rewrite FromList_cons.
      eapply Union_Included; [| eassumption ].
      eapply Singleton_Included. eapply project_var_In_Union.
      eassumption.
  Qed.
  
  Lemma project_var_not_In Scope c Γ FVs S x x' C S' :
    Disjoint _ S (FV Scope FVs) ->    
    project_var Scope c Γ FVs S x x' C S' ->
    ~ In _ S x.
  Proof.
    intros Hd Hproj Hin. inv Hproj.
    - eapply Hd. constructor; eauto. left; eauto.
    - eapply Hd; eauto. constructor. now apply Hin.
      right. constructor; eauto.
      eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_Disjoint Scope c Γ FVs S xs xs' C S' :
    Disjoint _ S (FV Scope FVs) ->      
    project_vars Scope c Γ FVs S xs xs' C S' ->
    Disjoint _ S (FromList xs).
  Proof.
    revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
    - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
    - inv Hproj. rewrite FromList_cons.
      eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. eapply project_var_not_In; eauto.
      inv H6.
      + eapply IHxs; [| eassumption ]. eauto.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H10.
        eapply Disjoint_Included_r. eassumption.
        eauto with Ensembles_DB.
  Qed.
  
  Lemma Closure_conversion_pre_occurs_free_Included_mut :
    (forall e Scope c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope c Γ FVs e e' C),
       occurs_free e \subset FV Scope FVs) /\
    (forall B c Funs FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (HD : FromList FVs <--> occurs_free_fundefs B),
       occurs_free_fundefs B \subset FromList FVs).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        unfold FV.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Included_trans. eapply Included_Intersection_l.
        now eauto with Ensembles_DB.
    - normalize_occurs_free. eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + inv H9. simpl in H2. destruct H2 as (Heq & C' & e' & Heq' & Hcc).
        destruct y; simpl in *; subst.
        eapply Union_Included.
        now eapply IHe; eauto.
        eapply IHl; eauto. econstructor; try eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + eapply Included_trans.
        eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        unfold FV.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Included_trans. eapply Included_Intersection_l.
        now eauto with Ensembles_DB.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Included_trans. eapply IHB; eauto.
        rewrite <- H1. reflexivity.
        eapply project_vars_In_Union; eauto.
      + eapply Included_trans. eapply Included_Setminus_compat.
        now eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union. unfold FV.
        eapply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Included_trans. eapply Included_Intersection_l...
        now eauto with Ensembles_DB. 
    - normalize_occurs_free. inv H3. eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        unfold FV.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        eapply Included_trans. eapply Included_Intersection_l.
        now eauto with Ensembles_DB.
    - rewrite occurs_free_Ehalt.
      eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - rewrite HD; eauto. reflexivity.
    - normalize_occurs_free...
  Qed.
  
  Corollary Closure_conversion_pre_occurs_free_Included :
    (forall e Scope c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope c Γ FVs e e' C),
       occurs_free e \subset FV Scope FVs).
  Proof.
    now apply Closure_conversion_pre_occurs_free_Included_mut.
  Qed.


  Corollary Closure_conversion_pre_occurs_free_fundefs_Included :
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (HD : FromList FVs <--> occurs_free_fundefs B),
       occurs_free_fundefs B \subset FromList FVs).
  Proof.
    intros. 
    eapply Closure_conversion_pre_occurs_free_Included_mut; eauto.
  Qed.
  
 
  Lemma Closure_conversion_fundefs_numOf_fundefs Funs (c : cTag) 
        (FVs : list var) (B1 B2 : fundefs) :
    Closure_conversion_fundefs clo_tag Funs c FVs B1 B2 ->
    numOf_fundefs B1 = numOf_fundefs B2.
  Proof.
    intros Hcc; induction Hcc; eauto; simpl. congruence.
  Qed.

  Lemma project_var_get Scope c Γ FVs S1 x x' C1 S2 rho1 H1 rho2 H2 m y:
    project_var Scope c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx. inv H18.
      destruct (var_dec y x'); subst.
      contradiction.
      now rewrite M.gso.
  Qed.    
  
  Lemma project_vars_get Scope c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m y:
    project_vars Scope c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    revert Scope Γ FVs S1 xs' C1 S2 rho1 H1 rho2 H2 m y.
    induction xs; intros Scope Γ FVs S1 xs' C1 S2 rho1 H1 rho2 H2 m y Hproj Hctx Hnin.
    - inv Hproj. inv Hctx. reflexivity.
    - inv Hproj.  
      edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho'' [H'' [m1 [m2  [Hctx1 [Hctx2 Hadd]]]]]]; eauto.
      subst. eapply project_var_get in Hctx1; eauto.
      eapply IHxs in Hctx2; eauto.
      rewrite Hctx1, <- Hctx2. reflexivity.
      intros Hc. eapply Hnin.
      eapply project_var_free_set_Included; eassumption.
  Qed.
  
  Lemma project_var_getlist Scope c Γ FVs S1 x x' C1 S2 rho1 H1 rho2 H2 m ys :
    project_var Scope c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 H1 rho2 H2 m; induction ys; intros rho1 H1 rho2 H2 m Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin.
      erewrite project_var_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        


  Lemma project_vars_getlist Scope c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m ys :
    project_vars Scope c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 H1 rho2 H2 m; induction ys; intros rho1 H1 rho2 H2 m  Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin. 
      erewrite project_vars_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        

  (** [project_var] preserves env_locs in dom *)
  Lemma project_var_env_locs Scope c Γ FVs x x' C S S' e k rho H rho' H':
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    env_locs rho (occurs_free (C |[ e ]|)) \subset dom H ->
    env_locs rho' (occurs_free e) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl in *; eauto.
    - inv H17.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        simpl. normalize_occurs_free.
        rewrite (reach_unfold H' (env_locs rho (Γ |: (occurs_free e \\ [set x'])))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ]. rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ]. simpl. normalize_occurs_free...
  Qed.
  
  Lemma project_var_env_locs' Scope c Γ FVs x x' C S S' k rho H rho' H':
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (FV_cc Scope Γ))) H ->
    env_locs rho (FV_cc Scope Γ) \subset dom H ->
    env_locs rho' (x' |: (FV_cc Scope Γ)) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    unfold FV_cc. rewrite !Union_assoc.
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - repeat rewrite (Union_Same_set [set x']) at 1. eassumption.
      eapply Singleton_Included; eauto.
    - inv H17.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H' (env_locs rho ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ].
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ]. simpl.
        eapply env_locs_monotonic. now eauto 20 with Ensembles_DB.
  Qed.

  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed Scope c Γ FVs x x' C S S' e k rho H rho' H':
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    well_formed (reach' H' (env_locs rho' (occurs_free e))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H17.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        simpl. normalize_occurs_free.
        rewrite <- Union_assoc.
        eapply Included_Union_preserv_r. eapply Included_Union_Setminus.
        now eauto with typeclass_instances.
      + simpl. eapply well_formed_antimon; try eassumption.
        simpl. normalize_occurs_free. rewrite (reach_unfold H' (env_locs rho (Γ |: (occurs_free e \\ [set x'])))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic. rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.
  
  Lemma project_var_reachable Scope c Γ FVs x x' C S S' e k rho H rho' H':
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    reach' H' (env_locs rho' (occurs_free e)) \subset
    reach' H (env_locs rho (occurs_free (C |[ e ]|))).
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx. inv Hvar; inv Hctx; try reflexivity.
    - simpl. normalize_occurs_free. inv H17.
      eapply Included_trans.
      eapply reach'_set_monotonic. eapply env_locs_set_Inlcuded'. 
      rewrite !env_locs_Union, !reach'_Union, env_locs_Singleton; eauto.
      eapply Included_Union_compat; try reflexivity.
      rewrite (reach_unfold H' (val_loc (Loc l))).
      eapply Included_Union_preserv_r. 
      eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; eauto.
      simpl. eapply In_Union_list. eapply in_map.
      eapply nthN_In. eassumption.
  Qed.
  
  Lemma project_vars_reachable Scope c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    reach' H' (env_locs rho' (occurs_free e)) \subset
    reach' H (env_locs rho (occurs_free (C |[ e ]|))).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply Included_trans. eapply IHHvar; eauto.
      eapply Included_trans. eapply project_var_reachable; eauto.
      rewrite app_ctx_f_fuse. reflexivity. 
  Qed.

  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed' Scope c Γ FVs x x' C S S' k rho H rho' H':
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    (env_locs rho (FV_cc Scope Γ)) \subset dom H ->
    well_formed (reach' H (env_locs rho (FV_cc Scope Γ))) H ->
    well_formed (reach' H' (env_locs rho' (x' |: (FV_cc Scope Γ)))) H'.
  Proof with (now eauto with Ensembles_DB). 
    unfold FV_cc. rewrite !Union_assoc.
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto. rewrite (Union_Same_set [set x']).
      eassumption.
      eapply Singleton_Included...
    - inv H17.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        now eauto 20 with Ensembles_DB.
      + simpl. eapply well_formed_antimon; try eassumption.
        rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H' (env_locs rho ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic.
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.
  
  Lemma project_var_env_locs_subset Scope c Γ FVs xs xs' C S S' S1 k rho H rho' H':
    project_var Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    Disjoint _ S1 S ->
    env_locs rho' S1 <--> env_locs rho S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx HD. destruct Hvar; inv Hctx; try reflexivity.
    - inv H17. rewrite env_locs_set_not_In. reflexivity. 
      intros Hc; eapply HD; eauto.
  Qed.
  
   Lemma project_vars_env_locs_subset Scope c Γ FVs xs xs' C S S' S1 k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    Disjoint _ S1 S ->
    env_locs rho' S1 <--> env_locs rho S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hd.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst. rewrite IHHvar; eauto.
      rewrite project_var_env_locs_subset; eauto.
      reflexivity. eapply Disjoint_Included_r; try eassumption.
      eapply project_var_free_set_Included; eauto.
  Qed.

  Lemma project_var_heap Scope c Γ FVs x x' S S' C H rho H' rho' k :
    project_var Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    H = H'. 
  Proof.
    intros Hvar Hctx; inv Hvar; inv Hctx; eauto.
    inv H17; eauto.
  Qed.

  Lemma project_vars_heap Scope c Γ FVs x x' S S' C H rho H' rho' k :
    project_vars Scope c Γ FVs S x x' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    H = H'. 
  Proof.
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx.
    - inv Hctx; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply project_var_heap in Hctx2; eauto.
      subst. eapply IHHvar; eauto.
  Qed.

  Lemma project_vars_env_locs Scope c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    (env_locs rho' (occurs_free e)) \subset dom H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_env_locs; try eassumption.
      eapply project_var_well_formed; try eassumption. 
  Qed.
    
  Lemma project_vars_env_locs' Scope c Γ FVs xs xs' C S S' k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    Disjoint _ S Scope  ->
    well_formed (reach' H (env_locs rho (FV_cc Scope Γ))) H ->
    env_locs rho (FV_cc Scope Γ) \subset dom H ->
    env_locs rho' (FromList xs' :|: (FV_cc Scope Γ)) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hd Hlocs Hwf.
    - inv Hctx. rewrite FromList_nil, Union_Empty_set_neut_l. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite FromList_cons.
      rewrite <- !Union_assoc. rewrite env_locs_Union.
      eapply Union_Included.
      erewrite <- project_vars_heap with (H := H3) (H' := H2); eauto .
      eapply project_vars_env_locs_subset in Hvar; eauto.
      rewrite Hvar. eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
      eapply Disjoint_Singleton_l. eapply project_var_not_In_free_set. eassumption.
      eapply Disjoint_Included_r; [| eassumption ]...
      eapply IHHvar; eauto.
      eapply Disjoint_Included_l. eapply project_var_free_set_Included. eassumption.
      eassumption.
      eapply well_formed_antimon; [| eapply project_var_well_formed'; eauto ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
      eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
  Qed.
  
  Lemma project_vars_well_formed Scope c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    well_formed (reach' H' (env_locs rho' (occurs_free e))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_env_locs; try eassumption.
      eapply project_var_well_formed; try eassumption. 
  Qed.
  
  Lemma project_vars_well_formed' Scope c Γ FVs xs xs' C S S' k rho H rho' H':
    project_vars Scope c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    Disjoint _ S Scope ->
    (env_locs rho (FV_cc Scope Γ)) \subset dom H ->
    well_formed (reach' H (env_locs rho (FV_cc Scope Γ))) H ->
    well_formed (reach' H' (env_locs rho' (FromList xs' :|: (FV_cc Scope Γ)))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx HD Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
      rewrite FromList_nil, Union_Empty_set_neut_l. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite FromList_cons.
      rewrite <- !Union_assoc. rewrite env_locs_Union, reach'_Union.
      eapply well_formed_Union.
      erewrite <- project_vars_heap with (H := H3) (H' := H2); eauto .
      eapply project_vars_env_locs_subset in Hvar; eauto.
      rewrite Hvar.
      eapply well_formed_antimon; [| eapply project_var_well_formed' ]; eauto.
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
      eapply Disjoint_Singleton_l. eapply project_var_not_In_free_set.
      eassumption.
      eapply Disjoint_Included_r; [| eassumption ]...
      eapply IHHvar; eauto.
      eapply Disjoint_Included_l. eapply project_var_free_set_Included. eassumption.
      eassumption.
      eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
      eapply well_formed_antimon; [| eapply project_var_well_formed'; eauto ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
  Qed.

End CCUtil. 