(* Syntactic properties of closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From L6 Require Import cps size_cps cps_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions eval.
From L6.Heap Require Import closure_conversion.

Require Import compcert.lib.Coqlib.
Require Import Coq.ZArith.Znumtheory ArithRing Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


(** * Syntactic Properties of the closure conversion relation *)

Section Closure_conversion_util.

  Variable clo_tag : cTag.

  (** ** Proof that after closure conversion all functions are closed *)

  Lemma project_var_occurs_free_ctx_Included Scope Funs c Γ FVs S x x' C S' F e:
    project_var Scope Funs c Γ FVs S x x' C S' ->
    Included _ (occurs_free e) (Union _ F (Singleton _ x')) ->
    Included _ (FV_cc Scope Funs Γ) F ->
    Included _ (occurs_free (C |[ e ]|)) F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption. 
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eassumption ].
      eauto with Ensembles_DB.
    - simpl. eapply Included_trans. eassumption. 
      apply Union_Included. reflexivity.
      eapply Included_trans; [| eassumption ].
      eapply Singleton_Included. left. right.
      constructor; eauto.
    - simpl. rewrite occurs_free_Eproj.
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
  
  Lemma project_vars_occurs_free_ctx_Included Scope Funs c Γ
    FVs S xs xs' C S' F e:
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Included _ (occurs_free e)  (Union _ F (FromList xs')) ->
    Included _ (FV_cc Scope Funs Γ) F ->
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
    intros Hun Hmc. revert F.
    induction Hmc; intros F Hinc1 Hinc2;
    simpl in *; repeat normalize_sets; (repeat normalize_occurs_free).
    - eassumption.
    - repeat normalize_sets.
      apply Union_Included. apply Union_Included.
      eapply Included_trans; [| eassumption ]...
      eapply Included_trans; [| eassumption ]...
      eapply Setminus_Included_Included_Union.
      inv Hun. eapply IHHmc.
      eassumption.
      eapply Included_trans; [ eassumption |]...
      eapply Included_Union_preserv_l.
      eapply Included_trans; [| eassumption ].
      apply Included_Union_compat; [| now apply Included_refl ]...
    - inv Hun. eapply IHHmc.
      eassumption.
      eapply Included_trans; [ eassumption |].
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans; [| eapply Included_Union_compat; [| reflexivity ]; eassumption ]...
      eapply Included_trans; [| eassumption ]... 
  Qed.

  Lemma project_var_free_funs_in_exp Scope Funs c Γ FVs S x x' C S' B e:
    project_var Scope Funs c Γ FVs S x x' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; inv Hvar; [ split; now eauto | split; now eauto |].
    (split; intros Hf; [ now inv Hf | now constructor ]).
  Qed.

  Lemma project_vars_free_funs_in_exp Scope Funs c Γ FVs S xs xs' C S' B e:
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.

  Lemma make_closures_funs_in_exp B S Γ C B' e:
    make_closures clo_tag B S Γ C  ->
    (funs_in_exp B' (C |[ e ]|) <-> funs_in_exp B' e).
  Proof.
    intros Hmc; induction Hmc;
    [ split; now eauto | | ].
    rewrite <- IHHmc. split; eauto; intros Hf; [ now inv Hf | now constructor ].
    eassumption.
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
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       occurs_free (C |[ e' ]|) \subset FV_cc Scope Funs Γ) /\
    (forall B Funs c FVs B'
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
      unfold FV_cc. now eauto 20 with Ensembles_DB. 
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ]. inv H10.
      rewrite occurs_free_Ecase_nil. now apply Included_Union_r.
    - inv H10. destruct y as [c' e'].
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
      unfold FV_cc. now eauto 20 with Ensembles_DB. 
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
      eapply Union_Included.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      repeat eapply Included_Union_preserv_l. reflexivity.
      do 5 eapply Included_Union_preserv_l. 
      eapply Included_Union_preserv_r...
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
      unfold FV_cc. eauto 30 with Ensembles_DB.      
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
        simpl.
        rewrite FromList_cons. now eauto 30 with Ensembles_DB.
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
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       occurs_free (C |[ e' ]|) \subset (FV_cc Scope Funs Γ)).
  Proof.
    now eapply Closure_conversion_occurs_free_Included_mut.
  Qed.
  
  Corollary Closure_conversion_occurs_free_fundefs_Included :
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (Hun: fundefs_names_unique_fundefs B) (Hun': fundefs_names_unique_fundefs Funs),
       Included _ (occurs_free_fundefs B') (Setminus _ (name_in_fundefs Funs) (name_in_fundefs B'))).
  Proof.
    now eapply Closure_conversion_occurs_free_Included_mut.
  Qed.
    
  Lemma Closure_conversion_closed_fundefs_mut :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C)
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
    - inv H10. 
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H4.
    - inv H10. destruct H2 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
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
      simpl in HB. inv HB. inv H8.
      + split; [| now apply Included_Empty_set ].
        eapply Included_trans.
        eapply Closure_conversion_occurs_free_Included_mut. eassumption.
        intros B HB. eapply Hun. inv HB; eauto.
        intros B HB. eapply Hun. inv HB; eauto.
        rewrite closure_conversion_fundefs_Same_set; [| eassumption ].
        rewrite Setminus_Same_set_Empty_set. now apply Included_Empty_set.
      + rewrite make_closures_funs_in_exp in H9; [| eassumption ].
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

  Lemma project_var_free_set_Included Scope Funs c Γ FVs x x' C S S' :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    Included _ S' S.
  Proof with now eauto with Ensembles_DB.
    intros Hproj. inv Hproj...
  Qed.

  Lemma project_vars_free_set_Included Scope Funs c Γ FVs xs xs' C S S' :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Included _ S' S.
  Proof.
    intros Hproj. induction Hproj.
    - now apply Included_refl.
    - eapply Included_trans. eassumption.
      eapply project_var_free_set_Included. eassumption. 
  Qed.

  Lemma project_var_not_In_free_set Scope Funs c Γ FVs x x' C S S'  :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    Disjoint _ S (Union var Scope
                        (Union var (Setminus _ Funs Scope)
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. eauto.
    - eapply Hd; eauto. constructor; eauto. right. left.
      eexists; eauto.
    - inv Hc. exfalso. eauto.    
  Qed.

  Lemma project_vars_not_In_free_set Scope Funs c Γ FVs xs xs' C S S'  :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Disjoint _ S (Union var Scope
                        (Union var (Setminus _ Funs Scope)
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
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

  Lemma project_var_In_Union Scope Funs c Γ FVs S x x' C S' :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    x \in (FV Scope Funs FVs).
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    left; right. constructor; eauto.
    right. constructor; eauto. eapply nthN_In. eassumption.
    intros Hc; inv Hc; eauto. 
  Qed.

  Lemma project_vars_In_Union Scope Funs c Γ FVs S xs xs' C S' :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    (FromList xs) \subset (FV Scope Funs FVs).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - rewrite FromList_nil. now apply Included_Empty_set.
    - rewrite FromList_cons.
      eapply Union_Included; [| eassumption ].
      eapply Singleton_Included. eapply project_var_In_Union.
      eassumption.
  Qed.
  
  Lemma project_var_not_In Scope Funs c Γ FVs S x x' C S' :
    Disjoint _ S (FV Scope Funs FVs) ->
    
    project_var Scope Funs c Γ FVs S x x' C S' ->
    ~ In _ S x.
  Proof.
    intros Hd Hproj Hin. inv Hproj.
    - eapply Hd. constructor; eauto. left; eauto.
    - eapply Hd. constructor; eauto. left; eauto.
      right. constructor; eauto.
    - eapply Hd; eauto. constructor. now apply Hin.
      right. constructor; eauto.
      eapply nthN_In in H1. eassumption.
      intros Hc; inv Hc; eauto.
  Qed.

  Lemma project_vars_Disjoint Scope Funs c Γ FVs S xs xs' C S' :
    Disjoint _ S (FV Scope Funs FVs) ->      
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Disjoint _ S (FromList xs).
  Proof.
    revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
    - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
    - inv Hproj. rewrite FromList_cons.
      eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. eapply project_var_not_In; eauto.
      inv H7.
      + eapply IHxs; [| eassumption ]. eauto.
      + eauto.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H11.
        eapply Disjoint_Included_r. eassumption.
        eauto with Ensembles_DB.
  Qed.

  Lemma Closure_conversion_pre_occurs_free_Included_mut :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       (* (Hun: fundefs_names_unique e), *)
       occurs_free e \subset FV Scope Funs FVs) /\
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (HD : FromList FVs <--> occurs_free_fundefs B),
       (* (Hun: fundefs_names_unique_fundefs B) (Hun': fundefs_names_unique_fundefs Funs), *)
       occurs_free_fundefs B \subset FromList FVs).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity. now eauto 20 with Ensembles_DB.
    - normalize_occurs_free. eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + inv H10. simpl in H2. destruct H2 as (Heq & C' & e' & Heq' & Hcc).
        destruct y; simpl in *; subst.
        eapply Union_Included.
        now eapply IHe; eauto.
        eapply IHl; eauto. econstructor; try eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity. now eauto 20 with Ensembles_DB.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Included_trans. eapply IHB; eauto.
        rewrite <- H1. reflexivity.
        eapply project_vars_In_Union; eauto.
      + eapply Included_trans. eapply Included_Setminus_compat.
        now eapply IHe; eauto. reflexivity.
        now eauto 20 with Ensembles_DB. 
    - normalize_occurs_free. inv H3. eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity. now eauto 20 with Ensembles_DB.
    - rewrite occurs_free_Ehalt.
      eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - rewrite HD; eauto. reflexivity.
    - normalize_occurs_free...
  Qed.
  
  Corollary Closure_conversion_pre_occurs_free_Included :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       occurs_free e \subset FV Scope Funs FVs).
  Proof.
    now apply Closure_conversion_pre_occurs_free_Included_mut.
  Qed.


  Corollary Closure_conversion_pre_occurs_free_fundefs_Included :
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B')
       (HD : FromList FVs <--> occurs_free_fundefs B),
       occurs_free_fundefs B \subset FromList FVs).
  Proof. 
     now apply Closure_conversion_pre_occurs_free_Included_mut.
  Qed.
  
  Lemma project_var_sizeOf_ctx_exp (Scope Funs : Ensemble var) (σ : var -> var) 
    (c : cTag) (Γ : var) (FVs : list var) (S : Ensemble var) 
    (x x' : var) (C : exp_ctx) (S' : Ensemble var) :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    sizeOf_exp_ctx C <= 3. 
  Proof.
    intros Hctx. inv Hctx; eauto.
  Qed.
 
  Lemma Closure_conversion_fundefs_numOf_fundefs Funs (c : cTag) 
        (FVs : list var) (B1 B2 : fundefs) :
    Closure_conversion_fundefs clo_tag Funs c FVs B1 B2 ->
    numOf_fundefs B1 = numOf_fundefs B2.
  Proof.
    intros Hcc; induction Hcc; eauto; simpl. congruence.
  Qed.

  Lemma project_var_not_In_free_set' Scope Funs c Γ FVs x x' C S S'  :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    Disjoint _ S (Scope :|: (Funs \\ Scope)) ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. eauto.
    - eapply Hd; eauto. constructor; eauto. right.
      eexists; eauto.
    - inv Hc. exfalso. eauto.    
  Qed.

  Lemma project_vars_not_In_free_set' Scope Funs c Γ FVs xs xs' C S S' :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Disjoint _ S (Scope :|: (Funs \\ Scope)) ->
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
        eapply project_var_not_In_free_set'; eassumption. 
      + eapply Disjoint_sym. eapply IHHproj.
        eapply Disjoint_Included_l.
        eapply project_var_free_set_Included. eassumption.
        eassumption.
  Qed.

End Closure_conversion_util.