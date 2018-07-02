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

  Instance Proper_FV1 : Proper (Same_set _ ==> eq ==> eq  ==> Same_set _) FV.
  Proof.
    intros s1 s2 Hseq s3 s4 Hseq' x1 x2 Heq; subst; unfold FV;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Instance Proper_FV_cc : Proper (Same_set _ ==> eq ==> eq ==> Same_set _) FV_cc.
  Proof.
    intros s1 s2 Hseq s3 s4 Hseq' x1 x2 Heq; subst; unfold FV_cc;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Instance Proper_FV2 S : Proper (Same_set _ ==> eq  ==> Same_set _) (FV S).
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; unfold FV.
    rewrite !Hseq at 1. reflexivity.
  Qed.
  
  Instance Proper_FV_cc2 S : Proper (Same_set _ ==> eq ==> Same_set _) (FV_cc S).
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; unfold FV_cc;
    rewrite !Hseq at 1. reflexivity.
  Qed.

    (** [FV] and [FV_cc] lemmas *)
  Lemma FV_Union1 Scope Funs FVs S :
    FV (S :|: Scope) Funs FVs \subset 
    S :|: FV Scope Funs FVs.
  Proof.   
    unfold FV.
    now eauto 20 with Ensembles_DB. 
  Qed.

  Lemma FV_cc_Union1 Scope Funs Γ S :
    FV_cc (S :|: Scope) Funs Γ \subset 
    S :|: FV_cc Scope Funs Γ.
  Proof.   
    unfold FV_cc.
    now eauto 20 with Ensembles_DB. 
  Qed.

  Lemma FV_Union2 Scope Funs FVs S :
    FV Scope (S :|: Funs) FVs \subset 
    (Proj1 S) :|: FV Scope Funs FVs.
  Proof with (now eauto with Ensembles_DB).   
    unfold FV.
    rewrite !Proj1_Union, !Setminus_Union_distr at 1.
    eapply Union_Included.
    eapply Union_Included...    
    now eauto with Ensembles_DB.
  Qed.
  
  Lemma FV_cc_Union2 Scope Funs Γ S :
    FV_cc Scope (S :|: Funs) Γ \subset 
    (Proj1 S) :|: (Proj2 S) :|: FV_cc Scope Funs Γ.
  Proof with (now eauto with Ensembles_DB).   
    unfold FV_cc.
    rewrite !Proj1_Union, !Proj2_Union, !Setminus_Union_distr at 1.
    eapply Union_Included.
    eapply Union_Included.
    eapply Union_Included...    
    now eauto with Ensembles_DB.
    now eauto with Ensembles_DB.
  Qed.

  Lemma FV_cc_Setminus1 Scope Funs Γ S {Hd : Decidable S} : 
    FV_cc (Scope \\ S) Funs Γ \subset
    S :|: FV_cc Scope Funs Γ.
  Proof.
    unfold FV_cc.
    eapply Union_Included;
      [| now eauto with Ensembles_DB ].
    eapply Union_Included.
    eapply Union_Included;
    [ now eauto with Ensembles_DB |].
    eapply Included_trans.
    eapply Setminus_Setminus_Included; eassumption.
    now eauto with Ensembles_DB.
    now eauto with Ensembles_DB.
  Qed.

  Lemma FV_Setminus1 Scope Funs FVs S {Hd : Decidable S} : 
    FV (Scope \\ S) Funs FVs \subset
    S :|: FV Scope Funs FVs.
  Proof.
    unfold FV.
    eapply Union_Included.
    eapply Union_Included;
      [ now eauto with Ensembles_DB |].
    eapply Included_trans.
    eapply Setminus_Setminus_Included;
      eauto with typeclass_instances...
    now eauto with Ensembles_DB.
    eapply Included_trans.
    rewrite Union_commut. rewrite <- !Setminus_Union.
    eapply Setminus_Setminus_Included. eassumption.
    rewrite Setminus_Union, Union_commut. 
    now eauto with Ensembles_DB.
  Qed. 


  (** ** Proof that after closure conversion all functions are closed *)

  Lemma project_var_Scope Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    Scope' \subset x |: Scope.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar...
  Qed.

  Lemma project_vars_Scope Scope Scope' Funs c Γ FVs xs C :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    Scope' \subset FromList xs :|: Scope.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; induction Hvar.
    - eauto with Ensembles_DB.
    - eapply Included_trans. eassumption.
      rewrite FromList_cons. eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Included_trans. eapply project_var_Scope.
      eassumption. now eauto with Ensembles_DB. 
  Qed.

  Lemma project_var_Scope_l Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    Scope \subset Scope'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar...
  Qed.

  Lemma project_vars_Scope_l Scope Scope' Funs c Γ FVs xs C :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    Scope \subset Scope'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; induction Hvar.
    - eauto with Ensembles_DB.
    - eapply Included_trans.
      eapply project_var_Scope_l; eassumption.
      eassumption.
  Qed.

  Lemma prod_Proj1 A B (S : Ensemble (A * B)) x y :
    (x, y) \in S -> x \in Proj1 S.
  Proof.
    firstorder.
  Qed.

  Lemma prod_Proj2 A B (S : Ensemble (A * B)) x y :
    (x, y) \in S -> y \in Proj2 S.
  Proof.
    firstorder.
  Qed.
  
  Lemma Prod_proj A B (S1 : Ensemble A) (S2 : Ensemble B) z :
    z \in Prod S1 S2 -> 
    fst z \in S1 /\ snd z \in S2.
  Proof.
    destruct z. firstorder.
  Qed.

  Lemma proj_Prod A B (S1 : Ensemble A) (S2 : Ensemble B) z :
    fst z \in S1 -> snd z \in S2 -> z \in Prod S1 S2.
  Proof.
    destruct z. firstorder.
  Qed.
  
  Lemma project_var_occurs_free_ctx_Included Scope Scope' Funs c Γ FVs x C e F:
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    occurs_free e \subset x |: F ->
    (FV_cc Scope Funs Γ) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hproj Hsub Hsub'. inv Hproj.
    - eapply Included_trans. eassumption.
      eapply Union_Included; [| reflexivity ].
      eapply Singleton_Included. eapply Hsub'. left. left. now left.
    - simpl. normalize_occurs_free. rewrite !FromList_cons, !FromList_nil. 
      rewrite Union_Empty_set_neut_r. eapply Union_Included.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply Hsub'.
        left. left. right. constructor; eauto.
        eapply prod_Proj1. eassumption.
      + eapply Included_trans; [| eassumption ].
        eapply Included_Union_preserv_l.
        eapply Included_Union_preserv_r.
        eapply Singleton_Included. eapply prod_Proj2.
        eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eassumption. reflexivity.
        rewrite Setminus_Union_distr...
    - simpl. normalize_occurs_free.
      eapply Union_Included. eapply Singleton_Included.
      eapply Hsub'. right. reflexivity.
      eapply Included_trans. eapply Included_Setminus_compat.
      eassumption. reflexivity.
      rewrite Setminus_Union_distr...
  Qed.

  Lemma project_var_In Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    x \in Scope'.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.

  Lemma project_vars_In Scope Scope' Funs c Γ FVs xs C :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    FromList xs \subset Scope'.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite FromList_nil...
    - rewrite FromList_cons.
      eapply Union_Included; [| eassumption ].
      eapply Singleton_Included.
      eapply project_vars_Scope_l. eassumption.
      eapply project_var_In. eassumption.
  Qed.

  Lemma project_var_get'
        (Scope Scope' : Ensemble var) Funs (c : cTag) 
        (Γ : var) (FVs : list var) (x : var) (C1 : exp_ctx) 
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block) 
        (m : nat) (y : var) :
    project_var clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    y <> x -> M.get y rho1 = M.get y rho2.
  Proof.
    intros Hvar Hctx Hnin. inv Hvar; inv Hctx; eauto.
    - inv H15. rewrite M.gso; eauto.
    - inv H18. rewrite M.gso; eauto.
  Qed. 
  
  Lemma project_vars_get' Scope Scope' Funs c Γ FVs xs C1
        rho1 H1 rho2 H2 m y:
    project_vars clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    ~ y \in FromList xs ->
    M.get y rho1 = M.get y rho2.
  Proof.
    intros Hvar; revert rho1 H1 rho2 H2 m;
    induction Hvar; intros rho1 H1 rho2 H2 m Hctx Hnin.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l
        as [rho'' [H'' [m1 [m2  [Hctx1 [Hctx2 Hadd]]]]]]; eauto.
      subst. eapply project_var_get' in Hctx1; eauto.
      rewrite Hctx1. eapply IHHvar. eassumption.
      intros Hc. eapply Hnin. now right.
      intros Hc; eapply Hnin. subst; now left.
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
  
  Lemma project_vars_occurs_free_ctx_Included Scope Scope' Funs c Γ
        FVs xs C e F:
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    occurs_free e \subset (FromList xs) :|: F ->
    (FV_cc Scope Funs Γ) \subset F ->
    (occurs_free (C |[ e ]|)) \subset F. 
  Proof with (now eauto with Ensembles_DB). 
    intros Hproj.
    revert F. induction Hproj; intros F Hsub Hsub'; repeat normalize_sets.
    - simpl...
    - rewrite <- app_ctx_f_fuse.
      eapply project_var_occurs_free_ctx_Included; try eassumption.
      eapply IHHproj.
      eapply Included_trans. eassumption.
      now eauto with Ensembles_DB. 
      eapply Included_trans. 
      eapply Included_Union_compat.
      eapply Included_Union_compat.
      eapply Included_Union_compat.
      eapply project_var_Scope. eassumption.
      eapply Included_Setminus_compat. reflexivity.
      eapply project_var_Scope_l. eassumption. 
      reflexivity.
      reflexivity.
      rewrite <- !(Union_assoc [set y]).
      eapply Included_Union_compat. reflexivity. eassumption.
  Qed.
  
  Lemma project_var_free_funs_in_exp Scope Scope' Funs c Γ FVs x C B e:
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof.
    intros Hvar; inv Hvar; [ split; now eauto | | ];
    (split; intros Hf; [ now inv Hf | now constructor ]).
  Qed.
  
  Lemma project_vars_free_funs_in_exp Scope Scope' Funs c Γ FVs xs C B e:
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.

  Lemma project_var_FV_cc Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    FV_cc Scope' Funs Γ \subset x |: FV_cc Scope Funs Γ.
  Proof with (now eauto with Ensembles_DB).  
    intros Hvar; induction Hvar.
    - simpl...
    - unfold FV_cc. rewrite <- !Union_assoc.
      eapply Included_Union_compat...
    - unfold FV_cc. rewrite <- !Union_assoc.
      eapply Included_Union_compat...
  Qed.

  Lemma project_vars_FV_cc Scope Scope' Funs c Γ FVs xs C :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    FV_cc Scope' Funs Γ \subset FromList xs :|: FV_cc Scope Funs Γ.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar.
    - simpl...
    - eapply Included_trans. eassumption.
      eapply Included_trans. eapply Included_Union_compat.
      reflexivity. eapply project_var_FV_cc. eassumption.
      normalize_sets...
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
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       occurs_free (C |[ e' ]|) \subset FV_cc Scope Funs Γ) /\
    (forall B c Funs FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B'),
       (occurs_free_fundefs B') \subset (name_in_fundefs Funs) \\ (name_in_fundefs B')).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Econstr.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      eapply Included_trans. eapply FV_cc_Union1.
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply project_vars_FV_cc. eassumption. 
      now eauto with Ensembles_DB. 
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      inv H9.
      rewrite occurs_free_Ecase_nil...
    - inv H9. destruct y as [c' e'].
      inv H1. simpl in H; subst.
      destruct H0 as [C' [e'' [Heq Hcce]]]. simpl in Heq; subst.
      eapply Included_trans. now eapply occurs_free_Ecase_ctx_app.
      apply Union_Included. 
      + eapply project_var_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
        eapply Included_trans. eapply IHe. eassumption.
        eapply project_var_FV_cc. eassumption.
      + eapply IHl. econstructor; eauto.
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Eproj.
      eapply Union_Included. now eauto with Ensembles_DB. 
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      eapply Included_trans. eapply FV_cc_Union1.
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply project_var_FV_cc. eassumption. 
      now eauto with Ensembles_DB. 
    - rewrite <- app_ctx_f_fuse. simpl. 
      eapply project_vars_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
      normalize_occurs_free. eapply Union_Included.
      now eauto with Ensembles_DB. normalize_occurs_free.
      rewrite Setminus_Union_distr. eapply Union_Included.
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply IHB. eassumption.
      reflexivity. rewrite closure_conversion_fundefs_Same_set; [| eassumption ]. 
      now eauto with Ensembles_DB.
      do 2 eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      eapply Included_trans. eapply FV_cc_Union2.
      do 3 (rewrite closure_conversion_fundefs_Same_set with (B1 := f2) at 1;
            [| eassumption ]).
      
      eapply Union_Included.
      eapply Included_trans. eapply Included_Union_compat.
      eapply Proj1_Prod_Included.
      eapply Proj2_Prod_Included.
      now eauto with Ensembles_DB. 

      eapply Included_trans. eapply FV_cc_Setminus1.
      now eauto with typeclass_instances.
      eapply Union_Included. now eauto with Ensembles_DB.
      
      eapply Included_trans;
        [ eapply project_vars_FV_cc; eassumption |]...
      
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
      eapply Included_trans. eapply FV_cc_Union1.
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply project_vars_FV_cc. eassumption.
      now eauto with Ensembles_DB...
       - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Ehalt...
    - eapply Included_Setminus.
      constructor. intros v' Hc. inv Hc.
      now eapply fun_names_not_free_in_fundefs; eauto.
      rewrite occurs_free_fundefs_Fcons.
      apply Union_Included.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHe. eassumption.
        unfold FV_cc. simpl.
        rewrite FromList_cons.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        rewrite <- (Union_assoc (FromList l)). eapply Union_Included.
        now eauto with Ensembles_DB.
        eapply Included_trans. eapply Included_Union_compat.
        eapply Included_trans. eapply Setminus_Included.
        eapply Proj1_Prod_Included.
        eapply Proj2_Prod_Included.
        now eauto with Ensembles_DB.  
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHB. eassumption.
        now eauto with Ensembles_DB. 
    - rewrite occurs_free_fundefs_Fnil. now apply Included_Empty_set.
  Qed.
  
  Corollary Closure_conversion_occurs_free_Included :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       occurs_free (C |[ e' ]|) \subset (FV_cc Scope Funs Γ)).
  Proof.
    now eapply Closure_conversion_occurs_free_Included_mut.
  Qed.
  
  Corollary Closure_conversion_occurs_free_fundefs_Included :
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B'),
       Included _ (occurs_free_fundefs B') (Setminus _ (name_in_fundefs Funs) (name_in_fundefs B'))).
  Proof.
    intros. 
    eapply Closure_conversion_occurs_free_Included_mut; eauto.
  Qed.
  
  Lemma Closure_conversion_closed_fundefs_mut :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       closed_fundefs_in_exp (C |[ e' ]|)) /\
    (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B'),
       closed_fundefs_in_fundefs B').
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; eassumption.
    - inv H9. 
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H3.
    - inv H9. destruct H1 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
      simpl in *; subst.
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H4.
      + inv H. eapply IHe; eassumption.
      + eapply IHl. now econstructor; eauto.
        rewrite project_var_free_funs_in_exp.
        econstructor; eassumption. eassumption.
    - intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; eassumption. 
    - rewrite <- app_ctx_f_fuse. intros B HB.
      rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      simpl in HB. inv HB. inv H5.
      + split; [| now apply Included_Empty_set ].
        eapply Included_trans.
        eapply Closure_conversion_occurs_free_Included_mut. eassumption.
        rewrite closure_conversion_fundefs_Same_set; [| eassumption ].
        rewrite Setminus_Same_set_Empty_set. now apply Included_Empty_set.
      + eapply IHe; eassumption.
      + eapply IHB; eassumption.
    - intros B HB.  rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H1. inv H4.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; eassumption.
    - intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB.
    - intros B HB. inv HB.
      + eapply IHe; eassumption.
      + eapply IHB; eassumption.
    - intros B HB. inv HB.
  Qed.
  
  (** * Lemmas about [project_var] and [project_vars] *)

(*  Lemma project_var_free_set_Included Scope c Γ FVs x x' C S S' :
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
 *)

  Lemma project_var_FV_eq Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    FV Scope Funs FVs <--> FV Scope' Funs FVs.
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    - reflexivity.
    - rewrite !(Union_commut [set x] Scope) at 2.
      rewrite <- (Union_assoc Scope [set x] (Proj1 Funs)).
      rewrite (Union_Same_set [set x] (Proj1 Funs));
        [|  eapply Singleton_Included; eapply prod_Proj1; eassumption ]. 
      rewrite <- !Setminus_Union.
      rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
      rewrite <- (Union_Same_set [set x] ((Proj1 Funs) \\ Scope));
        [| eapply Singleton_Included; constructor; eauto; eapply prod_Proj1; eassumption ]. 
      now eauto with Ensembles_DB. 
    - rewrite <- !(Setminus_Union (Proj1 Funs) [set x]).
      rewrite (Setminus_Disjoint (Proj1 Funs) [set x]);
        [| now eapply Disjoint_Singleton_r; eauto ].
      rewrite !(Union_commut [set x] Scope) at 2.
      rewrite <- (Union_assoc Scope [set x] (Proj1 Funs)).
      rewrite !(Union_commut [set x] (Proj1 Funs)) at 1.
      rewrite (Union_assoc Scope (Proj1 Funs) [set x]).
      rewrite <- (Setminus_Union (FromList FVs) (Scope :|: (Proj1 Funs))).
      rewrite (Union_Setminus_Included _ _ [set x]);
        eauto with Ensembles_DB typeclass_instances.
      rewrite <- !(Union_assoc [set x]).
      rewrite (Union_Same_set [set x] _). reflexivity.
      eapply Singleton_Included. right. 
      constructor; eauto.
      eapply nthN_In. eassumption.
      intros Hc; inv Hc; eauto. 
  Qed.

  Lemma project_vars_FV_eq Scope Scope' Funs c Γ FVs xs C :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    FV Scope Funs FVs <--> FV Scope' Funs FVs.
  Proof.
    intros Hvar. induction Hvar; eauto.
    - reflexivity.
    - rewrite project_var_FV_eq; [| eassumption ]. eassumption.
  Qed.

  
  Lemma project_var_In_Union Scope Scope' Funs c Γ FVs x C :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    x \in (FV Scope Funs FVs).
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    - left. right. constructor; eauto.
      eapply prod_Proj1; eassumption.
    - right. constructor; eauto. eapply nthN_In. eassumption.
      intros Hc; inv Hc; eauto. 
  Qed.
  
  Lemma project_vars_In_Union Scope Funs c Γ FVs xs C Scope' :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    (FromList xs) \subset (FV Scope Funs FVs).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - rewrite FromList_nil. now apply Included_Empty_set.
    - rewrite FromList_cons.
      
      eapply Union_Included.
      eapply Singleton_Included. eapply project_var_In_Union; eassumption.
      rewrite project_var_FV_eq; eassumption.
  Qed.

  Lemma Closure_conversion_pre_occurs_free_Included_mut :
    (forall e Scope Funs c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs c Γ FVs e e' C),
       occurs_free e \subset FV Scope Funs FVs) /\
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
        eapply Included_trans. eapply FV_Union1.
        rewrite <- project_vars_FV_eq; [| eassumption ]...
    - normalize_occurs_free. eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + inv H9. simpl in H1. destruct H1 as (Heq & C' & e' & Heq' & Hcc).
        destruct y; simpl in *; subst.
        eapply Union_Included.
        rewrite project_var_FV_eq; [| eassumption ]. now eapply IHe; eauto.
        eapply IHl; eauto. econstructor; try eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + eapply Included_trans.
        eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply FV_Union1.
        rewrite <- project_var_FV_eq; [| eassumption ]...
    - normalize_occurs_free. eapply Union_Included.
      + eapply Included_trans. eapply IHB; eauto.
        rewrite <- H1. reflexivity.
        eapply project_vars_In_Union; eauto.
      + eapply Included_trans. eapply Included_Setminus_compat.
        now eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        eapply Included_trans.
        eapply FV_Setminus1. now eauto with typeclass_instances.
        eapply Union_Included. now eauto with Ensembles_DB.
        eapply Included_trans. eapply FV_Union2.
        eapply Included_trans. eapply Included_Union_compat.
        eapply Proj1_Prod_Included. reflexivity.
        rewrite <- project_vars_FV_eq; [| eassumption ]...
    - normalize_occurs_free. inv H3. eapply Union_Included.
      + rewrite project_var_FV_eq; [| eassumption ].
        eapply project_vars_In_Union. eassumption.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
    - normalize_occurs_free.
      eapply Union_Included.
      + eapply project_vars_In_Union. eassumption.
      + eapply Included_trans. eapply Included_Setminus_compat.
        eapply IHe; eauto. reflexivity.
        eapply Setminus_Included_Included_Union.
        eapply Included_trans. eapply FV_Union1.
        rewrite <- project_vars_FV_eq; [| eassumption ]...
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

  Lemma project_var_get Scope Scope' Funs c Γ FVs x C1 rho1 H1 rho2 H2 m y:
    project_var clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    ~ In _ (Scope' \\ Scope) y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx. inv H15.
      rewrite M.gso. reflexivity. intros Hc; inv Hc.
      eapply Hin. constructor. now left. eassumption.
    - inv Hctx. inv H18.
      rewrite M.gso. reflexivity. intros Hc; inv Hc.
      eapply Hin. constructor. now left. eassumption.
  Qed.    
  
  Lemma project_vars_get Scope Scope' Funs c Γ FVs xs C1 rho1 H1 rho2 H2 m y:
    project_vars clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    ~ In _ (Scope' \\ Scope) y ->
    M.get y rho1 = M.get y rho2.
  Proof.
    intros Hvar; revert rho1 H1 rho2 H2 m; induction Hvar; intros rho1 H1 rho2 H2 m Hctx Hnin. 
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho'' [H'' [m1 [m2  [Hctx1 [Hctx2 Hadd]]]]]]; eauto.
      subst. eapply project_var_get in Hctx1; eauto.
      rewrite Hctx1. eapply IHHvar. eassumption.
      intros Hc. inv Hc. eapply Hnin. constructor; eauto.
      intros Hc; eapply H3.
      eapply project_var_Scope_l; eassumption.
      intros Hc. inv Hc. eapply Hnin. constructor; eauto.
      eapply project_vars_Scope_l; eassumption.
  Qed.
  
  Lemma project_var_getlist Scope Scope' Funs c Γ FVs x C1 rho1 H1 rho2 H2 m ys :
    project_var clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ (Scope' \\ Scope) (FromList ys) ->
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
  

  Lemma project_vars_getlist Scope Scope' Funs c Γ FVs xs C1 rho1 H1 rho2 H2 m ys :
    project_vars clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ (Scope' \\ Scope) (FromList ys) ->
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
  Lemma project_var_env_locs Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m e :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) H1 ->
    env_locs rho1 (occurs_free (C |[ e ]|)) \subset dom H1 ->
    env_locs rho2 (occurs_free e) \subset dom  H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl in *; eauto.
    - inv H15.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      rewrite HL.alloc_dom; [| eassumption ]...
      eapply Included_trans; [| eapply HL.alloc_dom; eassumption ]. 
      eapply Included_Union_preserv_r. eapply Included_trans; [| eassumption ].
      simpl. normalize_occurs_free.
      eapply env_locs_monotonic...
    - inv H18.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        simpl. normalize_occurs_free.
        rewrite (reach_unfold H2 (env_locs rho1 (Γ |: (occurs_free e \\ [set x])))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ].
        rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ]. simpl. normalize_occurs_free...
  Qed.
  
  Lemma project_var_env_locs' Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs Γ) \subset dom H1 ->
    env_locs rho2 (FV_cc Scope' Funs Γ) \subset dom H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - eassumption.
    - inv H15.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      rewrite HL.alloc_dom; [| eassumption ].
      eapply Included_Union_compat. reflexivity.
      eapply Included_trans. eapply env_locs_monotonic.
      eapply Setminus_Included_Included_Union.
      erewrite (Union_commut _ [set x]).
      eapply FV_cc_Union1. eassumption.
    - inv H18.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        unfold FV_cc. rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H2 (env_locs rho1 ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ].
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic.
        now eauto 20 with Ensembles_DB.
  Qed.
  
  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m e :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    (env_locs rho1 (occurs_free (C |[ e ]|))) \subset dom H1 ->
    well_formed (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free e))) H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H15.
      eapply well_formed_antimon; [| eapply well_formed_reach_alloc; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        simpl. normalize_occurs_free. rewrite <- Union_assoc.
        eapply Included_Union_preserv_r. eapply Included_Union_Setminus.
        now eauto with typeclass_instances.
      + simpl. normalize_occurs_free. repeat normalize_sets.
        simpl in H13.
        destruct (M.get x rho1) as [v1 |] eqn:Hget1; try congruence. 
        destruct (M.get Γ' rho1) as [v2 |] eqn:Hget2; try congruence. 
        inv H13.
        eapply Included_trans; [| eapply reach'_extensive ].
        rewrite !env_locs_Union, !env_locs_Singleton; eauto.
        simpl...
    - inv H18.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        simpl. normalize_occurs_free.
        rewrite <- Union_assoc.
        eapply Included_Union_preserv_r. eapply Included_Union_Setminus.
        now eauto with typeclass_instances.
      + simpl. eapply well_formed_antimon; try eassumption.
        simpl. normalize_occurs_free.
        rewrite (reach_unfold H2 (env_locs rho1 (Γ |: (occurs_free e \\ [set x])))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic. rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.

  (* 
  Lemma project_var_reachable Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m e :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    reach' H2 (env_locs rho2 (occurs_free e)) \subset
    reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|))).
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx. inv Hvar; inv Hctx; try reflexivity.
    - simpl. normalize_occurs_free. inv H15.
      simpl in H13.
      destruct (M.get x rho1) as [v1 |] eqn:Hget1; try congruence. 
      destruct (M.get Γ rho1) as [v2 |] eqn:Hget2; try congruence. 
      inv H13. eapply Included_trans. 
      eapply Included_trans; [| eapply reach'_alloc_set; try eassumption ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic.
      eapply Included_Union_preserv_l. reflexivity. simpl. set_Inlcuded'.
      rewrite !env_locs_Union, !reach'_Union, env_locs_Singleton; eauto.
      eapply Included_Union_compat; try reflexivity.
      rewrite (reach_unfold H' (val_loc (Loc l))).
      eapply Included_Union_preserv_r. 
      eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; eauto.
      simpl. eapply In_Union_list. eapply in_map.
      eapply nthN_In. eassumption.
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
   *)


  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed' Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    (env_locs rho1 (FV_cc Scope Funs Γ)) \subset dom H1 ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs Γ))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope' Funs Γ))) H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H15.
      eapply well_formed_antimon; [| eapply well_formed_reach_alloc; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Included_trans; [ eapply FV_cc_Union1 |]...
      + simpl. simpl in H13.
        destruct (M.get x rho1) as [v1 |] eqn:Hget1; try congruence. 
        destruct (M.get Γ' rho1) as [v2 |] eqn:Hget2; try congruence. 
        inv H13.
        eapply Included_trans; [| eapply reach'_extensive ].
        simpl. eapply Union_Included. eapply get_In_env_locs; [| eassumption ].
        left; left; right. constructor; eauto. eapply prod_Proj1; eassumption.
        rewrite Union_Empty_set_neut_r.
        eapply get_In_env_locs; [| eassumption ]. left; right.
        eapply prod_Proj2; eassumption.
    - inv H18.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Included_trans; [ eapply FV_cc_Union1 |]...
      + simpl. eapply well_formed_antimon; try eassumption.
        unfold FV_cc. 
        rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H2 (env_locs rho1 ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic.
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.
  
  Lemma project_var_env_locs_subset Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m S1 :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    Disjoint _ S1 (Scope' \\ Scope) ->
    env_locs rho2 S1 <--> env_locs rho1 S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx HD. destruct Hvar; inv Hctx; try reflexivity.
    - inv H15. rewrite env_locs_set_not_In. reflexivity.
      intros Hc. eapply HD; eauto. constructor; eauto.
      constructor. now left.  eassumption.
    - inv H18. rewrite env_locs_set_not_In. reflexivity.
      intros Hc. eapply HD; eauto. constructor; eauto.
      constructor. now left.  eassumption.
  Qed.
  
  Lemma project_vars_env_locs_subset Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m S1 :
      project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
      ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
      Disjoint _ S1 (Scope' \\ Scope) ->
      env_locs rho2 S1 <--> env_locs rho1 S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho1 H1 rho2 H2 m. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hd.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst. rewrite IHHvar; eauto.
      rewrite project_var_env_locs_subset; eauto.
      reflexivity. eapply Disjoint_Included_r; try eassumption.
      eapply Included_Setminus_compat; [| reflexivity ].
      eapply project_vars_Scope_l. eassumption.
      eapply Disjoint_Included_r; [| eassumption ].
      eapply Included_Setminus_compat; [ reflexivity |].
      eapply project_var_Scope_l. eassumption.
  Qed.

  Lemma project_var_subheap Scope Scope' Funs c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs c Γ FVs x C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    H1 ⊑ H2. 
  Proof.
    intros Hvar Hctx; inv Hvar; inv Hctx; eauto.
    now apply HL.subheap_refl. 
    inv H15. now eapply HL.alloc_subheap; eauto.
    inv H18. now apply HL.subheap_refl. 
  Qed.
  
  Lemma project_vars_subheap Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    H1 ⊑ H2. 
  Proof.
    intros Hvar. revert rho1 H1 rho2 H2 m. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx.
    - inv Hctx; now apply HL.subheap_refl.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply HL.subheap_trans. eapply project_var_subheap; eassumption. 
      eapply IHHvar. eassumption.
  Qed.

  Lemma project_vars_env_locs Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m e :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    (env_locs rho1 (occurs_free (C |[ e ]|))) \subset dom H1 ->
    well_formed (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) H1 ->
    (env_locs rho2 (occurs_free e)) \subset dom H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho1 H1 rho2 H2 m e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_env_locs; try eassumption.
      eapply project_var_well_formed; try eassumption. 
  Qed.
  
  Lemma project_vars_env_locs' Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs Γ) \subset dom H1 ->
    env_locs rho2 (FV_cc Scope' Funs Γ) \subset dom H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho1 H1 rho2 H2 m. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hlocs Hwf.
    - inv Hctx. eassumption.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply IHHvar.  eassumption. 
      eapply project_var_well_formed'; eassumption.
      eapply project_var_env_locs'; eassumption.
  Qed.
  
  Lemma project_vars_well_formed Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m e :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (occurs_free (C |[ e ]|)))) H1 ->
    env_locs rho1 (occurs_free (C |[ e ]|)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free e))) H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho1 H1 rho2 H2 m e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_well_formed; eassumption.
      eapply project_var_env_locs; eassumption.
  Qed.
  
  Lemma project_vars_well_formed' Scope Scope' Funs c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs c Γ FVs xs C Scope' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs Γ) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope' Funs Γ))) H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho1 H1 rho2 H2 m. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply IHHvar.  eassumption. 
      eapply project_var_well_formed'; eassumption.
      eapply project_var_env_locs'; eassumption.
  Qed.

End CCUtil. 