(* Syntactic properties of closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From L6 Require Import cps cps_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions eval tactics.
From L6.Heap Require Import closure_conversion compat heap GC.

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

  Import H C C.LR C.LR.Sem C.LR.Sem.GC C.LR.Sem.GC.Equiv C.LR.Sem.GC.Equiv.Defs.

  Variable clo_tag : cTag.

  Instance Proper_FV1 : Proper (Same_set _ ==> eq ==> eq  ==> Same_set _) FV.
  Proof.
    intros s1 s2 Hseq s3 s4 Hseq' x1 x2 Heq; subst; unfold FV;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Instance Proper_FV_cc : Proper (Same_set _ ==> eq ==> eq ==> eq ==> Same_set _) FV_cc.
  Proof.
    intros s1 s2 Hseq s3 s4 Hseq' x1 x2 Heq x3 x4 Heq'; subst; unfold FV_cc;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Instance Proper_FV2 S : Proper (Same_set _ ==> eq  ==> Same_set _) (FV S).
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; unfold FV.
    rewrite !Hseq at 1. reflexivity.
  Qed.
  
  Instance Proper_FV_cc2 S : Proper (Same_set _ ==> eq ==> eq ==> Same_set _) (FV_cc S).
  Proof.
    intros s1 s2 Hseq x1 x2 Heq x3 x4 Heq'; subst; unfold FV_cc;
    rewrite !Hseq at 1. reflexivity.
  Qed.

  Instance Proper_FV_cc3 S Funs : Proper (f_eq ==> eq ==> Same_set _) (FV_cc S Funs).
  Proof.
    intros f1 f2 Hfeq x1 x2 Heq; subst; unfold FV_cc.
    rewrite Hfeq. reflexivity. 
  Qed.
  
  (** [FV] and [FV_cc] lemmas *)
  Lemma FV_Union1 Scope Funs FVs S :
    FV (S :|: Scope) Funs FVs \subset 
    S :|: FV Scope Funs FVs.
  Proof.   
    unfold FV.
    now eauto 20 with Ensembles_DB. 
  Qed.

  Lemma FV_cc_Union1 Scope Funs fenv Γ S :
    FV_cc (S :|: Scope) Funs fenv Γ \subset 
    S :|: FV_cc Scope Funs fenv Γ.
  Proof.   
    unfold FV_cc.
    now eauto 20 with Ensembles_DB. 
  Qed.

  Lemma FV_Union2 Scope Funs FVs S :
    FV Scope (S :|: Funs) FVs \subset 
    S :|: FV Scope Funs FVs.
  Proof with (now eauto with Ensembles_DB).   
    unfold FV.
    eapply Union_Included.
    eapply Union_Included.
    now eauto with Ensembles_DB.
    rewrite Setminus_Union_distr. 
    now eauto with Ensembles_DB.
    now eauto with Ensembles_DB.
  Qed.
   
  Lemma FV_cc_Union2 Scope Funs fenv Γ S :
    FV_cc Scope (S :|: Funs) fenv Γ \subset 
    S :|: (image fenv S) :|: FV_cc Scope Funs fenv Γ.
  Proof with (now eauto with Ensembles_DB).   
    unfold FV_cc.
    rewrite !Setminus_Union_distr at 1. 
    rewrite !image_Union.
    eapply Union_Included.
    eapply Union_Included.
    eapply Union_Included...    
    eapply Union_Included...    
    now eauto with Ensembles_DB.
  Qed.
  
  Lemma FV_cc_Setminus1 Scope Funs fenv Γ S {Hd : Decidable S} : 
    FV_cc (Scope \\ S) Funs fenv Γ \subset
    S :|: (image fenv S) :|: FV_cc Scope Funs fenv Γ.
  Proof.
    unfold FV_cc.
    eapply Union_Included;
      [| now eauto with Ensembles_DB ]...
    eapply Union_Included.
    eapply Union_Included;
      [ now eauto with Ensembles_DB |].
    eapply Included_trans. 
    eapply Setminus_Setminus_Included. eassumption.    
    eapply Union_Included;
    now eauto with Ensembles_DB.
    eapply Included_trans.
    eapply image_monotonic. 
    eapply Setminus_Setminus_Included. eassumption.    
    rewrite image_Union. 
    eapply Union_Included;
    now eauto with Ensembles_DB.
  Qed. 

    Lemma FV_cc_Setminus2 Scope Funs fenv Γ S {Hd : Decidable S} : 
    FV_cc Scope (Funs \\ S) fenv Γ \subset
    FV_cc Scope Funs fenv Γ.
  Proof.
    unfold FV_cc.
    eapply Union_Included;
      [| now eauto with Ensembles_DB ]...
    eapply Union_Included. now eauto with Ensembles_DB.
    eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
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
    eapply Setminus_Setminus_Included. eassumption.    
    eapply Union_Included;
    now eauto with Ensembles_DB.
    eapply Included_trans.
    rewrite Union_commut. rewrite <- !Setminus_Union.
    eapply Setminus_Setminus_Included. eassumption.
    rewrite Setminus_Union, Union_commut. 
    now eauto with Ensembles_DB.
  Qed.

  Lemma FV_cc_Funs_monotonic Scope Funs Funs' fenv Γ : 
    Funs' \subset Funs ->
    FV_cc Scope Funs' fenv Γ \subset FV_cc Scope Funs fenv Γ.
  Proof.
    unfold FV_cc. intros Hsub.
    eapply Included_Union_compat; [| reflexivity ].
    eapply Included_Union_compat.
    eapply Included_Union_compat. reflexivity.
    now eauto with Ensembles_DB.
    eapply image_monotonic. now eauto with Ensembles_DB.
  Qed.


  Lemma FV_Setminus2 Scope Funs FVs S {Hd : Decidable S} : 
    FV Scope (Funs \\ S) FVs \subset
    S :|: FV Scope Funs FVs.
  Proof.
    unfold FV.
    eapply Union_Included.
    eapply Union_Included;
      [ now eauto with Ensembles_DB |].
    now eauto with Ensembles_DB.
    rewrite <- !Setminus_Union.
    eapply Included_trans. eapply Setminus_Setminus_Included.
    eassumption. now eauto with Ensembles_DB.
  Qed.

  Lemma extend_fundefs'_get_s f B x z :
    z \in name_in_fundefs B ->
          extend_fundefs' f B x z = x.
  Proof.
    intros Heq. unfold extend_fundefs'.
    destruct (Dec z); eauto.
    exfalso; eauto.
  Qed.

  Lemma extend_fundefs'_get_o f B x z :
    ~ z \in name_in_fundefs B ->
    extend_fundefs' f B x z = f z.
  Proof.
    intros Heq. unfold extend_fundefs'.
    destruct (Dec z); eauto.
    exfalso; eauto.
  Qed.

  Lemma extend_fundefs'_image f B x :
    image (extend_fundefs' f B x) (name_in_fundefs B) \subset [set x].  
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]]. 
    rewrite extend_fundefs'_get_s in Heq. subst; eauto.
    eassumption.
  Qed.

  Lemma extend_fundefs'_image_Included f B x S :
    image (extend_fundefs' f B x) S \subset x |: image f S.  
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]]. 
    unfold extend_fundefs' in *.
    destruct (Dec z); subst; eauto.
    right. eexists; split; eauto.
  Qed.

  Lemma extend_fundefs'_image_Included' f B x S :
    image (extend_fundefs' f B x) S \subset x |: image f (S \\ name_in_fundefs B).  
  Proof.
    intros y Hin.
    destruct Hin as [z [Hin' Heq]]. 
    unfold extend_fundefs' in *.
    destruct (Dec z); subst; eauto.
    right. eexists; split; eauto. constructor; eauto. 
  Qed.

  Lemma extend_fundefs'_same_funs f B B' x :
    name_in_fundefs B <--> name_in_fundefs B' ->
    f_eq (extend_fundefs' f B x) (extend_fundefs' f B' x).
  Proof.
    intros Heq y. unfold extend_fundefs'. destruct Heq.
    destruct (@Dec _ (name_in_fundefs B) _ y);
      destruct (@Dec _ (name_in_fundefs B') _ y); eauto.
    eapply H in n. now exfalso; eauto.
    eapply H0 in n0. now exfalso; eauto.
  Qed.
  

  Lemma FV_cc_extend_fundefs Scope Funs fenv B x Γ :
    FV_cc Scope Funs (extend_fundefs' fenv B x) Γ \subset 
    [set x] :|: FV_cc Scope Funs fenv Γ.
  Proof with (now eauto with Ensembles_DB).   
    unfold FV_cc.
    eapply Union_Included.
    eapply Union_Included.
    eapply Union_Included...
    eapply Included_trans. eapply extend_fundefs'_image_Included...
    now eauto with Ensembles_DB.
    now eauto with Ensembles_DB.
  Qed.

  (** ** Proof that after closure conversion all functions are closed *)

  Lemma project_var_Scope Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    Scope' \subset x |: Scope.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar...
  Qed.

  Lemma project_vars_Scope Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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

  Lemma project_var_Scope_l Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    Scope \subset Scope'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar...
  Qed.
  
  Lemma project_vars_Scope_l Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    Scope \subset Scope'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; induction Hvar.
    - eauto with Ensembles_DB.
    - eapply Included_trans.
      eapply project_var_Scope_l; eassumption.
      eassumption.
  Qed.

  Lemma project_var_Funs Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    Funs \subset x |: Funs'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar; try eauto with Ensembles_DB.

    rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances.
  Qed.

  Lemma project_vars_Funs Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    Funs \subset FromList xs :|: Funs'.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; induction Hvar.
    - eauto with Ensembles_DB.
    - eapply Included_trans. eapply project_var_Funs. eassumption.
      rewrite FromList_cons. eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Included_trans. eassumption.
      now eauto with Ensembles_DB. 
  Qed.

  Lemma project_var_Funs_l Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    Funs' \subset Funs.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; inv Hvar...
  Qed.
  
  Lemma project_vars_Funs_l Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    Funs' \subset Funs.
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar; induction Hvar.
    - eauto with Ensembles_DB.
    - eapply Included_trans. eassumption.
      eapply project_var_Funs_l; eassumption.
  Qed.

  Lemma project_var_occurs_free_ctx_Included Scope Scope' Funs Funs' fenv c Γ FVs x C e F:
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    occurs_free e \subset x |: F ->
    (FV_cc Scope Funs fenv Γ) \subset F ->
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
        left. left. right. constructor; eassumption.
      + eapply Included_trans; [| eassumption ].
        eapply Included_Union_preserv_l.
        eapply Included_Union_preserv_r.
        eapply Singleton_Included. now eapply In_image.
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


  Lemma project_var_Union_eq (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (xs : var) (C1 : exp_ctx) :
    project_var clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    ~ xs \in FromList FVs ->
    Scope' :|: Funs' <--> Scope :|: Funs.
  Proof.
    intros Hv Hnin. assert (Hv' := Hv). inv Hv.
    - reflexivity.
    - rewrite (Union_commut [set xs]), <- Union_assoc.
      rewrite <- Union_Setminus_Same_set. reflexivity.
      tci. now eapply Singleton_Included.
    - exfalso. eapply Hnin. eapply nthN_In. eassumption. 
  Qed.
  
  Lemma project_var_In Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    x \in Scope'.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.

  Lemma project_vars_In Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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
        (Scope Scope' : Ensemble var) Funs Funs' fenv (c : cTag) 
        (Γ : var) (FVs : list var) (x : var) (C1 : exp_ctx) 
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block) 
        (m : nat) (y : var) :
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    y <> x -> M.get y rho1 = M.get y rho2.
  Proof.
    intros Hvar Hctx Hnin. inv Hvar; inv Hctx; eauto.
    - inv H15. rewrite M.gso; eauto.
    - inv H18. rewrite M.gso; eauto.
  Qed. 
  
  Lemma project_vars_get' Scope Scope' Funs Funs' fenv c Γ FVs xs C1
        rho1 H1 rho2 H2 m y :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
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
  
  Lemma project_vars_occurs_free_ctx_Included Scope Scope' Funs Funs' fenv c Γ
        FVs xs C e F:
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    occurs_free e \subset (FromList xs) :|: F ->
    (FV_cc Scope Funs fenv Γ) \subset F ->
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
      eapply Included_Setminus_compat. 
      eapply project_var_Funs_l. eassumption.
      eapply project_var_Scope_l. eassumption.
      
      eapply image_monotonic.
      eapply Included_Setminus_compat. 
      eapply project_var_Funs_l. eassumption.
      eapply project_var_Scope_l. eassumption.
      reflexivity.
      rewrite <- !(Union_assoc [set y]).
      eapply Included_Union_compat. reflexivity. eassumption.
  Qed.
  
  Lemma project_var_free_funs_in_exp Scope Scope' Funs Funs' fenv c Γ FVs x C B e :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof.
    intros Hvar; inv Hvar; [ split; now eauto | | ];
    (split; intros Hf; [ now inv Hf | now constructor ]).
  Qed.
  
  Lemma project_vars_free_funs_in_exp Scope Scope' Funs Funs' fenv c Γ FVs xs C B e :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.
  
  Lemma project_var_FV_cc Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    FV_cc Scope' Funs' fenv Γ \subset x |: FV_cc Scope Funs fenv Γ.
  Proof with (now eauto with Ensembles_DB).  
    intros Hvar; induction Hvar.
    - simpl...
    - eapply Included_trans. eapply FV_cc_Union1.
      eapply Included_trans. eapply Included_Union_compat. reflexivity.
      eapply FV_cc_Setminus2. 
      eauto with Ensembles_DB typeclass_instances. reflexivity.
    - eapply Included_trans. eapply FV_cc_Union1. reflexivity. 
  Qed.

  Lemma project_vars_FV_cc Scope Scope' Funs Funs' c Γ FVs xs C fenv :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    FV_cc Scope' Funs' fenv Γ \subset FromList xs :|: FV_cc Scope Funs fenv Γ.
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
    (forall e Scope Funs fenv c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C),
       occurs_free (C |[ e' ]|) \subset FV_cc Scope Funs fenv Γ) /\
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
      eapply Included_trans.
      eapply FV_cc_Union1. rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
      eapply Included_trans. eapply project_vars_FV_cc. eassumption. 
      now eauto with Ensembles_DB. 
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      inv H10.
      rewrite occurs_free_Ecase_nil...
    - inv H10. destruct y as [c' e'].
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
      eapply Included_trans.
      eapply FV_cc_Union1. rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
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
      eapply Union_Included.
      now eauto with Ensembles_DB.
      
      eapply Included_trans. rewrite extend_fundefs'_same_funs.
      eapply extend_fundefs'_image. eapply closure_conversion_fundefs_Same_set.
      eassumption.
      now eauto with Ensembles_DB. 

      eapply Included_trans. eapply FV_cc_Setminus1. now eauto with typeclass_instances.
      eapply Union_Included.
      eapply Union_Included.
      now eauto with Ensembles_DB.

      rewrite <- (closure_conversion_fundefs_Same_set) at 1 ; [| eassumption ].
      eapply Included_trans. eapply extend_fundefs'_image. now eauto with Ensembles_DB. 
      eapply Included_trans. eapply FV_cc_extend_fundefs.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Included_trans. 
      eapply project_vars_FV_cc.
      eassumption.
      now eauto with Ensembles_DB.
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
      eapply Included_trans.
      eapply FV_cc_Union1. rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
      eapply Included_trans. eapply project_vars_FV_cc. eassumption. 
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
        eapply Included_trans. eapply IHe. eassumption.
        unfold FV_cc. simpl.
        rewrite FromList_cons.
        eapply Union_Included; [ | now eauto with Ensembles_DB ].
        rewrite <- (Union_assoc (FromList l)). eapply Union_Included.
        now eauto with Ensembles_DB.
        eapply Union_Included.
        (* eapply Included_trans. eapply Included_Setminus_compat.  *)
        (* eapply Ensembles_util.Included_Intersection_l. reflexivity.  *)
        now eauto with Ensembles_DB.
        
        eapply Included_trans. eapply image_monotonic.
        now eapply Setminus_Included. 
        (* eapply Included_trans. now eapply Setminus_Included. *)
        (* eapply Ensembles_util.Included_Intersection_l. *)
        eapply Included_trans. eapply extend_fundefs'_image.
        now eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHB. eassumption.
        now eauto with Ensembles_DB. 
    - rewrite occurs_free_fundefs_Fnil. now apply Included_Empty_set.
  Qed.
  
  Corollary Closure_conversion_occurs_free_Included :
    (forall e Scope Funs fenv c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C),
       occurs_free (C |[ e' ]|) \subset (FV_cc Scope Funs fenv Γ)).
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

  Lemma project_var_occurs_free_eq Scope Scope' Funs Funs' fenv c Γ FVs x C e:
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    occurs_free (C |[ e ]|) \subset x |: occurs_free e :|: image fenv (Funs \\ Scope) :|: [set Γ]. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hvar. inv Hvar.
    - simpl. now eauto with Ensembles_DB.
    - simpl. normalize_occurs_free. rewrite FromList_cons, FromList_singleton.
      eapply Union_Included.
      eapply Union_Included.
      now eauto with Ensembles_DB.
      eapply Singleton_Included. left. right. eexists; split; eauto.
      now constructor; eauto.
      now eauto with Ensembles_DB. 
    - simpl. normalize_occurs_free...
  Qed.

  Lemma project_vars_occurs_free_eq Scope Scope' Funs Funs' fenv c Γ FVs xs C e:
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    occurs_free (C |[ e ]|) \subset FromList xs :|: occurs_free e :|: image fenv (Funs \\ Scope) :|: [set Γ].
  Proof with (now eauto with Ensembles_DB).
    intros Hvars; induction Hvars. simpl...
    simpl. rewrite <- app_ctx_f_fuse.
    eapply Included_trans. eapply project_var_occurs_free_eq. eassumption.
    normalize_sets.
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Union_Included; [ now eauto with Ensembles_DB | ].
    eapply Included_trans. eassumption.
    eapply Union_Included; [| now eauto with Ensembles_DB ].
    eapply Union_Included; [ now eauto with Ensembles_DB | ].
    eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
    eapply image_monotonic.
    eapply Included_Setminus_compat. eapply project_var_Funs_l. eassumption. 
    eapply Included_trans. eapply project_var_Scope_l. eassumption. reflexivity. 
  Qed. 


  Lemma Closure_conversion_fv_sub e Scope Funs fenv c Γ FVs e' C 
        (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C) :
    occurs_free (C |[ e' ]|) \subset (occurs_free e) :|: image fenv (Funs \\ Scope) :|: [set Γ]. 
  Proof with (now eauto with Ensembles_DB).
    revert Scope Funs fenv c Γ FVs e' C Hcc; induction e using exp_ind';
    intros Scope Funs fenv c' Γ FVs e' C Hcc; inv Hcc.
    - repeat normalize_occurs_free.
      eapply Included_trans. eapply project_vars_occurs_free_eq.
      eassumption. eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      normalize_occurs_free.
      eapply Union_Included. now eauto with Ensembles_DB.
      
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply IHe; eassumption. reflexivity.
      rewrite !Setminus_Union_distr.
      eapply Union_Included; [|  now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_Union_preserv_l.
      eapply Included_Union_preserv_r. eapply image_monotonic.
      eapply Included_Setminus_compat. eapply project_vars_Funs_l. eassumption. 
      eapply Included_trans. eapply project_vars_Scope_l. eassumption.
      now eauto with Ensembles_DB.
    - inv H10.
      eapply Included_trans. eapply project_var_occurs_free_eq.
      eassumption.
      rewrite !occurs_free_Ecase_nil at 1...
    - inv H10. destruct y as [c'' e'].
      destruct H1 as [Heq [C' [e0' [Heq1 Hcc']]]]. simpl in *. subst. 
      normalize_occurs_free.
      
      eapply Included_trans. eapply occurs_free_Ecase_ctx_app.
      eapply Union_Included.
      + eapply Included_trans. eapply project_var_occurs_free_eq. eassumption. 
        eapply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Union_Included. now eauto with Ensembles_DB. 
        eapply Included_trans. eapply IHe. eassumption.

        eapply Union_Included; [| now eauto with Ensembles_DB ].
        eapply Union_Included. now eauto with Ensembles_DB.
        eapply Included_Union_preserv_l.
        eapply Included_Union_preserv_r. eapply image_monotonic.
        eapply Included_Setminus_compat. eapply project_var_Funs_l. eassumption. 
        eapply Included_trans. eapply project_var_Scope_l. eassumption.
        reflexivity.
      + eapply Included_trans. eapply IHe0. econstructor. eassumption.
        eassumption.
        now eauto with Ensembles_DB.
    - repeat normalize_occurs_free.
      eapply Included_trans. eapply project_var_occurs_free_eq.
      eassumption. eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      normalize_occurs_free.
      eapply Union_Included. now eauto with Ensembles_DB.
      
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply IHe; eassumption. reflexivity.
      rewrite !Setminus_Union_distr.
      eapply Union_Included; [|  now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_Union_preserv_l.
      eapply Included_Union_preserv_r. eapply image_monotonic.
      eapply Included_Setminus_compat. eapply project_var_Funs_l. eassumption. 
      eapply Included_trans. eapply project_var_Scope_l. eassumption.
      now eauto with Ensembles_DB.      
    - simpl. rewrite <- app_ctx_f_fuse.
      simpl. 
      eapply Included_trans. eapply project_vars_occurs_free_eq.
      eassumption. repeat normalize_occurs_free. rewrite <- !H1 at 1.
      repeat (eapply Union_Included; [|  now eauto with Ensembles_DB ]).
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Union_Included. now eauto with Ensembles_DB.
      rewrite !Setminus_Union_distr.  
      eapply Union_Included.

      eapply Setminus_Included_Included_Union. 
      eapply Included_trans. eapply Closure_conversion_occurs_free_fundefs_Included. eassumption.
      rewrite <- !closure_conversion_fundefs_Same_set with (B1 := f2) (B2 := B') at 1; [| eassumption ]...

      do 2 eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe; eassumption.
      rewrite <- !closure_conversion_fundefs_Same_set with (B1 := f2) (B2 := B') at 1; [| eassumption ].
      eapply Union_Included; [|  now eauto with Ensembles_DB ].
      eapply Union_Included.
      rewrite <- !Union_assoc. eapply Included_Union_preserv_r.
      rewrite (Union_commut). rewrite <- !Union_assoc. 
      do 3 eapply Included_Union_preserv_r.
      rewrite Union_Setminus_Included; tci; now eauto with Ensembles_DB.

      
      eapply Included_trans. eapply extend_fundefs'_image_Included'.
      eapply Union_Included. now eauto with Ensembles_DB.
      
      do 3 eapply Included_Union_preserv_l. 
      eapply Included_Union_preserv_r. 
      eapply image_monotonic. rewrite !Setminus_Union_distr.
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Setminus_Included_Included_Union.
      eapply Included_trans. eapply Setminus_Setminus_Included. tci. 
      eapply Included_Union_compat; [| reflexivity ].
      eapply Included_Setminus_compat. eapply project_vars_Funs_l. eassumption. 
      eapply Included_trans. eapply project_vars_Scope_l. eassumption.
      now eauto with Ensembles_DB.
    - eapply Included_trans.

      eapply project_vars_occurs_free_eq.
      eassumption. eapply Union_Included; [| now eauto with Ensembles_DB ].
      unfold AppClo; repeat normalize_occurs_free. normalize_sets.
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [ now eauto with Ensembles_DB |].
      eapply Union_Included; [ now eauto with Ensembles_DB |].
      rewrite Setminus_Union_distr. 
      eapply Union_Included; [ now eauto with Ensembles_DB |].
      normalize_sets. rewrite !Setminus_Union_distr. 
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ]...
    - repeat normalize_occurs_free.
      eapply Included_trans. eapply project_vars_occurs_free_eq.
      eassumption. eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included; [| now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      normalize_occurs_free.
      eapply Union_Included. now eauto with Ensembles_DB.
      
      eapply Included_trans. eapply Included_Setminus_compat.
      eapply IHe; eassumption. reflexivity.
      rewrite !Setminus_Union_distr.
      eapply Union_Included; [|  now eauto with Ensembles_DB ].
      eapply Union_Included. now eauto with Ensembles_DB.
      eapply Included_trans. eapply Setminus_Included.
      eapply Included_Union_preserv_l.
      eapply Included_Union_preserv_r. eapply image_monotonic.
      eapply Included_Setminus_compat. eapply project_vars_Funs_l. eassumption. 
      eapply Included_trans. eapply project_vars_Scope_l. eassumption.
      now eauto with Ensembles_DB.
    - repeat normalize_occurs_free.
      eapply Included_trans. eapply project_var_occurs_free_eq.
      eassumption. rewrite !occurs_free_Ehalt at 1...
  Qed. 

  (* TODO move *)
  Lemma Included_Intersection {A : Type} (s1 s2 s3 : Ensemble A) :
    s1 \subset s2 ->
    s1 \subset s3 ->
    s1 \subset s2 :&: s3. 
  Proof.
    now firstorder.
  Qed. 
  
  Corollary Closure_conversion_cc_fv_cor e Scope c Γ FVs e' C B 
            (Hcc : Closure_conversion clo_tag Scope (name_in_fundefs B)
                  (extend_fundefs' id B Γ) c Γ FVs e e' C) :
    ~ Γ \in Scope :|: (name_in_fundefs B) ->
    Disjoint _ (name_in_fundefs B) Scope ->
    occurs_free (C |[ e' ]|) \subset
    ((occurs_free e) :&: Scope) :|: ((occurs_free e) :&: (name_in_fundefs B \\ Scope)) :|: [set Γ].  
  Proof with (now eauto with Ensembles_DB).
    intros Hc Hdis. 
    assert (Hcc' := Hcc). eapply Closure_conversion_fv_sub in Hcc'. 
    assert (Hsub1 : occurs_free (C |[ e' ]|) \subset
                                occurs_free e :|: [set Γ]).
    { eapply Included_trans. eassumption.
      eapply Union_Included; [| now eauto with Ensembles_DB ]. 
      eapply Union_Included; [ now eauto with Ensembles_DB | ]. 
      eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
      eapply Included_trans. eapply extend_fundefs'_image. 
      now eauto with Ensembles_DB. }
    rewrite (Setminus_Disjoint _ Scope); [| eassumption ]. 
    eapply Closure_conversion_occurs_free_Included in Hcc.
    assert (Hsub2 : occurs_free (C |[ e' ]|) \subset
                                Scope :|: (name_in_fundefs B \\ Scope) :|: [set Γ]).  
    { eapply Included_trans. now apply Hcc.
      eapply Union_Included; [| now eauto with Ensembles_DB ]. 
      eapply Union_Included; [ now eauto with Ensembles_DB | ]. 
      eapply Included_trans. eapply image_monotonic. eapply Setminus_Included.
      eapply Included_trans. eapply extend_fundefs'_image. 
      now eauto with Ensembles_DB. }

    eapply Included_trans. eapply Included_Intersection. now eapply Hsub1. now eapply Hsub2.
    rewrite <- Union_Intersection_distr. eapply Included_Union_compat; [| reflexivity ].
    rewrite Intersection_commut. rewrite Intersection_Union_distr. eapply Included_Union_compat. 
    rewrite !(Intersection_commut _ (occurs_free e)). reflexivity.
    
    rewrite Intersection_commut. eapply Included_Intersection_compat...
  Qed.

 Lemma Closure_conversion_closed_fundefs_mut :
   (forall e Scope Funs fenv c Γ FVs e' C 
      (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C),
      closed_fundefs_in_exp (C |[ e' ]|)) /\
   (forall B Funs c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs c FVs B B'),
       closed_fundefs_in_fundefs B').
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; eassumption.
    - inv H10. 
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H3.
    - inv H10. destruct H1 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
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
      simpl in HB. inv HB. inv H6.
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

  
  Lemma project_var_FV_eq Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    FV Scope Funs FVs <--> FV Scope' Funs' FVs.
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    - reflexivity.
    - rewrite !(Union_commut [set x] Scope) at 2.
      rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
      rewrite Setminus_Union.
      rewrite (Union_Same_set [set x] (Scope :|: [set x])); eauto with Ensembles_DB typeclass_instances.
      rewrite <- (Setminus_Union Funs ). 
      rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
      
      rewrite <- (Union_assoc Scope [set x] Funs).
      rewrite (Union_Same_set [set x]  Funs); eauto with Ensembles_DB typeclass_instances.

      rewrite (Union_commut [set x]). rewrite <- (Union_assoc _ [set x] (Funs \\ Scope)).
      rewrite (Union_Same_set [set x] (Funs \\ Scope)); eauto with Ensembles_DB typeclass_instances.
    - rewrite !(Union_commut [set x] Scope) at 2.
      rewrite <- (Union_assoc Scope [set x] Funs').
      rewrite !(Union_commut [set x] Funs') at 1.
      rewrite (Union_assoc Scope Funs' [set x]).
      rewrite <- (Setminus_Union (FromList FVs) (Scope :|: Funs')).
      rewrite (Union_Setminus_Included _ _ [set x]);
        eauto with Ensembles_DB typeclass_instances.
      rewrite <- (Setminus_Union Funs' ). 
      rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.

      rewrite <- !(Union_assoc [set x]).
      rewrite (Union_Same_set [set x] _). reflexivity.
      eapply Singleton_Included. right. 
      constructor; eauto.
      eapply nthN_In. eassumption.
      intros Hc; inv Hc; eauto. 
  Qed.

  Lemma project_vars_FV_eq Scope Scope' Funs Funs' fenv c Γ FVs xs C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    FV Scope Funs FVs <--> FV Scope' Funs' FVs.
  Proof.
    intros Hvar. induction Hvar; eauto.
    - reflexivity.
    - rewrite project_var_FV_eq; [| eassumption ]. eassumption.
  Qed.

  
  Lemma project_var_In_Union Scope Scope' Funs Funs' fenv c Γ FVs x C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    x \in (FV Scope Funs FVs).
  Proof.
    unfold FV. intros Hvar. inv Hvar; eauto.
    - left. right. constructor; eauto. 
    - right. constructor; eauto. eapply nthN_In. eassumption.
      intros Hc; inv Hc; eauto. 
  Qed.
  
  Lemma project_vars_In_Union Scope Funs c Γ FVs xs C Scope' Funs' fenv:
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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
    (forall e Scope Funs fenv c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C),
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
        eapply Included_trans.
        eapply FV_Union1. rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
        rewrite <- project_vars_FV_eq; [| eassumption ]...
    - normalize_occurs_free. eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - normalize_occurs_free. eapply Union_Included.
      + eapply Singleton_Included.
        eapply project_var_In_Union. eassumption.
      + inv H10. simpl in H1. destruct H1 as (Heq & C' & e' & Heq' & Hcc).
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
        rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
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
        eapply Included_trans.
        eapply FV_Union1. rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ].
        rewrite <- project_vars_FV_eq; [| eassumption ]...
    - rewrite occurs_free_Ehalt.
      eapply Singleton_Included.
      eapply project_var_In_Union. eassumption.
    - rewrite HD; eauto. reflexivity.
    - normalize_occurs_free...
  Qed.
  
  Corollary Closure_conversion_pre_occurs_free_Included :
    (forall e Scope Funs fenv c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C),
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
  
  Corollary Closure_conversion_fv_cor e Scope c Γ FVs e' C Funs fenv 
            (Hcc : Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C) :
    occurs_free e <-->
    ((occurs_free e) :&: Scope) :|: ((occurs_free e) :&: (Funs \\ Scope)) :|:
    ((occurs_free e) :&: (FromList FVs \\ (Scope :|: Funs))).  
  Proof with (now eauto with Ensembles_DB).
    eapply Closure_conversion_pre_occurs_free_Included in Hcc.  
    rewrite <- (Intersection_Same_set (occurs_free e) (FV Scope Funs FVs)) at 1; [| eassumption ].
    unfold FV. 

    rewrite Intersection_commut. rewrite !Intersection_Union_distr.
    rewrite !(Intersection_commut (occurs_free e)). reflexivity.
  Qed.
    

    
  Lemma Closure_conversion_fundefs_numOf_fundefs Funs (c : cTag) 
        (FVs : list var) (B1 B2 : fundefs) :
    Closure_conversion_fundefs clo_tag Funs c FVs B1 B2 ->
    numOf_fundefs B1 = numOf_fundefs B2.
  Proof.
    intros Hcc; induction Hcc; eauto; simpl. congruence.
  Qed.

  Lemma project_var_get Scope Scope' Funs Funs' fenv c Γ FVs x C1 rho1 H1 rho2 H2 m y:
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
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
  
  Lemma project_vars_get Scope Scope' Funs Funs' fenv c Γ FVs xs C1 rho1 H1 rho2 H2 m y:
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
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
  
  Lemma project_var_getlist Scope Scope' Funs Funs' fenv c Γ FVs x C1 rho1 H1 rho2 H2 m ys :
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
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
  

  Lemma project_vars_getlist Scope Scope' Funs Funs' fenv c Γ FVs xs C1 rho1 H1 rho2 H2 m ys :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs'->
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
  Lemma project_var_env_locs Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m e :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
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
  
  Lemma project_var_env_locs' Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs fenv Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs fenv Γ) \subset dom H1 ->
    env_locs rho2 (FV_cc Scope' Funs' fenv Γ) \subset dom H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf.
    assert (Hsub := project_var_FV_cc _ _ _ _ _ _ _ _ _ _ Hvar).  inv Hvar; inv Hctx.
    - eassumption.
    - inv H15.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      rewrite HL.alloc_dom; [| eassumption ].
      eapply Included_Union_compat. reflexivity.
      eapply Included_trans. eapply env_locs_monotonic.
      eapply Setminus_Included_Included_Union.
      erewrite (Union_commut _ [set x]). eassumption.
      eassumption.
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
        eapply Included_trans.
        eapply Included_Setminus_compat.
        eapply FV_cc_Union1. reflexivity.
        now eauto 20 with Ensembles_DB.
  Qed.
  
  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m e :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
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
        destruct (M.get (fenv x) rho1) as [v2 |] eqn:Hget2; try congruence. 
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
  Lemma project_var_well_formed' Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    (env_locs rho1 (FV_cc Scope Funs fenv Γ)) \subset dom H1 ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs fenv Γ))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope' Funs' fenv Γ))) H2.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf.
    assert (Hsub := project_var_FV_cc _ _ _ _ _ _ _ _ _ _ Hvar). 
    inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H15.
      eapply well_formed_antimon; [| eapply well_formed_reach_alloc; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Included_trans. eassumption. simpl...
      + simpl. simpl in H13.
        destruct (M.get x rho1) as [v1 |] eqn:Hget1; try congruence. 
        destruct (M.get (fenv x) rho1) as [v2 |] eqn:Hget2; try congruence. 
        inv H13. 
        eapply Included_trans; [| eapply reach'_extensive ].
        simpl. eapply Union_Included. eapply get_In_env_locs; [| eassumption ].
        left; left; right. now constructor; eauto.
        rewrite Union_Empty_set_neut_r.
        eapply get_In_env_locs; [| eassumption ]. left; right.
        eapply In_image. now constructor; eauto.
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
  
  Lemma project_var_env_locs_subset Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m S1 :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
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
  
  Lemma project_vars_env_locs_subset Scope Scope' Funs Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m S1 :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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

  Lemma project_var_subheap Scope Scope' Funs Funs' fenv c Γ FVs x C rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    H1 ⊑ H2. 
  Proof.
    intros Hvar Hctx; inv Hvar; inv Hctx; eauto.
    now apply HL.subheap_refl. 
    inv H15. now eapply HL.alloc_subheap; eauto.
    inv H18. now apply HL.subheap_refl. 
  Qed.
  
  Lemma project_vars_subheap Scope Scope' Funs  Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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

  Lemma project_vars_env_locs Scope Scope' Funs  Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m e :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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
  
  Lemma project_vars_env_locs' Scope Scope' Funs Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs fenv Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs fenv Γ) \subset dom H1 ->
    env_locs rho2 (FV_cc Scope' Funs' fenv Γ) \subset dom H2.
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
  
  Lemma project_vars_well_formed Scope Scope' Funs Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m e :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
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
  
  Lemma project_vars_well_formed' Scope Scope' Funs Funs' fenv c Γ FVs xs C rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    ctx_to_heap_env_CC C H1 rho1 H2 rho2 m ->
    well_formed (reach' H1 (env_locs rho1 (FV_cc Scope Funs fenv Γ))) H1 ->
    env_locs rho1 (FV_cc Scope Funs fenv Γ) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope' Funs' fenv Γ))) H2.
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

  Lemma project_var_binding_in_map Scope Scope' Funs Funs' fenv c Γ FVs x C1 rho1 H1 rho2 H2 m :
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    binding_in_map Scope rho1 ->
    binding_in_map Scope' rho2. 
  Proof with (now eauto with Ensembles_DB).
    intros Hvar Hctx Hnin. inv Hvar; inv Hctx; eauto.
    - inv H15.
      eapply binding_in_map_antimon;
        [| eapply binding_in_map_set; eassumption ]...
    - inv H18; eauto. 
      eapply binding_in_map_antimon;
        [| eapply binding_in_map_set; eassumption ]...
  Qed.

  Lemma project_vars_binding_in_map Scope Scope' Funs Funs' fenv c Γ FVs xs C1 rho1 H1 rho2 H2 m :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    binding_in_map Scope rho1 ->
    binding_in_map Scope' rho2. 
  Proof.
    intros Hvar; revert rho1 H1 rho2 H2 m; induction Hvar; intros rho1 H1 rho2 H2 m Hctx Hbin. 
    - inv Hctx. eassumption.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho'' [H'' [m1 [m2  [Hctx1 [Hctx2 Hadd]]]]]]; eauto.
      subst. eapply IHHvar. eassumption.
      eapply project_var_binding_in_map; eassumption.
  Qed.

  Instance Proper_binding_in_map (A : Type) : Proper (Same_set _ ==> eq ==> iff) (@binding_in_map A). 
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; split; intros Hbin x Hin;
    eapply Hbin; eapply Hseq; eauto.
  Qed.


  Lemma Closure_conversion_fundefs_find_def B1' B1 B2 c FVs f e1 ft xs:
      Closure_conversion_fundefs clo_tag B1' c FVs B1 B2 ->
      find_def f B1 = Some (ft, xs, e1) ->
      exists Γ e2 C,
        find_def f B2 = Some (ft, Γ :: xs, C |[ e2 ]|) /\
        ~ Γ \in (name_in_fundefs B1':|: FromList xs :|: bound_var e1
                                 :|: FromList FVs) /\
        Closure_conversion clo_tag (FromList xs) (name_in_fundefs B1')
                           (extend_fundefs' id B1' Γ) c Γ FVs e1 e2 C.
  Proof.
    intros Hc Hdef; induction Hc.
    - simpl in Hdef.
      destruct (M.elt_eq f f0); subst.
      + inv Hdef. do 3 eexists. split; [| split ].
        * simpl. rewrite Coqlib.peq_true. reflexivity.
        * intros Hc'. eapply H. constructor; eauto. 
        * eassumption.
      + edestruct IHHc as (Γ & e2 & C'  & Hfind & Hclo).
        * eassumption.
        * do 3 eexists. split.
          simpl. rewrite Coqlib.peq_false; now eauto. eassumption.
    - inv Hdef.
  Qed.

  Lemma project_var_Scope_Funs_eq Scope Scope' Funs Funs'
        fenv c Γ FVs xs C1 :
    project_var clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs' <--> Funs \\ (Scope' \\ Scope).
  Proof.
    intros hvar; inv hvar; eauto.
    - rewrite Setminus_Same_set_Empty_set, Setminus_Empty_set_neut_r. reflexivity.
    - rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope). reflexivity.
      eapply Disjoint_Singleton_l. eassumption.
    - rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope).
      rewrite (Setminus_Disjoint Funs').
      reflexivity.
      eapply Disjoint_Singleton_r. eassumption.
      eapply Disjoint_Singleton_l. eassumption.
  Qed.

  Lemma project_var_size_ps_cardinal Scope Funs {Hf : ToMSet Funs} Scope' Funs' {Hf' : ToMSet Funs'}
        fenv c x FVs Γ C :
    project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    PS.cardinal (@mset Funs Hf)  =
    PS.cardinal (@mset Funs' Hf') + PS.cardinal (@mset (Funs \\ Funs') _).
  Proof.
    intros Hvar. assert (Hvar' := Hvar). 
    rewrite PS_cardinal_union. 
    eapply Proper_carinal. eapply Same_set_From_set.
    rewrite FromSet_union.
    do 3 setoid_rewrite <- mset_eq at 1.
    eapply project_var_Scope_Funs_eq in Hvar.
    eapply Union_Setminus_Same_set. now tci.
    eapply project_var_Funs_l. eassumption.
    eapply FromSet_disjoint.
    do 2 setoid_rewrite <- mset_eq at 1.
    eapply Disjoint_Setminus_r. reflexivity. 
  Qed.

  Lemma project_vars_size_ps_cardinal Scope Funs {Hf : ToMSet Funs} Scope' Funs' {Hf' : ToMSet Funs'}
        fenv c xs FVs Γ C :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    PS.cardinal (@mset Funs Hf)  =
    PS.cardinal (@mset Funs' Hf') + PS.cardinal (@mset (Funs \\ Funs') _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvars. induction Hvars.
    - rewrite PS_cardinal_union. 
      eapply Proper_carinal. eapply Same_set_From_set.
      rewrite FromSet_union.
      do 3 setoid_rewrite <- mset_eq at 1.
      rewrite Setminus_Same_set_Empty_set...
      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_r. reflexivity. 
    - rewrite PS_cardinal_union. 
      eapply Proper_carinal. eapply Same_set_From_set.
      rewrite FromSet_union.
      do 3 setoid_rewrite <- mset_eq at 1.
      rewrite <- Union_Setminus_Same_set. reflexivity.
      now tci.
      eapply Included_trans.

      eapply project_vars_Funs_l. eassumption.
      eapply project_var_Funs_l. eassumption.

      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_r. reflexivity. 
  Qed.

  Lemma project_vars_ToMSet (Scope1 : Ensemble positive) (Scope2 : Ensemble var)
        { Hs : ToMSet Scope1 } (Funs1 Funs2 : Ensemble var) (fenv : var -> var) 
        (c : cTag) (Γ : var) (FVs : list var) (ys : list var) 
        (C1 : exp_ctx) :
    project_vars clo_tag Scope1 Funs1 fenv c Γ FVs ys C1 Scope2 Funs2 -> ToMSet Scope2.
  Proof.
  Admitted.

  Lemma project_vars_ToMSet_Funs (Scope1 : Ensemble positive) (Scope2 : Ensemble var)
        (Funs1 Funs2 : Ensemble var)  { Hf : ToMSet Funs1 } (fenv : var -> var) 
        (c : cTag) (Γ : var) (FVs : list var) (ys : list var) 
        (C1 : exp_ctx) :
    project_vars clo_tag Scope1 Funs1 fenv c Γ FVs ys C1 Scope2 Funs2 -> ToMSet Funs2.
  Proof.
  Admitted.

    Lemma project_var_Setminus_eq (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (xs : var) (C1 : exp_ctx) :
    project_var clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs' \\ Scope' \subset Funs \\ Scope.
  Proof.
    intros Hv. assert (Hv' := Hv). 
    eapply project_var_Scope_Funs_eq in Hv. rewrite Hv.
    rewrite Setminus_Union.
    eapply Included_Setminus_compat. reflexivity.
    eapply Included_trans. eapply project_var_Scope_l. eassumption. 
    now eauto with Ensembles_DB.
  Qed.

  Lemma project_vars_Setminus_eq (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (xs : list var) (C1 : exp_ctx) :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs' \\ Scope' \subset Funs \\ Scope.
  Proof.
    intros Hv. assert (Hv' := Hv). 
    eapply Included_Setminus_compat.
    eapply project_vars_Funs_l. eassumption. 
    eapply project_vars_Scope_l. eassumption. 
  Qed.


  Lemma project_var_cost_eq'
        Scope Scope'  Funs Funs' fenv
        c Γ FVs x C1 :
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    cost_ctx_full C1 <= 3.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; inv Hvar; eauto.
  Qed.

  Lemma project_vars_cost_eq'
        Scope Scope'  Funs Funs' fenv
        c Γ FVs xs C1 :
    project_vars clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    cost_ctx_full C1 <= 3 * length xs.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    rewrite cost_ctx_full_ctx_comp_ctx_f. simpl.
    eapply le_trans. eapply plus_le_compat.
    eapply project_var_cost_eq'. eassumption. eassumption.
    omega.
  Qed.

  Lemma binding_in_map_def_closures (S : Ensemble M.elt) (rho1 rho1' : env) H1 H1' B1 B1' v :
    binding_in_map S rho1 ->
    def_closures B1 B1' rho1 H1 v = (H1', rho1') ->
    binding_in_map (name_in_fundefs B1 :|: S) rho1'.
  Proof. 
    revert H1' rho1'. induction B1; intros H2 rho2 Hbin Hclo.
    - simpl in *.
      destruct (def_closures B1 B1' rho1 H1 v) as [H' rho'] eqn:Hd.
      destruct (alloc (Clos (FunPtr B1' v0) v) H')as [l' H''] eqn:Ha. 
      inv Hclo.
      rewrite <- Union_assoc. rewrite Union_commut. eapply binding_in_map_set.
      eauto.
    - inv Hclo. simpl. eapply binding_in_map_antimon; [| eassumption ].
      eauto with Ensembles_DB.
  Qed.

  Lemma restrict_env_getlist S rho rho' xs vs :
    Restrict_env S rho rho' -> 
    getlist xs rho = Some vs -> 
    FromList xs \subset S ->
    getlist xs rho' = Some vs. 
  Proof with (now eauto with Ensembles_DB).
    revert vs. induction xs; intros vs HR Hget Hin.
    - inv Hget. reflexivity.
    - simpl in Hget.
      destruct (M.get a rho) eqn:Hgeta; try congruence.
      destruct (getlist xs rho) eqn:Hgetxs; try congruence.
      inv Hget. normalize_sets.
      assert (HR' := HR). 
      simpl. destruct HR as [Heq _].
      rewrite <- Heq, Hgeta; eauto.
      erewrite IHxs; eauto. eapply Included_trans; [| eassumption ]...
  Qed.

  Lemma project_var_env_locs_dis (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (x : var) (C1 : exp_ctx) (rho1 : env) (H1 : heap block) 
        (rho2 : env) (H2 : heap block) (m : nat) S :
    project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S (Scope' \\ Scope) ->
    env_locs rho1 S <--> env_locs rho2 S.
  Admitted.

  Lemma project_vars_env_locs_dis (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (x : list var) (C1 : exp_ctx) (rho1 : env) (H1 : heap block) 
        (rho2 : env) (H2 : heap block) (m : nat) S :
    project_vars clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S (Scope' \\ Scope) ->
    env_locs rho1 S <--> env_locs rho2 S.
  Admitted.  
       
End CCUtil. 