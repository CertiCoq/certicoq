(* Correctness proof for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.cps L6.cps_util L6.set_util L6.hoisting L6.identifiers L6.ctx L6.Ensembles_util
        L6.List_util L6.functions L6.closure_conversion L6.eval L6.logical_relations.
Require Import Libraries.Coqlib.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(** For closure conversion, the free variables of an expression are divided in
    three categories :

    1. Variables in the current scope, i.e. arguments of the current function
    and bindings in the body of the current function definition.

    2. Names of the functions that are defined in the current block of mutually
    recursive functions.

    3. Free variables, i.e. variables that are not declared outside of the
    body of the current function but in outer definitions

    In the proof maintains different invariants for each kind of variable *)


(** * Invariants *)

(** Naming conventions in the following :

    [Scope] : The set of variables in the current scope.

    [Funs] : The set of variables in the current block of mutually recursive
    functions.

    [FVs] : The list of free variables (needs to be ordered).

    [Γ] : The formal parameter of the environment after closure conversion. *)


Section Closure_conversion_correct.

  Variable pr : prims.
  Variable cenv : cEnv.
  Variable clo_tag : cTag.


  (** ** Proof that after closure conversion all functions are closed *)

  Lemma project_var_occurs_free_ctx_Included Scope Funs σ c Γ FVs S x x' C S' F e:
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    Included _ (occurs_free e) (Union _ F (Singleton _ x')) ->
    Included _ (Union _ Scope
                      (Union _ (image σ Funs) (Singleton _ Γ))) F ->
    Included _ (occurs_free (C |[ e ]|)) F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hproj Hinc1 Hinc2. inv Hproj.
    - simpl. eapply Included_trans. eassumption. 
      apply Union_Included. now apply Included_refl.
      eapply Included_trans; [| eassumption ].
      eauto with Ensembles_DB.
    - simpl.
      rewrite occurs_free_Econstr, !FromList_cons, FromList_nil,
      Union_Empty_set_neut_r.
      eapply Union_Included.
      + eapply Included_trans; [| now apply Hinc2 ]...
      + eauto with Ensembles_DB.
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
  
  Lemma project_vars_occurs_free_ctx_Included Scope Funs σ c Γ
    FVs S xs xs' C S' F e:
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Included _ (occurs_free e)  (Union _ F (FromList xs')) ->
    Included _ (Union _ Scope
                      (Union _ (image σ Funs) (Singleton _ Γ))) F ->
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

  Lemma make_closures_occurs_free_ctx_Included B S Γ C σ S' F e:
    unique_functions B ->
    make_closures clo_tag B S Γ C σ S'  ->
    Included _ (occurs_free e) (Union _ F (name_in_fundefs B)) ->
    Included _ (Union _ (image σ (name_in_fundefs B)) (Singleton _ Γ)) F ->
    Included _ (occurs_free (C |[ e ]|)) F. 
  Proof with now eauto with Ensembles_DB functions_BD. 
    intros Hun Hmc. revert F.
    induction Hmc; intros F Hinc1 Hinc2;
    simpl in *; repeat normalize_sets; (repeat normalize_occurs_free).
    - eassumption.
    - repeat normalize_sets.
      apply Union_Included. apply Union_Included.
      eapply Included_trans; [| eassumption ].
      rewrite <- (extend_gss g f f'), H0...
      eapply Included_trans; [| eassumption ]...
      eapply Setminus_Included_Included_Union.
      inv Hun. eapply IHHmc.
      eassumption.
      eapply Included_trans; [ eassumption |]...
      eapply Included_Union_preserv_l.
      eapply Included_trans; [| eassumption ].
      apply Included_Union_compat; [| now apply Included_refl ].
      rewrite <- H0...
  Qed.

  Lemma project_var_free_funs_in_exp Scope Funs σ c Γ FVs S x x' C S' B e:
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; inv Hvar; [ split; now eauto | |];
    (split; intros Hf; [ now inv Hf | now constructor ]).
  Qed.

  Lemma project_vars_free_funs_in_exp Scope Funs σ c Γ FVs S xs xs' C S' B e:
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    (funs_in_exp B (C |[ e ]|) <-> funs_in_exp B e).
  Proof. 
    intros Hvar; induction Hvar; [ now eauto |].
    rewrite <- app_ctx_f_fuse, project_var_free_funs_in_exp; eassumption.
  Qed.

  Lemma make_closures_funs_in_exp B S Γ C σ S' B' e:
    make_closures clo_tag B S Γ C σ S'  ->
    (funs_in_exp B' (C |[ e ]|) <-> funs_in_exp B' e).
  Proof.
    intros Hmc; induction Hmc;
    [ split; now eauto | ].
    rewrite <- IHHmc. split; eauto; intros Hf; [ now inv Hf | now constructor ].
  Qed.

  Lemma closure_conversion_fundefs_Same_set_image σ c Funs FVs B1 B2  :
    Closure_conversion_fundefs clo_tag Funs σ c FVs B1 B2 ->
    Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2).
  Proof. 
    intros Hcc. induction Hcc.  
    - simpl. rewrite image_Union, image_Singleton, IHHcc.
      apply Same_set_refl.
    - simpl. rewrite image_Empty_set. apply Same_set_refl.
  Qed.
  
  Lemma Closure_conversion_occurs_free_Included_mut :
    (forall e Scope Funs σ c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       Included _ (occurs_free (C |[ e' ]|))
                (Union _ Scope (Union _ (image σ Funs) (Singleton _ Γ)))) /\
    (forall B Funs σ c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
       Included _ (occurs_free_fundefs B') (Setminus _ (image σ Funs) (name_in_fundefs B'))).
  Proof with now eauto with Ensembles_DB functions_BD.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Econstr.
      apply Union_Included. now eauto with Ensembles_DB.
      apply Setminus_Included_Included_Union.
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor.
      rewrite Union_commut with (s2 := Singleton var v), !Union_assoc.
      now apply Included_Union_l.
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ]. inv H11.
      rewrite occurs_free_Ecase_nil. now apply Included_Union_r.
    - inv H11. destruct y as [c' e'].
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
      eauto with Ensembles_DB. 
    - rewrite <- app_ctx_f_fuse.
      eapply project_vars_occurs_free_ctx_Included;
        [ eassumption | | now apply Included_refl ].
      simpl. rewrite occurs_free_Econstr.
      apply Union_Included. now apply Included_Union_r.
      rewrite occurs_free_Efun. apply Setminus_Included_Included_Union.
      eapply Union_Included.
      eapply Included_trans. eapply IHB. eassumption.
      intros f Hunf. eapply Hun. now inv Hunf; eauto.
      rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ]...
      eapply Setminus_Included_Included_Union.
      eapply make_closures_occurs_free_ctx_Included; [| eassumption | | ].
      eapply Hun. now constructor.
      eapply Included_trans. eapply IHe. eassumption.
      intros f Hunf. eapply Hun. now constructor. 
      now eauto 15 with Ensembles_DB.
       rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ]...
    - eapply project_vars_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      repeat normalize_occurs_free. repeat normalize_sets.
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
      eauto 7 with Ensembles_DB.
    - eapply project_var_occurs_free_ctx_Included;
      [ eassumption | | now apply Included_refl ].
      rewrite occurs_free_Ehalt...
    - rewrite occurs_free_fundefs_Fcons.
      apply Union_Included.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHe. eassumption.
        intros f Hunf. eapply Hun. left. now eauto.
        rewrite FromList_cons. simpl.
        rewrite <- Union_Included_Union_Setminus;
          eauto 6 with Ensembles_DB typeclass_instances.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans. eapply IHB. eassumption.
        intros f Hunf. inv Hunf; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)).
        now inv Hun; eauto.
        simpl. eapply Setminus_Included_Included_Union.
        rewrite <- Union_assoc, <- Union_Included_Union_Setminus;
          eauto with Ensembles_DB typeclass_instances.
    - rewrite occurs_free_fundefs_Fnil. now apply Included_Empty_set.
  Qed.

  Lemma Closure_conversion_closed_fundefs_mut :
    (forall e Scope Funs σ c Γ FVs e' C 
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hun: fundefs_names_unique e),
       closed_fundefs_in_exp (C |[ e' ]|)) /\
    (forall B Funs σ c FVs B'
       (Hcc: Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hun: fundefs_names_unique_fundefs B),
       closed_fundefs_in_fundefs B').
  Proof.
    exp_defs_induction IHe IHl IHB; intros; inv Hcc.
    - intros B HB. rewrite project_vars_free_funs_in_exp in HB; [| eassumption ].
      inv HB. eapply IHe; [ eassumption | | eassumption ]. 
      intros B' H. eapply Hun. now constructor. 
    - inv H11. 
      intros B HB. rewrite project_var_free_funs_in_exp in HB; [| eassumption ].
      inv HB. inv H4.
    - inv H11. destruct H2 as [Heq [C' [e' [Heq' Hcc']]]]. destruct y as [t e''].
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
      inv HB. inv H8.
      + split; [| now apply Included_Empty_set ].
        eapply Included_trans.
        eapply Closure_conversion_occurs_free_Included_mut. eassumption.
        intros B HB. eapply Hun. inv HB; eauto.
        rewrite closure_conversion_fundefs_Same_set_image; [| eassumption ].
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
      + eapply IHe; [ eassumption | | eassumption ].  
        intros B' H. eapply Hun. left. now constructor. 
      + eapply IHB; [ eassumption | | eassumption ].
        intros B' H. inv H; eauto.
        specialize (Hun (Fcons v t l e f5) (or_intror eq_refl)). now inv Hun; eauto.
    - intros B HB. inv HB.
  Qed.

  (** ** Semantics preservation proof *)

  (** Invariant about the values of free variables. *)
  Definition closure_env k rho Scope Funs vs FVs : Prop :=
    forall (x : var) N (v : val),
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      M.get x rho = Some v ->
      exists (v' : val),  nthN vs N = Some v' /\
                     cc_approx_val pr cenv clo_tag k v v'.
  
  (** Invariant about the free variables *) 
  Definition FV_inv k rho rho' Scope Funs c Γ FVs : Prop :=
    forall (x : var) N (v : val),
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      M.get x rho = Some v ->
      exists (vs : list val) (v' : val),
        M.get Γ rho' = Some (Vconstr c vs) /\
        nthN vs N = Some v' /\
        cc_approx_val pr cenv clo_tag k v v'.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv k (rho rho' : env) Scope Funs σ c Γ : Prop :=
    forall f v,
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho = Some v  ->
      exists vs rho1 B1 f1 rho2 B2 f2,
        M.get Γ rho' = Some (Vconstr c vs) /\
        v = (Vfun rho1 B1 f1) /\
        ~ In _ Scope (σ f) /\
        M.get (σ f) rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val pr cenv clo_tag k (Vfun rho1 B1 f1)
                      (Vconstr clo_tag [(Vfun rho2 B2 f2) ; (Vconstr c vs)]).
  

  (** * Lemmas about Fun_inv *)

  (** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
  Lemma Fun_inv_set k rho rho' Scope Funs σ c Γ f rho1 B1 f1 rho2 B2 f2 vs:
    Fun_inv k rho rho' Scope Funs σ c Γ ->
    (σ f) <> Γ ->
    ~ In _ Scope (σ f) ->
    ~ In _ (image σ (Setminus _ Funs Scope)) (σ f) ->
    M.get Γ rho' = Some (Vconstr c vs) ->
    (cc_approx_val pr cenv clo_tag k (Vfun rho1 B1 f1)
                   (Vconstr clo_tag [(Vfun rho2 B2 f2) ; (Vconstr c vs)])) ->
    Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
            (M.set (σ f) (Vfun rho2 B2 f2) rho')
            Scope (Union _ (Singleton _ f) Funs) σ c Γ.
  Proof.
    intros Hinv Hneq Hnin Hnin' Hget Hv f'' v Hnin'' Hin Hget'.
    destruct (peq f'' f); subst.
    - repeat eexists; eauto. rewrite M.gso; eauto.
      now rewrite M.gss in Hget'; inv Hget'; eauto.
      now rewrite M.gss.
    - inv Hin. inv H; congruence. rewrite M.gso in Hget'; eauto.
      edestruct Hinv with (f := f'') as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
        subst; eauto.
      repeat eexists; eauto. rewrite M.gso; now eauto. 
      rewrite M.gso. now eauto.
      intros Hc. eapply Hnin'. eexists; eauto. split; [| eassumption ].
      now constructor; eauto.
  Qed.

  (** Rename the environment parameter *)
  Lemma Fun_inv_rename k rho1 rho2 Scope Funs σ c Γ Γ' v :
    ~ In _ (image σ (Setminus _ Funs Scope)) Γ ->  ~ In _ (image σ Funs) Γ' ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ c Γ ->
    Fun_inv k rho1 (M.set Γ' v rho2) Scope Funs σ c Γ'.
  Proof.
    intros Hnin Hnin' Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite M.gss in Hget1. inv Hget1.
    repeat eexists; eauto. now rewrite M.gss; eauto.
    rewrite M.gso in Hget2. rewrite M.gso; eauto.
    intros Hc. eapply Hnin'. now eexists; split; eauto.
    intros Hc. eapply Hnin. now eexists; split; eauto.
  Qed.
  
  (** Extend [Scope] with a set that does not shadow the new function names *)
  Lemma Fun_inv_mon k rho1 rho2 Scope Scope' Funs σ c Γ :
    Disjoint _ (image σ (Setminus _ Funs Scope)) Scope' ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    Fun_inv k rho1 rho2 (Union _ Scope' Scope) Funs σ c Γ.
  Proof.
    intros Hd Hinv f v Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    intros Hc; inv Hc. eapply Hd. constructor; eauto. 
    eexists; eauto. split; [| now eauto ]. now constructor; eauto.
    now eauto.
  Qed.

  (** Extend the first environment with a variable in [Scope] *)
  Lemma Fun_inv_set_In_Scope_l k rho1 rho2 Scope Funs σ c Γ x v :
    In _ Scope x ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    Fun_inv k (M.set x v rho1) rho2 Scope Funs σ c Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.
  
  (** Extend the second environment with a variable in [Scope] *)
  Lemma Fun_inv_set_In_Scope_r k rho1 rho2 Scope Funs σ c Γ x v v' :
    In _ Scope x ->  ~ In _ (image σ (Setminus _ Funs Scope)) x ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ c Γ ->
    Fun_inv k rho1 (M.set Γ v (M.set x v' rho2)) Scope Funs σ c Γ.
  Proof.
    intros Hin Hnin Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite M.gss in Hget1; inv Hget1. 
    repeat eexists; eauto. now rewrite M.gss.
    destruct (peq (σ f) Γ).
    - subst. now rewrite M.gss in *.
    - rewrite M.gso; eauto. rewrite M.gso in Hget2; eauto.
      rewrite M.gso; eauto.
      intros Hc; subst. eapply Hnin. eexists; eauto.
      split; [| now eauto]. constructor; eauto.
  Qed.

  (** Extend the second environment with a variable in [Scope] that is different
    from [Γ] *)
  Lemma Fun_inv_set_In_Scope_r_not_Γ k rho1 rho2 Scope Funs σ c Γ x v :
    In _ Scope x -> Γ <> x ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs σ c Γ.
  Proof.
    intros Hin Hnin Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    now rewrite M.gso.
    rewrite M.gso. now eauto.
    intros Hc. subst. contradiction.
  Qed.  

  (** Extend the second environment with a variable not in [Funs] that is different
    from Γ *)
  Lemma Fun_inv_set_not_In_Funs_r_not_Γ k rho1 rho2 Scope Funs σ c Γ x v :
    ~ In _ (image σ (Setminus _ Funs Scope)) x ->
    x <> Γ -> 
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs σ c Γ.
  Proof.
    intros Hnin Hneq Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite M.gso. now eauto.
    intros Hc. subst. congruence.
    rewrite M.gso. now eauto.
    intros Hc. subst. eapply Hnin.
    now eexists; eauto.
  Qed.

  (** Extend the first environment with a list of variables in [Scope] *)
  Lemma Fun_inv_setlist_In_Scope_l k rho1 rho1' rho2 Scope Funs σ c Γ xs vs :
    Included _ (FromList xs) Scope ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    setlist xs vs rho1 = Some rho1' ->
    Fun_inv k rho1' rho2 Scope Funs σ c Γ.
  Proof.
    revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
    - intros Hinc Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (setlist xs vs rho1) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply Fun_inv_set_In_Scope_l.
      + rewrite FromList_cons in Hinc. 
        eapply Hinc. eauto.
      + eapply IHxs; eauto.
        rewrite FromList_cons in Hinc. 
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_r.
  Qed.

  (** Extend the second environment with a list of variables in [Scope] *)
  Lemma Fun_inv_setlist_In_Scope_r k rho1 rho2 rho2' Scope Funs σ c Γ xs vs v :
    Included _ (FromList xs) Scope ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (FromList xs) ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ c Γ ->
    setlist xs vs rho2 = Some rho2' ->
    Fun_inv k rho1 (M.set Γ v rho2') Scope Funs σ c Γ.
  Proof.
    revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
    - intros Hinc Hd Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hd Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (setlist xs vs rho2) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply Fun_inv_set_In_Scope_r.
      + rewrite FromList_cons in Hinc. 
        eapply Hinc. eauto.
      + intros Hin. eapply Hd. constructor; eauto.
        rewrite FromList_cons. eauto.
      + rewrite FromList_cons in Hinc, Hd. eapply IHxs; eauto.      
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_r.
        eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_Union_r.
  Qed.

  (** Redefine the environment argument in the second environment *)
  Lemma Fun_inv_reset k rho rho' B v Scope Funs σ c Γ :
    ~ In _ (name_in_fundefs B) Γ ->
    Fun_inv k rho
            (def_funs B B (M.set Γ v rho') (M.set Γ v rho')) Scope Funs σ c Γ ->
    Fun_inv k rho
            (M.set Γ v (def_funs B B  (M.set Γ v rho') (M.set Γ v rho')))
            Scope Funs σ c Γ.
  Proof. 
    intros Hnin Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite def_funs_neq in Hget1; eauto. rewrite M.gss in Hget1.
    inv Hget1.
    repeat eexists; eauto.
    now rewrite M.gss.
    eapply def_funs_spec in Hget2.
    destruct Hget2 as [[Hname Heq] | [Hname Hget']].
    - inv Heq. repeat eexists; eauto.
      rewrite M.gso.
      rewrite def_funs_eq. reflexivity. eassumption.
      intros Hc; subst; eauto.
    - rewrite M.gsspec in Hget'.
      destruct (peq (σ f) Γ).
      + subst. inv Hget'.
      + repeat eexists; eauto. rewrite M.gso. 
        rewrite def_funs_neq; eauto. 
        rewrite M.gso. eassumption.
        now intros Hc; subst; eauto.
        now intros Hc; subst; eauto.
  Qed.

  Global Instance Fun_inv_proper :
    Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==>
                     Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           (Fun_inv).
  Proof.
    constructor; intros Hinv; subst;
    intros f v1 Hninf Hinf Hget;
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto;
    repeat eexists; try (now rewrite <- H2; eauto); try rewrite H2; eauto.
  Qed.
  
  (** Define a block of functions in the first environment and put them in the
    current scope *)
  Lemma Fun_inv_def_funs_l k rho rho' B1 B1' Scope Funs σ c Γ:
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') -> 
    Fun_inv k rho rho' Scope Funs σ c Γ ->
    Fun_inv k (def_funs B1 B1' rho rho) rho'
            (Union _ (name_in_fundefs B1')  Scope) Funs σ c Γ.
  Proof.
    intros HD Hinv f v1 Hninf Hinf Hget. rewrite def_funs_neq in Hget; eauto.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. repeat eexists; eauto.
    intros Hc; inv Hc; eauto.
    eapply HD. econstructor; eauto.
    eexists; split; [| now eauto ]. constructor; eauto.
  Qed.

  (** Define a block of functions in the second environment and put the in the
    current scope *)
  Lemma Fun_inv_def_funs_r k rho rho' B1 B1' Scope Funs σ c Γ:
    ~ In _ (name_in_fundefs B1') Γ ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') -> 
    Fun_inv k rho rho' Scope Funs σ c Γ ->
    Fun_inv k rho (def_funs B1 B1' rho' rho')
            (Union _ (name_in_fundefs B1') Scope) Funs σ c Γ.
  Proof.
    intros Hnin HD Hinv f v1 Hninf Hinf Hget.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. repeat eexists; eauto.
    now rewrite def_funs_neq; eauto.
    intros Hc; inv Hc; eauto. 
    eapply HD. econstructor; eauto. eexists;  split; [| now eauto ].
    now constructor; eauto.
    rewrite def_funs_neq; eauto. 
    intros Hc. eapply HD. constructor; eauto. eexists; split; [| now eauto ].
    now constructor; eauto.
  Qed.

  (** Define a block of functions in both environments and put the in the
    current scope *)
  Lemma Fun_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs σ c Γ:
    ~ In _ (name_in_fundefs B2') Γ -> ~ In _ (name_in_fundefs B1') Γ ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B2') ->
    Fun_inv k rho rho' Scope Funs σ c Γ ->
    Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
            (Union _ (name_in_fundefs B1') Scope) Funs σ c Γ.
  Proof.
    intros Hnin1 Hnin2 HD1 HD2 Hinv f v1 Hninf Hinf Hget.
    rewrite def_funs_neq in Hget; eauto.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    subst. repeat eexists; eauto.
    now rewrite def_funs_neq; eauto.
    intros Hc; inv Hc; eauto.
    eapply HD1. econstructor; eauto. eexists; split; [| now eauto ].
    now constructor; eauto.
    rewrite def_funs_neq; eauto.
    intros Hc. eapply HD2. econstructor; eauto. eexists; split; [| now eauto ].
    now constructor; eauto.
  Qed.
  
  (** * Lemmas about FV_inv *)

  (** Extend the first environment with a variable in [Scope] *)
  Lemma FV_inv_set_In_Scope_l k rho rho' x v Scope Funs FVs c Γ :
    In var Scope x ->
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs c Γ FVs.
  Proof.
    intros Hin HInv x' N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HInv as [vs [v1 [Hget' [Hnth' Hcc]]]]; eauto.
    rewrite M.gso in Hget. now eauto.
    intros Hc; subst. now eauto.
  Qed.
  
  (** Extend the second environment with a variable in [Scope] that is not [Γ].
    XXX : deprecated. See [FV_inv_set_r] *)
  Lemma FV_inv_set_In_Scope_r k rho rho' x v Scope Funs FVs c Γ :
    In var Scope x ->
    x <> Γ ->
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k rho (M.set x v rho') Scope Funs c Γ FVs.
  Proof.
    intros Hin Hneq HInv x' N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HInv as [vs [v1 [Hget' [Hnth' Hcc]]]]; eauto.
    repeat eexists; eauto.
    now rewrite M.gso; eauto.
  Qed.

  (** Extend the first environment with a variable not in [FVs] *)
  Lemma FV_inv_set_not_In_FVs_l k rho rho' x v Scope Funs c Γ FVs :
    ~ List.In x FVs ->
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs c Γ FVs.
  Proof.
    intros Hnin HInv x' N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HInv as [vs [v1 [Hget' [Hnth' Hcc]]]]; eauto.
    rewrite M.gso in Hget. now eauto. intros Hc. subst.
    eapply nthN_In in Hnth.
    contradiction.
  Qed.

  (** Extend the second environment with a variable that is not [Γ] *)
  Lemma FV_inv_set_r k rho rho' x v Scope Funs c Γ FVs :
    x <> Γ ->
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k rho (M.set x v rho') Scope Funs c Γ FVs.
  Proof.
    intros Hneq HInv x' N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HInv as [vs [v1 [Hget' [Hnth' Hcc]]]]; eauto.
    repeat eexists; eauto. 
    rewrite M.gso. now eauto. congruence.
  Qed.
  
  (** Extend the [Scope]. TODO : replace with monotonicity property? *)
  Lemma FV_inv_extend_Scope k rho rho' Scope Funs c Γ FVs x :
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k rho rho' (Union _ (Singleton _ x) Scope) Funs c Γ FVs.
  Proof.
    intros HInv x' N v' Hnin1 Hnin2 Hnth Hget. eapply HInv; eauto.
  Qed.
  
  (** Define a block of functions in both environments and put the in the
    current scope *)
  Lemma FV_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs c Γ FVs:
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    FV_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
           (Union _ (name_in_fundefs B1') Scope) Funs c Γ FVs.
  Proof.
    intros Hnin Hnin' HInv x' N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HInv as [vs [v1 [Hget' [Hnth' Hcc]]]]; eauto.
    now rewrite def_funs_neq in Hget; eauto.
    repeat eexists; eauto. now rewrite def_funs_neq.
  Qed.


  (** * Interpretation of evaluation contexts as environments *)

  Inductive ctx_to_rho : exp_ctx -> env -> env -> Prop :=
  | Hole_c_to_rho :
      forall rho,
        ctx_to_rho Hole_c rho rho
  | Eproj_c_to_rho :
      forall rho rho' t y N Γ C vs v,
        M.get Γ rho = Some (Vconstr t vs) ->
        nthN vs N = Some v ->
        ctx_to_rho C (M.set y v rho) rho' ->
        ctx_to_rho (Eproj_c y t N Γ C) rho rho'
  | Econstr_c_to_rho :
      forall rho rho' t y  x Γ C v1 v2,
        M.get Γ rho = Some v1 ->
        M.get x rho = Some v2 ->
        ctx_to_rho C (M.set y (Vconstr t [v2; v1]) rho) rho' ->
        ctx_to_rho (Econstr_c y t [x; Γ] C) rho rho'.


  (** * Lemmas about [ctx_to_rho] *)

  Lemma ctx_to_rho_comp_ctx_l C C1 C2 rho rho' :
    ctx_to_rho C rho rho' ->
    comp_ctx C1 C2 C ->
    exists rho'',
      ctx_to_rho C1 rho rho'' /\
      ctx_to_rho C2 rho'' rho'.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. eexists; split; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
  Qed.

  Lemma ctx_to_rho_comp_ctx_f_r C1 C2 rho1 rho2 rho3 :
    ctx_to_rho C1 rho1 rho2 ->
    ctx_to_rho C2 rho2 rho3 ->
    ctx_to_rho (comp_ctx_f C1 C2) rho1 rho3.
  Proof.
    revert C2 rho1 rho2 rho3.
    induction C1; intros C2 rho1 rho2 rho3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - simpl; econstructor; eauto. 
    - simpl; econstructor; eauto.
  Qed.

  (** [(e1, ρ1) < (C [ e2 ], ρ2)] if [(e1, ρ1) < (e2, ρ2')], where [ρ2'] is the
    interpretation of [C] in [ρ2] *)
  Lemma ctx_to_rho_cc_approx_exp k rho1 rho2 rho2' C e e' :
    ctx_to_rho C rho2 rho2' ->
    cc_approx_exp pr cenv clo_tag k (e, rho1) (e', rho2') ->
    cc_approx_exp pr cenv clo_tag k (e, rho1) (C |[ e' ]|, rho2).
  Proof.  
    intros Hctx Hcc. induction Hctx.
    - assumption.
    - intros v1 c1 Hleq1 Hstep1.
      edestruct IHHctx as [v2 [c2 [Hstep2 Hcc2]]]; eauto.
      repeat eexists; eauto.
      simpl. econstructor; eauto.
    - intros v1' c1 Hleq1 Hstep1.
      edestruct IHHctx as [v2' [c2 [Hstep2 Hcc2]]]; eauto.
      repeat eexists; eauto.
      simpl. econstructor; eauto. simpl.
      rewrite H, H0. reflexivity.
  Qed.

  (** * Various lemmas about [Closure_conversion_fundefs] *)

  Lemma closure_conversion_fundefs_find_def σ c Funs FVs B1 B2 f t1 xs e1 :
    injective_subdomain (name_in_fundefs B1) σ ->
    Closure_conversion_fundefs clo_tag Funs σ c FVs B1 B2 ->
    find_def f B1 = Some (t1, xs, e1) ->
    exists Γ' C e2,
      ~ In var (Union var (image σ Funs) (Union _ (FromList xs) (bound_var e1))) Γ' /\
      find_def (σ f) B2 = Some (t1, Γ' :: xs, (C |[ e2 ]|)) /\
      Closure_conversion clo_tag (FromList xs) Funs σ c Γ' FVs e1 e2 C.
  Proof.
    intros Hinj Hcc Hdef. induction Hcc.
    - simpl in Hdef. destruct (M.elt_eq f f0) eqn:Heq; subst.
      + inv Hdef. repeat eexists; eauto. 
        simpl.
        intros Hc. eapply H. now eauto.
        simpl. rewrite peq_true. reflexivity.
      + edestruct IHHcc as [Γ'' [C' [e2 [Hnin [Hfind Hcc']]]]]; eauto.
        eapply injective_subdomain_antimon. eassumption.
        now apply Included_Union_r.
        repeat eexists; eauto. simpl. rewrite peq_false. eassumption.
        intros Hc. eapply n. eapply Hinj; eauto.
        right. eapply fun_in_fundefs_name_in_fundefs.
        eapply find_def_correct. now eauto.
        left; eauto.
    - inv Hdef.
  Qed.

  (** * Lemmas about [make_closures] *)

  Lemma make_closures_image_Included B S Γ C σ S' :
    make_closures clo_tag B S Γ C σ S' ->
    Included _ (image σ (name_in_fundefs B)) S.
  Proof. 
    intros Hmc. induction Hmc.
    - rewrite image_Empty_set. apply Included_Empty_set.
    - simpl. subst. 
      rewrite image_Union, image_Singleton.
      apply Union_Included. apply Singleton_Included.
      rewrite <- H0. rewrite extend_gss. eassumption.
      eapply Included_trans.
      rewrite <- H0. now apply image_extend_Included.
      apply Union_Included.
      eapply Included_trans. eassumption. now eapply Setminus_Included.
      now apply Singleton_Included.
  Qed.
  
  Lemma make_closures_free_set_Included B S Γ C σ S' :
    make_closures clo_tag B S Γ C σ S' ->
    Included _  S' S.
  Proof. 
    intros Hmc. induction Hmc.
    - now apply Included_refl.
    - eapply Included_trans. eassumption.
      now apply Setminus_Included.
  Qed.

  Lemma make_closures_image_Disjoint B S Γ C σ S' :
    make_closures clo_tag B S Γ C σ S' ->
    Disjoint _ (image σ (name_in_fundefs B)) S'.
  Proof.
    intros Hmc. induction Hmc.
    - rewrite image_Empty_set. apply Disjoint_Empty_set_l.
    - simpl. rewrite image_Union, image_Singleton.
      rewrite <- H0. rewrite extend_gss. eapply Union_Disjoint_l.
      + eapply Disjoint_Included_r.
        now eapply make_closures_free_set_Included; eauto.
        now eauto with Ensembles_DB.
      + eapply Disjoint_Included_l. rewrite <- H0.
        now apply image_extend_Included.
        apply Union_Disjoint_l. eassumption.
        eapply Disjoint_Included_r.
        now eapply make_closures_free_set_Included; eauto.
        now eauto with Ensembles_DB.
  Qed.

  Lemma make_closures_injective B S Γ C σ S' :
    Disjoint _ S (name_in_fundefs B) ->
    make_closures clo_tag B S Γ C  σ S' ->
    injective_subdomain (name_in_fundefs B) σ.
  Proof. 
    intros Hd Hmc. induction Hmc.
    - intros x y Hc. inv Hc. 
    - simpl. rewrite <- H0.
      eapply injective_subdomain_extend.
      + eapply IHHmc.
        eapply Disjoint_Included_r; [
          | eapply Disjoint_Included_l; [| eassumption ] ];
        eauto with Ensembles_DB.
      + eapply make_closures_image_Included in Hmc.
        intros Hc. 
        eapply Hmc; [| now apply Included_refl ].
        eapply image_monotonic; [ | eassumption ].
        now apply Setminus_Included.
  Qed.

  (** * Lemmas about [project_var] and [project_vars] *)

  Lemma project_var_free_set_Included Scope Funs σ c Γ FVs x x' C S S' :
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    Included _ S' S.
  Proof with now eauto with Ensembles_DB.
    intros Hproj. inv Hproj...
  Qed.

  Lemma project_vars_free_set_Included Scope Funs σ c Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Included _ S' S.
  Proof.
    intros Hproj. induction Hproj.
    - now apply Included_refl.
    - eapply Included_trans. eassumption.
      eapply project_var_free_set_Included. eassumption. 
  Qed.

  Lemma project_var_not_In_free_set Scope Funs σ c Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. eauto.
    - inv Hc. exfalso. eauto.
    - inv Hc. exfalso. eauto.    
  Qed.

  Lemma project_vars_not_In_free_set Scope Funs σ c Γ FVs xs xs' C S S'  :
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
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

  Lemma project_var_get Scope Funs σ c Γ FVs S1 x x' C1 S2 rho1 rho2 y:
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx. inv H11.
      destruct (peq y x'); subst.
      contradiction.
      now rewrite M.gso.
    - inv Hctx. inv H12.
      destruct (peq y x'); subst.
      contradiction.
      now rewrite M.gso.
  Qed.    

  Lemma project_vars_get Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 rho2 y:
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    revert Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y.
    induction xs; intros Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y Hproj Hctx Hnin.
    - inv Hproj. inv Hctx. reflexivity.
    - inv Hproj.  
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_get in Hctx1; eauto. 
      eapply IHxs in Hctx2; eauto.
      rewrite Hctx1, <- Hctx2. reflexivity.
      intros Hc. eapply Hnin.
      eapply project_var_free_set_Included; eassumption.
  Qed.

  Lemma project_var_getlist Scope Funs σ c Γ FVs S1 x x' C1 S2 rho1 rho2 ys :
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 rho2; induction ys; intros rho1 rho2  Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin. 
      erewrite project_var_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        


  Lemma project_vars_getlist Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 rho2 ys :
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_rho C1 rho1 rho2 ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 rho2; induction ys; intros rho1 rho2  Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin. 
      erewrite project_vars_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        

  Lemma project_var_In_Union Scope Funs σ c Γ FVs S x x' C S' :
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    In _ (Union var Scope (Union var Funs (FromList FVs))) x.
  Proof.
    intros Hvar. inv Hvar; eauto.
    right; right. eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_In_Union Scope Funs σ c Γ FVs S xs xs' C S' :
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Included var (FromList xs) (Union var Scope (Union var Funs (FromList FVs))).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - rewrite FromList_nil. now apply Included_Empty_set.
    - rewrite FromList_cons.
      eapply Union_Included; [| eassumption ].
      eapply Singleton_Included. eapply project_var_In_Union.
      eassumption.
  Qed.
  
  Lemma project_var_not_In Scope Funs σ c Γ FVs S x x' C S' :
    Disjoint _ S (Union var Scope
                        (Union var Funs
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    ~ In _ S x.
  Proof.
    intros Hd  Hproj. inv Hproj; intros Hin; try now eapply Hd; eauto.
    eapply nthN_In in H1. eapply Hd. eauto.
  Qed.

  Lemma project_vars_Disjoint Scope Funs σ c Γ FVs S xs xs' C S' :
    Disjoint _ S (Union var Scope
                        (Union var Funs
                               (Union var (FromList FVs) (Singleton var Γ)))) ->      
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Disjoint _ S (FromList xs).
  Proof.
    revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
    - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
    - inv Hproj. rewrite FromList_cons.
      eapply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. eapply project_var_not_In; eauto.
      inv H8.
      + eapply IHxs; [| eassumption ]. eauto.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H12.
        eapply Disjoint_Included_r. eassumption.
        eauto with Ensembles_DB.
      + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y'))
                               (FromList xs))
          by (eapply IHxs; eauto with Ensembles_DB).
        eapply project_vars_In_Union in H12.
        eapply Disjoint_Included_r. eassumption.
        eauto with Ensembles_DB.
  Qed.

  (** * Lemmas about the existance of the interpretation of an evaluation context *)

  Lemma project_var_ctx_to_rho Scope Funs σ c Γ FVs x x' C S S' v1 k rho1 rho2 :
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    FV_inv k rho1 rho2 Scope Funs c Γ FVs ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    M.get x rho1 = Some v1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hproj HFV HFun Hget. inv Hproj.
    - eexists; econstructor; eauto.
    - edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      eexists; econstructor; eauto.
      constructor.
    - edestruct HFV as [vs [v [Hget' [Hnth' Hcc]]]]; eauto.
      eexists. econstructor; eauto. constructor. 
  Qed.

  Lemma make_closures_ctx_to_rho B S c Γ C σ S' k rho1 rho2 :
    make_closures clo_tag B S Γ C σ S' ->
    unique_functions B ->
    Disjoint _ S (name_in_fundefs B) ->
    ~ In _ (name_in_fundefs B) Γ ->
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ c Γ ->
    (forall f, In _ (name_in_fundefs B) f -> exists v, M.get f rho1 = Some v) ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hclo. revert rho1 rho2. induction Hclo; intros rho1 rho2 Hun Hd Hnin HFun Hyp. 
    - eexists; constructor. 
    - destruct (Hyp f) as [v' Hget'].
      now left; eauto.
      edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      now apply not_In_Empty_set.
      now left; eauto. inv Hun.
      edestruct IHHclo as [rho2' Hctx]; [ eassumption | | | | | ]. 
      + eauto with Ensembles_DB.
      + intros Hc; eapply Hnin; right; eauto.
      + eapply Fun_inv_set_not_In_Funs_r_not_Γ with (x := f).
        rewrite Setminus_Empty_set_neut_r.
        intros Hin. eapply make_closures_image_Included in Hclo.
        eapply Hd.  constructor; [| now left; eauto ].
        eapply Hclo. eassumption.
        intros Hc; subst. eapply Hnin. now left; eauto.
        intros x v Hninx Hinx Hget.
        edestruct HFun  with (f0 := x) as
            [vs'' [rho3' [B3' [f3' [rho4' [B4' [f4' [Hget1' [Heq2' [Ηnin2' [Hget2' Happrox']]]]]]]]]]]; eauto.
        now right.
        repeat eexists; eauto.
        now apply not_In_Empty_set. 
        rewrite <-  H0, extend_gso in Hget2'.
        now eauto.
        intros Hc; subst; contradiction.
      + intros. eapply Hyp. right; eauto.
      + eexists. econstructor; eauto.
        now rewrite <-  H0, extend_gss in Hget2; eauto.
  Qed.
  
  Lemma project_vars_ctx_to_rho Scope Funs σ c Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    FV_inv k rho1 rho2 Scope Funs c Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof. 
    intros HD Hvars HFun HFV.
    (* assert (HD' := Hvars). *)
    revert Scope Funs Γ FVs xs' C S S' vs1 k
           rho1 rho2  HD  Hvars HFun HFV.
    induction xs;
      intros Scope Funs Γ FVs xs' C S S' vs1 k
             rho1 rho2 HD Hvars HFun HFV Hgetlist.
    - inv Hvars. eexists; econstructor; eauto.
    - inv Hvars. simpl in Hgetlist.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate. 
      destruct (getlist xs rho1) eqn:Hgetlist1; try discriminate.
      edestruct project_var_ctx_to_rho with (rho1 := rho1) as [rho2' Hctx1]; eauto.
      edestruct IHxs with (rho2 := rho2') as [rho2'' Hctx2].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + eassumption.
      +inv Hgetlist. intros f v' Hnin Hin Hget.
       edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
       repeat eexists; eauto.
       erewrite <- project_var_get; eauto.  intros Hc. eapply HD. now eauto.
       erewrite <- project_var_get; eauto. 
       intros Hin'. eapply HD. constructor. now eauto.
       right. left. eexists. now eauto.
      + intros x N v' Hnin1 Hnin2 Hnth Hget.
        edestruct HFV as [vs [v'' [Hget' [Hnth' Hcc]]]]; eauto.
        repeat eexists; eauto.
        erewrite <- project_var_get; eauto.
        intros Hin. eapply HD. now eauto.
      + eassumption.
      + exists rho2''. eapply ctx_to_rho_comp_ctx_f_r; eassumption.
  Qed.

  (** * Correctness lemmas *)

  Lemma fun_in_fundefs_bound_var_fundefs B f tau xs e :
    fun_in_fundefs B (f, tau, xs, e) ->
    Included _ (Union _ (Singleton _ f) (Union _ (FromList xs) (bound_var e))) (bound_var_fundefs B).
  Proof.
    intros H; induction B.
    - inv H.
      + inv H0. rewrite bound_var_fundefs_Fcons.
        rewrite !Union_assoc. now apply Included_Union_l.
      + rewrite bound_var_fundefs_Fcons.
        eapply Included_trans. now eauto.
        eauto with Ensembles_DB.
    - inv H.
  Qed.

  (** Correctness of [closure_conversion_fundefs]. Basically un-nesting the nested
    induction that is required by the correctness of [Closure_conversion] *) 
  Lemma Closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
        Scope c Γ FVs Funs' σ FVs' vs:
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e : exp) (rho rho' : env) (e' : exp)
         (Scope Funs : Ensemble var) σ c (Γ : var) (FVs : list var)
         (C : exp_ctx),
         cc_approx_env_P pr cenv clo_tag Scope m rho rho' ->
         ~ In var (bound_var e) Γ ->
         binding_in_map (occurs_free e) rho ->
         fundefs_names_unique e ->
         injective_subdomain Funs σ ->
         Disjoint var (image σ (Setminus _ Funs Scope)) (bound_var e) ->
         Fun_inv m rho rho' Scope Funs σ c Γ ->
         FV_inv m rho rho' Scope Funs c Γ FVs ->
         Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C ->
         cc_approx_exp pr cenv clo_tag m (e, rho) (C |[ e' ]|, rho')) ->
    Same_set _ (occurs_free_fundefs B1) (FromList FVs) ->
    fundefs_names_unique_fundefs B1 ->
    fundefs_names_unique_fundefs B1' ->
    binding_in_map (occurs_free_fundefs B1) rho ->
    Closure_conversion_fundefs clo_tag (name_in_fundefs B1) σ c FVs B1 B2 ->
    Closure_conversion_fundefs clo_tag Funs' σ c FVs' B1' B2' ->
    Disjoint _ (image σ (name_in_fundefs B1)) (bound_var_fundefs B1) ->
    Disjoint _ (image σ (name_in_fundefs B1')) Scope ->
    Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2) ->
    injective_subdomain (name_in_fundefs B1) σ ->
    injective_subdomain (name_in_fundefs B1') σ ->
    ~ In _ (name_in_fundefs B1) Γ ->
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2) Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    closure_env k rho (Empty_set _) (Empty_set _) vs FVs ->
    Fun_inv k (def_funs B1 B1' rho rho)
            (def_funs B2 B2' (M.set Γ (Vconstr c vs) rho') (M.set Γ (Vconstr c vs) rho'))
            Scope (name_in_fundefs B1') σ c Γ.
  Proof.
    revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' c vs.
    induction k as [k IHk] using lt_wf_rec1.
    induction B1'; 
      intros rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' c vs
             IHe Hs Hun Hun' Hfv Hcc Hcc' Hd Hd'' Hseq Hinj Hinj' Hnin1 Hnin1' Hnin2 Hnin2' Henv.
    - inv Hcc'. simpl.
      eapply Fun_inv_set. 
      + eapply IHB1'; eauto.
        * intros B H. inv H; eauto. specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
          inv Hun'; eauto.
        * eapply Disjoint_Included_l; [| eassumption ].
          eapply image_monotonic.  now apply Included_Union_r.
        * eapply injective_subdomain_antimon. eassumption. now apply Included_Union_r.
        * intros Hc. apply Hnin1'. simpl; eauto.
        * intros Hc. apply Hnin2'. simpl; eauto.
      + intros Hc. eapply Hnin2'. subst. left. eauto.
      + intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
        left. eauto.
      + simpl in Hinj'. eapply injective_subdomain_Union_not_In_image in Hinj'.
        intros Hc. eapply Hinj'. constructor; eauto. eexists; eauto.
        eapply image_monotonic; [| eassumption ]. now apply Setminus_Included.
        eapply Disjoint_sym. eapply Disjoint_Singleton_r.
        specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
        inv Hun'; eauto.
      + rewrite def_funs_neq. rewrite M.gss. reflexivity.
        intros Hc. eapply Hnin2'. right. eauto.
      + rewrite cc_approx_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
        edestruct (@setlist_length val)
        with (rho' := def_funs B2 B2 (M.set Γ (Vconstr c vs) rho')
                               (M.set Γ (Vconstr c vs) rho')) as [rho2' Hset'].
        eassumption. now eauto.
        edestruct closure_conversion_fundefs_find_def
          as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]; [  |  | eassumption |].
        eassumption. eassumption.
        exists Γ'', xs1. do 2 eexists.
        split. reflexivity. split. eassumption. split.
        simpl. rewrite Hset'. reflexivity.
        intros Hlt Hall. eapply IHe with (Scope := FromList xs1). 
        * eassumption.
        * eapply cc_approx_env_P_set_not_in_P_r.
          eapply cc_approx_env_P_setlist_l with (P1 := Empty_set _); eauto.
          eapply cc_approx_env_Empty_set. now intros Hc; eauto.
          intros Hc. eapply Hnin''. right; left. eassumption.
        * intros Hc. apply Hnin''. eauto.
        * eapply binding_in_map_antimon.
          eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
          eapply binding_in_map_setlist; [| now eauto ].
          eapply binding_in_map_def_funs. eassumption.
        * intros B Hin. eapply Hun. left. 
          eapply fun_in_fundefs_funs_in_fundef; eauto.
          eapply find_def_correct. eassumption.
        * now eapply Hinj.
        * eapply Disjoint_Included_r;
          [| eapply Disjoint_Included_l;
             [ apply image_monotonic; now apply Setminus_Included | now apply Hd ] ].
          eapply Included_trans;
            [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
          rewrite !Union_assoc. now apply Included_Union_r.
        * assert
            (Fun_inv j (def_funs B1 B1 rho rho)
                     (def_funs B2 B2 (M.set Γ (Vconstr c vs) rho')
                               (M.set Γ (Vconstr c vs) rho'))
                     (FromList xs1) (name_in_fundefs B1) σ c Γ).
          { eapply IHk; try eassumption.
            - intros. eapply IHe; eauto. omega. 
            - eapply Disjoint_Included_r; [| eassumption ].
              eapply Included_trans;
                [| now eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ].
              apply Included_Union_preserv_r. now apply Included_Union_l.
            - intros x1 N v1 Hnin3 Hnin4 Hnth Hget.
              edestruct Henv as [v2 [Hnth' Happ']]; eauto.
              eexists; split; eauto. eapply cc_approx_val_monotonic.
              eassumption. omega. } 
          eapply Fun_inv_rename with (Γ := Γ).
          intros Hin.
          eapply Hnin2. rewrite <- Hseq. eapply image_monotonic; [| eassumption ].
          now apply Setminus_Included.
          intros Hin. eapply Hnin''. left; eassumption.
          eapply Fun_inv_setlist_In_Scope_l; [ now apply Included_refl | |].
          eapply Fun_inv_setlist_In_Scope_r; [ now apply Included_refl | | | eassumption ].  
          eapply Disjoint_Included_r;
            [| eapply Disjoint_Included_l;
               [ apply image_monotonic; now apply Setminus_Included | now apply Hd ]].
          eapply Included_trans;
            [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
          right; eauto.
          eapply Fun_inv_reset; [| eassumption ]. eassumption. now eauto.
        * intros x N v1 Hnin3 Hnin4 Hnth Hget'. 
          edestruct Henv as [v' [Hnth'' Hcc'']]; eauto.
          now apply not_In_Empty_set. now apply not_In_Empty_set.
          erewrite <- def_funs_neq.
          erewrite setlist_not_In. eassumption. now eauto.
          intros Hc. now eapply Hnin3; eauto. eassumption.
          repeat eexists; eauto.
          rewrite M.gss. reflexivity.
          eapply cc_approx_val_monotonic. eassumption. omega.
        * eassumption.
    - intros f v Hnin Hin Hget. now inv Hin.
  Qed.
  
  (** Correctness of [project_var] *)
  Lemma project_var_correct k rho1 rho2 rho2'
        Scope Funs σ c Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    FV_inv k rho1 rho2 Scope Funs c Γ FVs ->
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    ~ In _ S' x' /\
    cc_approx_env_P pr cenv clo_tag Scope k rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ c Γ /\
    FV_inv k rho1 rho2' Scope Funs c Γ FVs /\
    cc_approx_var_env pr cenv clo_tag k rho1 rho2' x x'.
  Proof.
    intros Hproj Hcc Hfun Henv Hctx Hd.
    inv Hproj.
    - inv Hctx. repeat split; eauto. intros Hc. eapply Hd; eauto.
    - inv Hctx. inv H11.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. eauto.
      + (* TODO : make lemma *)
        intros f v Hnin Hin Hget.
        edestruct Hfun as
            [vs [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | now intros Heq; subst; eapply Hd; eauto ].
        rewrite M.gso. eassumption. 
        intros Hc. subst; eapply Hd; constructor; eauto. right; left.
        eexists. split; [| now eauto ]. constructor; eauto.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hfun as
            [vs [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        rewrite Hget2 in H10; inv H10.
        rewrite Hget1 in H9; inv H9. eassumption.
    - inv Hctx. inv H12.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. eauto.
      + intros f' v' Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | now intros Heq; subst; eapply Hd; eauto ].
        rewrite M.gso. eassumption. 
        intros Hc. subst; eapply Hd; constructor; eauto. right; left.
        eexists. split; [| now eauto ]. constructor; eauto.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Henv as [vs' [v'' [Hget' [Hnth Hcc']]]]; eauto.
        rewrite Hget' in H10; inv H10.
        rewrite H11 in Hnth. now inv Hnth.
  Qed.

  (** Correctness of [project_vars] *)
  Lemma project_vars_correct k rho1 rho2 rho2'
        Scope Funs σ c Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ c Γ ->
    FV_inv k rho1 rho2 Scope Funs c Γ FVs ->
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    cc_approx_env_P pr cenv clo_tag Scope k rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ c Γ /\
    FV_inv k rho1 rho2' Scope Funs c Γ FVs /\
    (forall vs,
       getlist xs rho1 = Some vs ->
       exists vs', getlist xs' rho2' = Some vs' /\
              Forall2 (cc_approx_val pr cenv clo_tag k) vs vs').
  Proof.
    revert k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S.
    induction xs;
      intros k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S Hproj Hcc Hfun Henv Hctx Hd.
    - inv Hproj. inv Hctx. repeat split; eauto. 
      eexists. split. reflexivity. 
      inv H. now constructor. 
    - inv Hproj.
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_correct in Hctx1; eauto.
      destruct Hctx1 as [Hnin [Hcc1 [Hfun1 [Henv1 Hcc_var]]]].
      edestruct IHxs as [Hcc2 [Hfun2 [Henv2 Hyp]]]; eauto;
      [ eapply Disjoint_Included_l; [| eassumption ];
        eapply project_var_free_set_Included; eassumption |].
      repeat split; eauto. intros vs Hget. 
      simpl in Hget. destruct (M.get a rho1) eqn:Hget'; try discriminate. 
      destruct (getlist xs rho1) eqn:Hgetlist; try discriminate.
      inv Hget. edestruct Hyp as [vs' [Hgetlist' Hall]]; [ reflexivity |].
      edestruct Hcc_var as [v' [Hget''' Hcc''']]; eauto.
      eexists. split; eauto. simpl. rewrite Hgetlist'. 
      erewrite <- project_vars_get; eauto. rewrite Hget'''. reflexivity.
  Qed.

  (** Correctness of [make_closures] *)
  Lemma make_closures_correct k rho1 rho2 rho2' B S c' Γ' C σ S' σ' Scope Funs FVs c Γ :
    make_closures clo_tag B S Γ' C σ S' ->
    unique_functions B ->
    ~ In _ (name_in_fundefs B) Γ ->
    ~ In _ (name_in_fundefs B) Γ' ->
    Included _ (name_in_fundefs B) Scope ->
    Disjoint _ S (name_in_fundefs B) ->
    cc_approx_env_P pr cenv clo_tag (Setminus _ Scope (name_in_fundefs B)) k rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ' c Γ ->  
    FV_inv k rho1 rho2 Scope Funs c Γ FVs ->
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ c' Γ' ->
    ctx_to_rho C rho2 rho2' ->
    cc_approx_env_P pr cenv clo_tag Scope k rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ' c Γ /\
    FV_inv k rho1 rho2' Scope Funs c Γ FVs.
  Proof.
    intros Hmake. revert k rho1 rho2 rho2' Scope Funs FVs Γ.
    induction Hmake;
      intros k rho1 rho2 rho2' Scope Funs FVs Γ1 Hun Hnin1 Hnin2
             Hsub Hd Hcc Hfun Henv Hfun' Hctx.
    - inv Hctx. repeat split; eauto.
      simpl in *.
      rewrite Setminus_Empty_set_neut_r in Hcc. eassumption.
    - eapply ctx_to_rho_comp_ctx_l in Hctx; [| apply Constr_cc; constructor ].
      destruct Hctx as [rho2'' [Hctx1 Hctx2]].
      inv Hctx1. inv H10. inv Hun.
      edestruct IHHmake as [Hcc1 [Hfun1 Henv1]];
        [ eassumption | | | | | | | | | eassumption | ].  
      + intros Hc. eapply Hnin1. right. now apply Hc. 
      + intros Hc. eapply Hnin2. right. now apply Hc.
      + eapply Included_trans; [| now apply Hsub ].
        now eapply Included_Union_r.
      + eauto with Ensembles_DB.
      + eapply cc_approx_env_P_antimon;
        [| now apply (@Included_Union_Setminus _ _ (Singleton var f) _) ]. 
        rewrite Setminus_Union, (Union_commut (name_in_fundefs B)).
        eapply cc_approx_env_P_union.
        eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. inv Hc. now eauto.
        intros x Hin v Hget. inv Hin.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
        [| | eassumption |]. now apply not_In_Empty_set. now left. 
        eexists. split. now rewrite M.gss.
        subst. rewrite H8 in Hget1. inv Hget1.
        rewrite <- H0, extend_gss in Hget2. rewrite H9 in Hget2. inv Hget2.
        eassumption.
      + eapply Fun_inv_set_In_Scope_r_not_Γ ; [| | eassumption ].
        * eapply Hsub. now left. 
        * intros Hc; subst. eapply Hnin1. left; eauto.
      + eapply FV_inv_set_r; [| eassumption ].
        intros Hc; subst. eapply Hnin1. left; eauto.
      + intros f'' v Hnin Hin Hget.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
          [| | eassumption |]. now apply not_In_Empty_set. now right. 
        subst. repeat eexists; eauto. 
        rewrite M.gso. eassumption.
        intros Hc; subst. eapply Hnin2. now left; eauto.
        now eapply not_In_Empty_set.
        rewrite <- H0 in Hget2. rewrite M.gso. rewrite extend_gso in Hget2.
        eassumption.
        intros Hc; subst. contradiction.
        eapply make_closures_image_Included in Hmake. intros Hc; subst.
        eapply Hd. constructor; [| now left; eauto ].
        eapply Hmake. eexists; eauto. 
      + eauto.
  Qed.

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct k rho rho' e e' Scope Funs σ c Γ FVs C :
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k rho rho' ->
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain Funs σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Setminus _ Funs Scope)) (bound_var e) ->
    (* [Fun] invariant *)
    Fun_inv k rho rho' Scope Funs σ c Γ ->
    (* Free variables invariant *)
    FV_inv k rho rho' Scope Funs c Γ FVs ->
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C ->
    cc_approx_exp pr cenv clo_tag k (e, rho) (C |[ e' ]|, rho').
  Proof with now eauto with Ensembles_DB.
    revert k e rho rho' e' Scope Funs σ c Γ FVs C.
    induction k as [k IHk] using lt_wf_rec1.
    induction e using exp_ind';
      intros rho1 rho2 e' Scope Funs σ c' Γ FVs C Happrox Hnin HFVs Hun Hinj Hd Hfun Henv Hcc.
    - (* Case Econstr *)
      inv Hcc.
      intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto. 
      intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H8; eauto. inv H8.
      repeat normalize_bound_var_in_ctx.
      edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | eassumption | | | | eassumption | eassumption | eassumption | ]. 
      + eapply cc_approx_env_P_extend with (v2 := Vconstr t v').
        eapply cc_approx_env_P_antimon; [ eassumption |]...
        rewrite cc_approx_val_eq. constructor; eauto.
        now eapply Forall2_Forall2_asym_included.
      + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        eapply occurs_free_Econstr_Included. 
      + intros f Hfin. eauto.
      + eapply Disjoint_Included_r;
        [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]]...
      + eapply Fun_inv_set_In_Scope_l. now eauto.
        eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_mon; [ | now eauto ]...
      + eapply FV_inv_set_In_Scope_l. now constructor.
        eapply FV_inv_set_r. intros Hc. eapply Hnin.
        subst. now eauto. now eapply FV_inv_extend_Scope.
      + repeat eexists; [| eassumption ].
        econstructor; eauto.
    - (* Case [Ecase x []] *)
      inv Hcc. inv H11.
      intros v1 c1 Hleq Hstep. inv Hstep. inv H5. 
    - (* Case [Ecase x ((c, p) :: pats] *)
      inv Hcc.
      inversion H11 as [ | [c1 p1] [c2 p2] l1 l2 [Heq [C' [e' [Heq' Hcc]]]] Hall ];
        simpl in Heq, Heq'; subst.
      intros v1 c1 Hleq Hstep. inv Hstep.
      repeat normalize_bound_var_in_ctx.
      simpl in H5. destruct (M.elt_eq c2 t) eqn:Heq; subst. 
      { inv H3. inv H5. inv H8. 
        - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
          rewrite cc_approx_val_eq in Happrox2.
          destruct vcon; try contradiction. inv Happrox2.
          edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
            [ eassumption
            | now intros Hc; eapply Hnin; eauto | |
            | eassumption | | eassumption | eassumption
            | eassumption | eassumption | eassumption | ].
          + eapply binding_in_map_antimon; [|  eassumption ].
            eapply occurs_free_Ecase_Included. now constructor.
          + intros f Hfin. eapply Hun.
            econstructor. eassumption. now constructor. 
          + eauto with Ensembles_DB.
          + repeat eexists; [| eassumption ].
            econstructor; eauto; [| simpl; now rewrite Heq ].
            econstructor; eauto. inv H11. eapply caseConsistent_same_cTags.
            eapply Forall2_monotonic; [| eassumption ].
            intros x x2 H'. now inv H'. eassumption.
        - edestruct Hfun as
              [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox']]]]]]]]]]]; eauto.
          congruence.
        - edestruct Henv as [vs2 [v' [Hget [Hnth' Happrox2]]]]; eauto.
          rewrite cc_approx_val_eq in Happrox2.
          destruct v'; try contradiction. inv Happrox2.
          edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
            [| now intros Hc; eapply Hnin; eauto | | 
             | eassumption | | | | eassumption | eassumption | eassumption
             | ].
          + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
            intros Hc. eapply H1. eauto.
          + eapply binding_in_map_antimon; [|  eassumption ].
            eapply occurs_free_Ecase_Included. now constructor.
          + intros f Hfin. eapply Hun.
            econstructor. eassumption. now constructor.
          + eauto with Ensembles_DB.
          + eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ]. 
            intros Hc. eapply H1. now eauto.
            intros Heq'; subst. eapply H1. now eauto.
          + eapply FV_inv_set_r. intros Hc. subst. eapply H1. now eauto.
            eassumption.
          +  repeat eexists; [| eassumption ]; econstructor; eauto.
             econstructor; eauto;
             [ rewrite M.gss ; reflexivity | | simpl; now rewrite Heq ].
             inv H11. econstructor; eauto. eapply caseConsistent_same_cTags.
             eapply Forall2_monotonic; [| eassumption ].
             intros x x2 H'. now inv H'. eassumption. }
      { inv H5. assert (H8' := H8). inv H8. 
        - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
          rewrite cc_approx_val_eq in Happrox2.
          destruct vcon; try contradiction. inv Happrox2.
          edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
            [ eassumption
            | now intros Hc; eapply Hnin; eauto | |
            | eassumption | | eassumption | eassumption | now econstructor; eauto
            | eassumption |  | ].
          + eapply binding_in_map_antimon; [| eassumption ].
            intros x Hin. inv Hin; eauto.
          + intros f Hfin. eapply Hun. inv Hfin. 
            econstructor; eauto. constructor 2. eassumption.
          + eauto with Ensembles_DB.
          + econstructor; eauto. inv H3. eassumption.
          + inv Hstep2. repeat eexists; [| eassumption ].
            inv H3.
            econstructor; eauto. simpl. rewrite Hget' in H7. inv H7.
            econstructor; eauto.
            simpl. rewrite Hget' in H7. inv H7. now rewrite Heq.
        -  edestruct Hfun as
              [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox']]]]]]]]]]]; eauto.
          congruence.
        - edestruct Henv as [vs2 [v' [Hget [Hnth' Happrox2]]]]; eauto.
          rewrite cc_approx_val_eq in Happrox2.
          destruct v'; try contradiction. inv Happrox2. inv H3.
          edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
            [ eassumption
            | now intros Hc; eapply Hnin; eauto | |
            | eassumption | | eassumption | eassumption | now econstructor; eauto
            | eassumption | now econstructor; eauto | ].
          + eapply binding_in_map_antimon; [|  eassumption ].
            intros x Hin. inv Hin; eauto.
          + intros f Hfin. eapply Hun. inv Hfin.
            econstructor; eauto. constructor 2. eassumption.
          + eauto with Ensembles_DB.
          + inv Hstep2; rewrite Hget in H20; inv H20; rewrite Hnth' in H21; inv H21.
            inv H22. rewrite M.gss in H10. inv H10.
            repeat eexists; [| eassumption ]; econstructor; eauto.
            econstructor; eauto. simpl. rewrite M.gss; reflexivity.
            now econstructor; eauto. simpl. now rewrite Heq. }
    - (* Case Eproj *)
      inv Hcc.
      intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_var_correct as [Hnin' [Happ [Hfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      rewrite cc_approx_val_eq in Happ'. destruct v'; try contradiction.
      inv Happ'. eapply ctx_to_rho_cc_approx_exp; eauto.
      intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H9; eauto.
      inv H9. edestruct (@Forall2_asym_nthN val) as [v2' [Hnth2 Happ2]]; eauto.
      repeat normalize_bound_var_in_ctx.
      edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | eassumption | | |
         | eassumption | eassumption | eassumption | ].
      + eapply cc_approx_env_P_extend; [| eassumption ].
        eapply cc_approx_env_P_antimon; [ eassumption |]...
      + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        eapply occurs_free_Eproj_Included. 
      + intros f Hfin. eauto.
      + eapply Disjoint_Included_r;
        [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]]...
      + eapply Fun_inv_set_In_Scope_l. now eauto.
        eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_mon; [ | now eauto ]...
      + eapply FV_inv_set_In_Scope_l. now constructor.
        eapply FV_inv_set_r. intros Hc. eapply Hnin.
        subst. now eauto. now eapply FV_inv_extend_Scope.
      + repeat eexists; [| eassumption ]. econstructor; eauto. 
    - (* Case Efun -- the hardest one! *) 
      inv Hcc.
      assert (Ha : exists vs, getlist FVs' rho1 = Some vs).
      { eapply In_getlist. intros x Hin. eapply HFVs. 
        rewrite occurs_free_Efun, H1. eauto. }
      destruct Ha as [vs Hgetlist].
      intros v1 c1 Hleq Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; [ | eassumption | | | | ]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto. rewrite <- app_ctx_f_fuse.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      repeat normalize_bound_var_in_ctx.
      assert (Hsuf :
                cc_approx_exp pr cenv clo_tag k (e, def_funs f2 f2 rho1 rho1)
                              (C0 |[ Ce |[ e'0 ]| ]|, def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2')
                                                   (M.set Γ' (Vconstr c'0 v') rho2'))).
      { edestruct make_closures_ctx_to_rho as [rho2'' Htp_rho']; eauto.
        - eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
        - intros Hc. eapply H4. now eauto.
        - eapply Closure_conversion_fundefs_correct; eauto. 
          + intros f Hfin. inv Hfin; eauto.
          + intros f Hfin. inv Hfin; eauto.
          + eapply binding_in_map_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption.
          + eapply Disjoint_Included_l.
            eapply make_closures_image_Included; eassumption.
            eauto with Ensembles_DB.
          + now apply Disjoint_Empty_set_r. 
          + eapply closure_conversion_fundefs_Same_set_image. eassumption.
          + eapply make_closures_injective; [| eassumption ].
            eapply Disjoint_Included_r; [| eassumption ].
            apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          + eapply make_closures_injective; [| eassumption ].
            eapply Disjoint_Included_r; [| eassumption ].
            apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          + intros Hc. eapply H4. now eauto.
          + intros Hc. eapply H4. now eauto.
          + intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H6. constructor; [| now eauto ].
            eapply make_closures_image_Included. eassumption. eassumption.
          + intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H6. constructor; [| now eauto ].
            eapply make_closures_image_Included. eassumption. eassumption.
          + edestruct Hvar as [vs' [Hgetlist' Hall]]; eauto.
            intros x N v _ _ Hnth Hget. rewrite Hget' in Hgetlist'; inv Hgetlist'.
            edestruct (@getlist_nth_get val) as [v' [Hnth' Hget'']].
            now apply Hgetlist. eassumption.
            edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
            eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
        - intros g' Hin. eexists. now rewrite def_funs_eq.
        - edestruct make_closures_correct with
          (Scope := Union var (name_in_fundefs f2) Scope)
            (Γ := Γ)
            (rho1 := def_funs f2 f2 rho1 rho1)
            (rho2 := def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2')
                              (M.set Γ' (Vconstr c'0 v') rho2'))
            as [Hcc'' [Hfun'' Henv'']].
          + eauto.
          + eauto.
          + intros Hc. eapply Hnin. constructor.
            now eapply name_in_fundefs_bound_var_fundefs.
          + intros Hc. eapply H4. now eauto.
          + eapply Included_Union_l.
          + eapply Disjoint_Included_r; [| eassumption ].
            apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          + eapply cc_approx_env_P_def_funs_not_In_P_l.
            now eauto with Ensembles_DB.
            eapply cc_approx_env_P_def_funs_not_In_P_r.
            erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); [| eassumption ].
            eapply Disjoint_Included_r.
            now eapply make_closures_image_Included; eauto.
            now eauto 7 with Ensembles_DB.
            eapply cc_approx_env_P_set_not_in_P_r.
            eapply cc_approx_env_P_antimon; [ eassumption |]...
            intros Hin. inv Hin. inv H. eauto. eapply H4. eauto.
          + eapply Fun_inv_def_funs.
            * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
              eapply H6. constructor.
              eapply make_closures_image_Included. eassumption. eassumption.
              rewrite !Union_assoc...
            * intros Hc. eapply Hnin. eapply Included_Union_l.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply Disjoint_Included_r; [| eassumption ].
              apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
            * erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].   
              eapply Disjoint_Included_r;
                [ eapply make_closures_image_Included; eassumption |]...
            * eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | ].
              intros Hc. eapply H4. now eauto.
              intros Hc. subst. eapply H4. constructor. now eauto.
              now eauto. now eauto.
          + eapply FV_inv_def_funs.
            * intros Hc. eapply Hnin. constructor. 
              now eapply name_in_fundefs_bound_var_fundefs.
            * intros Hc.
              erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
              eapply H6. constructor.
              eapply make_closures_image_Included. eassumption. eassumption.
              rewrite !Union_assoc. now apply Included_Union_r.
            * eapply  FV_inv_set_r.
              intros Hc. subst. eapply H4. constructor; eauto.
              eassumption. 
          + eapply Closure_conversion_fundefs_correct with (c := c'0) ; eauto.
            * intros f Hfin. inv Hfin; eauto.
            * intros f Hfin. inv Hfin; eauto.
            * eapply binding_in_map_antimon; [| eassumption ].
              intros x H. eapply Free_Efun2. eassumption.
            * eapply Disjoint_Included_l;
              [ eapply make_closures_image_Included; eassumption |]...
            * now apply Disjoint_Empty_set_r.
            * eapply closure_conversion_fundefs_Same_set_image. eassumption.
            * eapply make_closures_injective; [| eassumption].
              eapply Disjoint_Included_r; [| eassumption ].
              apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
            * eapply make_closures_injective; [| eassumption].
              eapply Disjoint_Included_r; [| eassumption ].
              apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
            * intros Hc. eapply H4. now eauto.
            * intros Hc. eapply H4. now eauto.
            * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].     
              eapply H6. constructor.
              eapply make_closures_image_Included. eassumption.
              eassumption. now eauto.
            * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].     
              eapply H6. constructor.
              eapply make_closures_image_Included. eassumption.
              eassumption. now eauto.
            * edestruct Hvar as [vs' [Hgetlist' Hall]]; eauto.
              intros x N v _ _ Hnth Hget. rewrite Hget' in Hgetlist'; inv Hgetlist'.
              edestruct (@getlist_nth_get val) as [v' [Hnth' Hget'']].
              now apply Hgetlist. eassumption.
              edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
              eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
          + eauto.
          + eapply ctx_to_rho_cc_approx_exp; eauto.
            eapply IHe; eauto. 
            * eapply binding_in_map_antimon.
              eapply Included_trans. now eapply occurs_free_Efun_Included.
              rewrite Union_commut. now apply Included_refl.
              apply binding_in_map_def_funs. eassumption.
            * intros f Hfin; eauto.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l;
                 [ apply image_monotonic | now apply Hd ]]... }
      intros v1' c1' Hleq' Hstep'. inv Hstep'.
      edestruct Hsuf as [v2' [c2' [Hstep2' Hcc2']]]; [| eassumption |]; eauto.
      repeat eexists; eauto. econstructor; eauto. econstructor; eauto.
    - (* Case Eapp *)
      inv Hcc.
      intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      simpl. rewrite H4, H5. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H4, H5. reflexivity.
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
      destruct (getlist ys' rho2') eqn:Hgetlist'; try discriminate. inv Hget'.
      inv Happ'. rewrite cc_approx_val_eq in H6. destruct v0; try contradiction.
      eapply ctx_to_rho_cc_approx_exp with (e := Eapp v t l); eauto.
      * intros v1' c1' Hleq' Hstep'. inv Hstep'.
        rewrite H4 in H8. inv H8. rewrite H5 in H15; inv H15.
        destruct l1; try contradiction. destruct v0, l1; try contradiction.
        destruct v2; try contradiction.
        rewrite H17 in H7. inv H7. 
        rewrite H11 in H20. inv H20. eapply bstep_e_deterministic in H21; eauto. inv H21.
        assert (Hlen := List_util.Forall2_length _ _ _ H9).
        edestruct H6 with (vs2 := l0) (j := k - 1)
          as [Γ' [xs2 [e2 [rho2'' [Heq [Hfind [Hset Hyp]]]]]]]; eauto.
        edestruct Hyp as [v2' [c'2 [Hstep2 Hcc']]]; try eassumption. omega.
        eapply List_util.Forall2_monotonic; [| eassumption ].
        intros. eapply cc_approx_val_monotonic. eassumption. omega. omega.
        subst. repeat eexists. econstructor. eassumption. reflexivity.
        econstructor. rewrite M.gso. eassumption.
        intros Hc; subst. eapply project_vars_not_In_free_set; [ now eauto | now eauto | ].
        constructor. now eapply H10. rewrite FromList_cons. now eauto.
        reflexivity.
        eapply BStep_app. rewrite M.gso. rewrite M.gss. reflexivity.
        now eauto.
        simpl. rewrite M.gss. rewrite getlist_set_neq. rewrite getlist_set_neq.
        rewrite Hgetlist'. reflexivity. 
        intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption. 
        constructor. eapply H10. rewrite FromList_cons. now eauto.
        intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption.
        constructor. now eauto. rewrite FromList_cons. now eauto.
        eassumption. simpl in Hset. eauto. eassumption.
        eapply cc_approx_val_monotonic. eassumption. omega.
      * econstructor; eauto.
    (* Case Eprim *)
    - inv Hcc.
      intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H10; eauto.
      inv H10. edestruct Prim_axiom_cc as [vs' [Hf' Hcc]]; eauto.
      repeat normalize_bound_var_in_ctx.
      edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | eassumption | | | | eassumption | eassumption | eassumption | ]. 
      + eapply cc_approx_env_P_extend; [| eassumption ].
        eapply cc_approx_env_P_antimon; [ eassumption |]...
      + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        eapply occurs_free_Eprim_Included. 
      + intros f Hfin. eauto.
      + eapply Disjoint_Included_r;
        [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]]...
      + eapply Fun_inv_set_In_Scope_l. now eauto.
        eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_mon; [ | now eauto ]...
      + eapply FV_inv_set_In_Scope_l. now constructor.
        eapply FV_inv_set_r. intros Hc. eapply Hnin.
        subst. now eauto. now eapply FV_inv_extend_Scope.
      + repeat eexists; [| eassumption ]. econstructor; eauto.
    - inv Hcc.
      intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      edestruct project_var_correct as [Hnin' [Happ [Hfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      eapply ctx_to_rho_cc_approx_exp; eauto.
      eapply cc_approx_exp_halt_compat. eassumption. now econstructor; eauto.
  Qed.

End Closure_conversion_correct. 
