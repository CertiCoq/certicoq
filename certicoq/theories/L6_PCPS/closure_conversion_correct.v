Require Import cps cps_util set_util hoisting identifiers ctx
        Ensembles_util closure_conversion eval logical_relations.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.


(* It should be the case that variables in FV are
 * shadowed by variables with the same name in xs *)

(** Invariant about closure environments. *)
Definition closure_env k rho Scope Funs vs FVs : Prop :=
  forall (x : var) N (v : val),
    ~ In _ Scope x ->
    ~ In _ Funs x -> 
    nthN FVs N = Some x ->
    M.get x rho = Some v ->
    exists (v' : val),  nthN vs N = Some v' /\
                   cc_approx_val k v v'.

(** Invariant about the free variables *) 
Definition env_inv k rho rho' Scope Funs Γ FVs : Prop :=
  exists tau t vs,
    M.get Γ rho' = Some (Vconstr tau t vs) /\
    closure_env k rho Scope Funs vs FVs.

(** Invariant about the functions in the current function definition *)
Definition Fun_inv k (rho rho' : env) Scope Funs Γ : Prop :=
  exists tau t vs,
    M.get Γ rho' = Some (Vconstr tau t vs) /\
    forall f v,
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho = Some v  ->
      exists  rho1 B1 f1 rho2 B2 f2 tau' t',
        v = (Vfun rho1 B1 f1) /\
        M.get f rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val k (Vfun rho1 B1 f1)
                      (Vconstr tau' t' [(Vfun rho2 B2 f2) ; (Vconstr tau t vs)]).

(* XXX : deprecated *)
Lemma Fun_inv_extend' k rho rho' Scope Funs Γ
      f rho1 B1 f1 rho2 B2 f2 tau t vs:
  Fun_inv k rho (M.set Γ (Vconstr tau t vs) rho') Scope Funs Γ ->
  f <> Γ ->
  (exists tau' t',
     cc_approx_val k (Vfun rho1 B1 f1)
                   (Vconstr tau' t' [(Vfun rho2 B2 f2) ; (Vconstr tau t vs)])) ->
  Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
          (M.set Γ (Vconstr tau t vs) (M.set f  (Vfun rho2 B2 f2) rho'))
          Scope (Union _ (Singleton _ f) Funs) Γ.
Proof.
  intros Hinv Hneq Hv. edestruct Hinv as [tau' [t' [vs' [Hget Hyp]]]].
  rewrite M.gss in Hget. inv Hget.
  do 3 eexists. rewrite M.gss. split; [ reflexivity |].
  intros f' v Hnin Hin Hget'.
  rewrite M.gsspec in Hget'. destruct (Coqlib.peq f' f); subst.
  - inv Hget'.
    edestruct Hv as [tau1 [t1 Happrox]]; eauto.
    repeat eexists. rewrite M.gso; eauto. now rewrite M.gss; eauto.
    eassumption.
  - edestruct Hyp as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [tau2 [t2 [Heq [Hget2 Happrox]]]]]]]]]];
    subst; eauto.
    + inv Hin; eauto. inv H. congruence.
    + repeat eexists; eauto.
      rewrite M.gsspec in Hget2.
      destruct (Coqlib.peq f' Γ); subst.
      * inv Hget2.
      * do 2 (rewrite M.gso; eauto).
Qed.

Lemma Fun_inv_extend k rho rho' Scope Funs Γ
      f rho1 B1 f1 rho2 B2 f2 tau t vs:
  Fun_inv k rho rho' Scope Funs Γ ->
  f <> Γ ->
  M.get Γ rho' = Some (Vconstr tau t vs) ->
  (exists tau' t',
     cc_approx_val k (Vfun rho1 B1 f1)
                   (Vconstr tau' t' [(Vfun rho2 B2 f2) ; (Vconstr tau t vs)])) ->
  Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
          (M.set f  (Vfun rho2 B2 f2) rho')
          Scope (Union _ (Singleton _ f) Funs) Γ.
Proof.
  intros Hinv Hneq Hget Hv. edestruct Hinv as [tau' [t' [vs' [Hget' Hyp]]]].
  do 3 eexists. rewrite M.gso; eauto. split; [ eassumption |].
  intros f' v Hnin Hin Hget''. rewrite Hget in Hget'. inv Hget'.
  rewrite M.gsspec in Hget''. destruct (Coqlib.peq f' f); subst.
  - inv Hget''.
    edestruct Hv as [tau1 [t1 Happrox]]; eauto.
    repeat eexists. rewrite M.gss; eauto.
    eassumption.
  - edestruct Hyp as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [tau2 [t2 [Heq [Hget2 Happrox]]]]]]]]]];
    subst; eauto.
    + inv Hin; eauto. inv H. congruence.
    + repeat eexists; eauto.
      rewrite M.gso; eauto.
Qed.

Lemma closure_conversion_fundefs_find_def Funs FVs B1 B2 f t1 xs e1 :
  Closure_conversion_fundefs Funs FVs B1 B2 ->
  find_def f B1 = Some (t1, xs, e1) ->
  exists t2 Γ' e2,
    ~ In var (Union var Funs (Union _ (FromList xs) (bound_var e1))) Γ' /\
    find_def f B2 = Some (t2, Γ' :: xs, e2) /\
    Closure_conversion (FromList xs) Funs Γ' FVs e1 e2.
Proof.
  intros Hcc Hdef. induction Hcc.
  - simpl in Hdef. destruct (M.elt_eq f f0) eqn:Heq; subst.
    + inv Hdef. repeat eexists; eauto.
      simpl. rewrite Heq. reflexivity.
    + edestruct IHHcc as [t2 [Γ'' [e2 [Hnin [Hfind Hcc']]]]]; eauto.
      repeat eexists; eauto. simpl; rewrite Heq. eassumption.
  - inv Hdef.
Qed.

Lemma cc_approx_env_P_set_not_in_P_r
      (x : var) (v : val) (P : Ensemble var) (k : nat) (rho1 rho2 : env):
  cc_approx_env_P P k rho1 rho2 ->
  Disjoint var P (Singleton var x) -> cc_approx_env_P P k rho1 (M.set x v rho2).
Proof.
  intros Hcc HD y HP v' Hget.
  edestruct (Coqlib.peq x y); subst.
  - exfalso. eapply HD; eauto.
  - edestruct Hcc as [v2 [Hget' Hcc']]; eauto.
    eexists. rewrite M.gso. split; eauto.
    congruence.
Qed.

Lemma Fun_inv_rename k rho1 rho2 Scope Funs Γ Γ' v :
  ~ In _ Funs Γ ->  ~ In _ Funs Γ' ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs Γ ->
  Fun_inv k rho1 (M.set Γ' v rho2) Scope Funs Γ'.
Proof.
  intros Hnin Hnin' [tau [t [vs [Hget H]]]].
  rewrite M.gss in Hget. inv Hget.
  do 3 eexists. rewrite M.gss; split; [ now eauto |].
  intros f v Hninf Hin Hget.
  edestruct H as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hget' Happrox']]]]]]]]]]; eauto.
  rewrite M.gsspec in Hget'.
  destruct (Coqlib.peq f Γ); subst; [ contradiction |].
  destruct (Coqlib.peq f Γ'); subst; [ contradiction |].
  repeat eexists; eauto. rewrite M.gso; eauto.
Qed.

Lemma Fun_inv_mon k rho1 rho2 Scope Scope' Funs Γ :
  Included _ Scope Scope' -> 
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  Fun_inv k rho1 rho2 Scope' Funs Γ.
Proof.
  intros Hincl [tau [t [vs [Hget H]]]].
  do 3 eexists. split; [ now eauto |].
  intros f v Hninf Hin Hget'.
  now eapply H; eauto. 
Qed.

Lemma Fun_inv_set_In_Scope_l k rho1 rho2 Scope Funs Γ x v :
  In _ Scope x ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  Fun_inv k (M.set x v rho1) rho2 Scope Funs Γ.
Proof.
  intros Hin [tau [t [vs [Hget H]]]].
  do 3 eexists. split; [ now eauto |].
  intros f v' Hninf Hin' Hget'.
  rewrite M.gsspec in Hget'.
  destruct (Coqlib.peq f x); subst; [ contradiction |].
  edestruct H as [v'' [tau' [t' [Hget'' Happrox']]]]; eauto.
Qed.

Lemma Fun_inv_set_In_Scope_r k rho1 rho2 Scope Funs Γ x v v' :
  In _ Scope x ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs Γ ->
  Fun_inv k rho1 (M.set Γ v (M.set x v' rho2)) Scope Funs Γ.
Proof.
  intros Hin [tau [t [vs [Hget H]]]].
  rewrite M.gss in Hget. inv Hget.
  do 3 eexists. rewrite M.gss; split; [ now eauto |].
  intros f v1 Hninf Hin' Hget.
  edestruct H as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hget' Happrox']]]]]]]]]]; eauto.
  rewrite M.gsspec in Hget'.
  destruct (Coqlib.peq f Γ).
  - subst. inv Hget'.
  - repeat eexists. eassumption.
    rewrite M.gso; eauto.
    destruct (Coqlib.peq f x); subst; [ contradiction |].
    rewrite M.gso; eauto. eassumption.
Qed.

Lemma Fun_inv_set_In_Scope_r_not_Γ k rho1 rho2 Scope Funs Γ x v :
  In _ Scope x ->
  x <> Γ ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  Fun_inv k rho1 (M.set x v rho2) Scope Funs Γ.
Proof. 
  intros Hin Hneq [tau [t [vs [Hget H]]]].
  do 3 eexists. rewrite M.gso; [| now eauto ].
  split; [ now eauto |].
  intros f v' Hninf Hin' Hget'.
  edestruct H
    as [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hget'' Happrox']]]]]]]]]]; eauto.
  destruct (Coqlib.peq f x); subst; [ contradiction |].
  do 8 eexists. rewrite M.gso; eauto.
Qed.

Lemma Fun_inv_set_not_In_Funs_r_not_Γ k rho1 rho2 Scope Funs Γ x v :
  ~ In _ Funs x ->
  x <> Γ ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  Fun_inv k rho1 (M.set x v rho2) Scope Funs Γ.
Proof. 
  intros Hin Hneq [tau [t [vs [Hget H]]]].
  do 3 eexists. rewrite M.gso; [| now eauto ].
  split; [ now eauto |].
  intros f v' Hninf Hin' Hget'.
  edestruct H
    as [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hget'' Happrox']]]]]]]]]]; eauto.
  destruct (Coqlib.peq f x); subst; [ contradiction |].
  do 8 eexists. rewrite M.gso; eauto.
Qed.


Lemma Fun_inv_setlist_In_Scope_l k rho1 rho1' rho2 Scope Funs Γ xs vs :
  Included _ (FromList xs) Scope ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  setlist xs vs rho1 = Some rho1' ->
  Fun_inv k rho1' rho2 Scope Funs Γ.
Proof.
  revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
  - intros Hinc Hfun Hset. inv Hset.
    destruct vs; [ congruence | discriminate ].
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

Lemma Fun_inv_setlist_In_Scope_r k rho1 rho2 rho2' Scope Funs Γ xs vs v :
  Included _ (FromList xs) Scope ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs Γ ->
  setlist xs vs rho2 = Some rho2' ->
  Fun_inv k rho1 (M.set Γ v rho2') Scope Funs Γ.
Proof.
  revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
  - intros Hinc Hfun Hset. inv Hset.
    destruct vs; [ congruence | discriminate ].
  - intros Hinc Hfun Hset.
    simpl in Hset.
    destruct vs; [ discriminate | ].
    destruct (setlist xs vs rho2) eqn:Heq; [ | discriminate ]. inv Hset.
    eapply Fun_inv_set_In_Scope_r.
    + rewrite FromList_cons in Hinc. 
      eapply Hinc. eauto.
    + eapply IHxs; eauto. rewrite FromList_cons in Hinc. 
      eapply Included_trans; [| eassumption ].
      eapply Included_Union_r.
Qed.

Lemma Closure_conversion_fundefs_name_in_fundefs Funs FVs B1 B2  :
  Closure_conversion_fundefs Funs FVs B1 B2 ->
  Same_set _ (name_in_fundefs B1) (name_in_fundefs B2).
Proof.
  intros Hcc. induction Hcc; simpl.
  - eapply Same_set_Union_compat.
    now eapply Same_set_refl.
    now eauto.
  - now apply Same_set_refl.
Qed.

Lemma Fun_inv_reset k rho rho' B v Scope Funs Γ :
  ~ In _ (name_in_fundefs B) Γ ->
  Fun_inv k rho
          (def_funs B B (M.set Γ v rho') (M.set Γ v rho')) Scope Funs Γ ->
  Fun_inv k rho
          (M.set Γ v (def_funs B B (M.set Γ v rho') (M.set Γ v rho')))
          Scope Funs Γ.
Proof. 
  intros Hin [tau [t [vs [Hget Hfun]]]]. 
  rewrite def_funs_neq in Hget; eauto. rewrite M.gss in Hget.
  inv Hget.
  do 3 eexists. rewrite M.gss. split; eauto.
  intros f v Hnin Hin' Hget.
  edestruct Hfun as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hget' Hcc]]]]]]]]]]; eauto.
  subst. eapply def_funs_spec in Hget'.
  destruct Hget' as [[Hname Heq] | [Hname Hget']].
  - inv Heq. repeat eexists; eauto.
    rewrite M.gso.
    rewrite def_funs_eq. reflexivity. eassumption.
    intros Hc; subst; eauto.
  - rewrite M.gsspec in Hget'.
    destruct (Coqlib.peq f Γ).
    + subst. inv Hget'.
    + repeat eexists; eauto. rewrite M.gso. 
      rewrite def_funs_neq; eauto. 
      rewrite M.gso. eassumption.
      intros Hc; subst; eauto.
      intros Hc; subst; eauto.
Qed.

Lemma get_def_funs_In_names B' B f rho :
  In var (name_in_fundefs B) f ->
  exists v : val, M.get f (def_funs B' B rho rho) = Some v.
Proof.
  induction B; intros Hin; inv Hin. 
  - inv H. eexists. simpl. rewrite M.gss. eauto.
  - edestruct IHB as [v' Heq]; eauto.
    destruct (Coqlib.peq f v) eqn:Heq'.
    + eexists. simpl. now rewrite M.gsspec, Heq'.
    + eexists. simpl. rewrite M.gsspec, Heq'.
      eassumption.
Qed.

Lemma get_setlist_In_xs x xs vs rho rho' :
  In var (FromList xs) x ->
  setlist xs vs rho = Some rho' ->
  exists v : val, M.get x rho' = Some v.
Proof.
  revert rho rho' vs. induction xs; intros rho rho' vs Hin Hset.
  - rewrite FromList_nil in Hin. exfalso.
    eapply not_In_Empty_set. eassumption. 
  - rewrite FromList_cons in Hin.
    destruct vs; try discriminate.    
    simpl in Hset. destruct (setlist xs vs rho) eqn:Hsetlist; try discriminate.
    inv Hset. inv Hin.
    + inv H. eexists. rewrite M.gss. reflexivity.
    + destruct (Coqlib.peq x a); subst.
      * eexists. now rewrite M.gss.
      * edestruct IHxs; eauto.
        eexists. simpl. rewrite M.gso; eauto. 
Qed.

Definition vars_in_env S (rho : env) : Prop :=
  forall x, In _ S x -> exists v, M.get x rho = Some v. 

Inductive unique_functions : fundefs -> Prop :=
| Fnil_un :
    unique_functions Fnil
| Fcons_un :
    forall f tau xs e B,
      unique_functions B ->
      ~ In _ (name_in_fundefs B) f ->
      unique_functions (Fcons f tau xs e B).

Definition fundefs_names_unique (e : exp) : Prop :=
  forall B, funs_in_exp B e -> unique_functions B.

Definition fundefs_names_unique_fundefs (B : fundefs) : Prop :=
  forall B', funs_in_fundef B' B \/ B' = B -> unique_functions B'.

Lemma vars_in_env_antimon S S' rho :
  Included _ S' S ->
  vars_in_env S rho ->
  vars_in_env S' rho.
Proof.
  intros Hin Hv x Hs. eauto.

Qed.

Lemma vars_in_env_extend x v S rho :
  vars_in_env S rho ->
  vars_in_env (Union _ S (Singleton _ x)) (M.set x v rho).
Proof. 
  intros H x' Hs. inv Hs.
  - edestruct H; eauto.
    destruct (Coqlib.peq x' x) eqn:Heq'.
    + eexists. simpl. now rewrite M.gsspec, Heq'.
    + eexists. simpl. rewrite M.gsspec, Heq'.
      eassumption.
  - inv H0. eexists. rewrite M.gss. eauto.
Qed.

Instance Decidable_FromList (l : list var) : Decidable (FromList l). 
Proof. 
  constructor. intros x. induction l. 
  - right. intros H. inv H. 
  - destruct (Coqlib.peq a x).
    + subst. left. constructor. eauto.
    + destruct IHl. left. now constructor 2.
      right. intros Hc. eapply H. inv Hc; eauto.
      congruence.
Qed.

Lemma vars_in_env_setlist xs vs S rho rho' :
  vars_in_env S rho ->
  setlist xs vs rho = Some rho' ->
  vars_in_env (Union _ (FromList xs) S) rho'.
Proof.
  intros H Hset x' Hs.
  destruct (Decidable_FromList xs). destruct (Dec x').
  - eapply get_setlist_In_xs; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite <- setlist_not_In; eauto.
Qed.

Lemma vars_in_env_def_funs B' B rho S  :
  vars_in_env S rho ->
  vars_in_env (Union _ (name_in_fundefs B) S) (def_funs B' B rho rho).
Proof.
  intros H x' Hs.
  destruct (Decidable_name_in_fundefs B). destruct (Dec x').
  - eapply get_def_funs_In_names; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite def_funs_neq; eauto.
Qed.

Lemma closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
      Scope Γ FVs Funs' FVs' t tau vs:
  (* The IH *)
  (forall m : nat,
     m < k ->
     forall (e : exp) (rho rho' : env) (e' : exp)
       (Scope Funs : Ensemble var) (Γ : var) (FVs : list M.elt),
       cc_approx_env_P Scope m rho rho' ->
       ~ In var (bound_var e) Γ ->
       vars_in_env (occurs_free e) rho ->
       fundefs_names_unique e ->
       Fun_inv m rho rho' Scope Funs Γ ->
       env_inv m rho rho' Scope Funs Γ FVs ->
       Closure_conversion Scope Funs Γ FVs e e' ->
       cc_approx_exp m (e, rho) (e', rho')) ->
  Same_set _ (occurs_free_fundefs B1) (FromList FVs) ->
  fundefs_names_unique_fundefs B1 ->
  vars_in_env (occurs_free_fundefs B1) rho ->
  Closure_conversion_fundefs (name_in_fundefs B1) FVs B1 B2 ->
  Closure_conversion_fundefs Funs' FVs' B1' B2' ->
  ~ In _ (name_in_fundefs B1) Γ ->
  ~ In _ (name_in_fundefs B1') Γ ->
  closure_env k rho (Empty_set _) (Empty_set _) vs FVs ->
  Fun_inv k (def_funs B1 B1' rho rho)
          (def_funs B2 B2' (M.set Γ (Vconstr tau t vs) rho') (M.set Γ (Vconstr tau t vs) rho'))
          Scope (name_in_fundefs B1') Γ.
Proof.
  revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t tau vs.
  induction k as [k IHk] using lt_wf_rec1.
  induction B1'; 
    intros rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t' tau' vs
           IHe Hs Hun Hfv Hcc Hcc' Hnin Hnin' Henv.
  - inv Hcc'. simpl.
    eapply Fun_inv_extend.
    + eapply IHB1'; eauto.
      intros Hc. apply Hnin'.
      simpl; eauto.
    + intros Hc. apply Hnin'. subst. simpl; eauto.
    + rewrite def_funs_neq.
      rewrite M.gss. reflexivity.
      simpl in Hnin'.
      rewrite Closure_conversion_fundefs_name_in_fundefs in Hnin';
        [now eauto | eassumption ].
    + exists tau', t.
      rewrite cc_approx_val_eq.
      intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
      edestruct setlist_length
      with (rho' := def_funs B2 B2 (M.set Γ (Vconstr tau' t' vs) rho')
                             (M.set Γ (Vconstr tau' t' vs) rho')) as [rho2' Hset'].
      eassumption. now eauto.
      edestruct closure_conversion_fundefs_find_def
        as [t2 [Γ'' [e2 [Hnin'' [Hfind' Hcc']]]]]; [| eassumption |]. eassumption.
      exists t2, Γ'', xs1. do 2 eexists.
      split. eassumption. split.
      simpl. rewrite Hset'. reflexivity.
      intros Hlt Hall.  
      eapply IHe; try eassumption.  
      * eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_setlist_l with (P1 := Empty_set _); eauto. 
        eapply cc_approx_env_Empty_set.
        intros x H1 H2. contradiction.
        constructor. intros x Hc. inv Hc. inv H0. eauto.
      * intros Hc. apply Hnin''. eauto.
      * eapply vars_in_env_antimon.
        eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
        eapply vars_in_env_setlist; [| now eauto ].
        eapply vars_in_env_def_funs. eassumption.
      * intros B Hin. eapply Hun. left. 
        eapply fun_in_fundefs_funs_in_fundef; eauto.
        eapply find_def_correct. eassumption.
      * assert
          (Fun_inv j (def_funs B1 B1 rho rho)
                   (def_funs B2 B2 (M.set Γ (Vconstr tau' t' vs) rho')
                             (M.set Γ (Vconstr tau' t' vs) rho'))
                   (FromList xs1) (name_in_fundefs B1) Γ).
        { eapply IHk; try eassumption.
          - intros. eapply IHe; eauto. omega. 
          - intros x1 N v1 Hnin1 Hnin2 Hnth Hget.
            edestruct Henv as [v2 [Hnth' Happ']]; eauto.
            eexists; split; eauto. eapply cc_approx_val_monotonic.
            eassumption. omega. } 
        eapply Fun_inv_rename with (Γ := Γ); eauto.
        eapply Fun_inv_setlist_In_Scope_l; [ now apply Included_refl | |].
        eapply Fun_inv_setlist_In_Scope_r; [ now apply Included_refl | |]. 
        eapply Fun_inv_reset; [| eassumption ].
        rewrite <- Closure_conversion_fundefs_name_in_fundefs; [ | eassumption ].
        now eauto. now eauto. now eauto.
      * do 3 eexists. split.
        rewrite M.gss. reflexivity.
        intros x N v1 Hnin1 Hnin2 Hnth Hget'. 
        edestruct Henv as [v' [Hnth'' Hcc'']]; eauto.
        intros Hc. now inv Hc.
        intros Hc. now inv Hc.
        erewrite <- def_funs_neq.
        erewrite setlist_not_In. eassumption.
        now eauto. now eauto. now eauto.
        eexists; eauto. split. eassumption.
        eapply cc_approx_val_monotonic. eassumption. omega.
  - do 3 eexists.
    rewrite def_funs_neq. rewrite M.gss. split; eauto.
    intros. inv H0. inv Hcc'. simpl. eauto.
Qed.

(* Fixpoint ctx_as_env (rho : env) v C : env := *)
(*   match C with *)
(*     | Hole_c => rho *)
(*     | Econstr_c x tau t [f; env] C => *)
(*       match M.get f rho with *)
(*         | Some v1 => *)
(*           ctx_as_env (M.set x (Vconstr tau t [v1; v]) rho) v C *)
(*         | _ => ctx_as_env rho v C *)
(*       end *)
(*     | _ => rho *)
(*   end. *)

(* Lemma ctx_as_env_comp_ctx_f rho v C1 C2: *)
(*   ctx_as_env rho v (comp_ctx_f C1 C2) = *)
(*   ctx_as_env (ctx_as_env rho v C1) v C2. *)
(* Admitted. *)
(*   (* Proof. *) *)
(* (*   revert rho. induction C1; intros rho; simpl. *) *)
(* (*   - reflexivity. *) *)
(* (*   - rewrite IHC1 with (rho := . Focus 3.   *) *)

(* Lemma ctx_as_env_comp_ctx_f_Econstr Γ v x v' tau t B B' rho C : *)
(*   Γ <> x -> *)
(*   ctx_as_env *)
(*     (M.set Γ v *)
(*            (M.set x v' (def_funs B B' rho rho))) *)
(*     v (comp_ctx_f C (Econstr_c x tau t [x; Γ] Hole_c)) = *)
(*   M.set x (Vconstr tau t [v'; v]) *)
(*         (ctx_as_env *)
(*            (M.set Γ v *)
(*                   (M.set x v' (def_funs B B' rho rho))) *)
(*            v C). *)
(* Proof. *)
(*   intros Hneq. rewrite ctx_as_env_comp_ctx_f. simpl. *)
(*   rewrite M.gso; eauto. now rewrite M.gss. *)
(*   - rewrite IHC. *)


Lemma env_inv_extend_In_Scope_l k rho rho' x v Scope Funs FVs Γ :
  In var Scope x ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k (M.set x v rho) rho' Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. intros y n v' Hnin Hnin' Hnth Hget'.
  rewrite M.gsspec in Hget'. destruct (Coqlib.peq y x); subst.
  - contradiction. 
  - eauto. 
Qed.

Lemma env_inv_extend_In_Scope_r k rho rho' x v Scope Funs FVs Γ :
  In var Scope x ->
  x <> Γ ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k rho (M.set x v rho') Scope Funs Γ FVs.
Proof.
  intros Hin Hneq HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. rewrite M.gso; eauto.
Qed.

Lemma nthN_In {A} (l : list A) n v :
  nthN l n = Some v ->
  List.In v l.
Proof. 
  revert n v. induction l; intros n v Hnth.
  - inv Hnth.
  - destruct n. inv Hnth.
    now constructor.
    constructor 2. eapply IHl. eauto. 
Qed. 

Lemma env_inv_extend_not_In_FVs_l k rho rho' x v Scope Funs Γ FVs :
  ~ List.In x FVs ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k (M.set x v rho) rho' Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. intros y n v' Hnin Hnin' Hnth Hget'.
  rewrite M.gsspec in Hget'. destruct (Coqlib.peq y x); subst.
  - inv Hget. eapply H; eauto.
    eapply nthN_In in Hnth.
    contradiction.
  - eauto.
Qed.

Lemma env_inv_extend_r k rho rho' x v Scope Funs Γ FVs :
  x <> Γ ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k rho (M.set x v rho') Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. 
  rewrite M.gso; eauto. 
Qed.

Lemma env_inv_extend_Scope k rho rho' Scope Funs Γ FVs x :
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k rho rho' (Union _ (Singleton _ x) Scope) Funs Γ FVs.
Proof.
  intros [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. 
  intros y N v Hnin Hnin' Hnth Hget'. eapply H; eauto.
Qed.

Lemma cc_approx_env_P_not_in_P_r P k rho rho' x v :
  cc_approx_env_P P k rho rho' ->
  ~ In _ P x ->
  cc_approx_env_P P k rho (M.set x v rho').
Proof. 
  intros Hcc Hnin y Py v' Hget.
  edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
  exists v''. rewrite M.gsspec.
  destruct (Coqlib.peq y x); subst.
  - contradiction.
  - eauto.
Qed.


Inductive ctx_to_rho : exp_ctx -> env -> env -> Prop :=
| Hole_c_to_rho :
    forall rho,
      ctx_to_rho Hole_c rho rho
| Eproj_c_to_rho :
    forall rho rho' tau t y tau' N Γ C vs v,
      M.get Γ rho = Some (Vconstr tau t vs) ->
      nthN vs N = Some v ->
      ctx_to_rho C (M.set y v rho) rho' ->
      ctx_to_rho (Eproj_c y tau' N Γ C) rho rho'
| Econstr_c_to_rho :
    forall rho rho' tau t y  x Γ C v1 v2,
      M.get Γ rho = Some v1 ->
      M.get x rho = Some v2 ->
      ctx_to_rho C (M.set y (Vconstr tau t [v2; v1]) rho) rho' ->
      ctx_to_rho (Econstr_c y tau t [x; Γ] C) rho rho'.

  
Lemma project_var_correct k rho1 rho2 rho2'
      Scope Funs Γ FVs x x' C S S'  :
  project_var Scope Funs Γ FVs S x x' C S' ->
  cc_approx_env_P Scope k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  env_inv k rho1 rho2 Scope Funs Γ FVs ->
  ctx_to_rho C rho2 rho2' ->
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  ~ In _ S' x' /\
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs Γ /\
  env_inv k rho1 rho2' Scope Funs Γ FVs /\
  cc_approx_var_env k rho1 rho2' x x'.
Proof.
  intros Hproj Hcc Hfun Henv Hctx Hd.
  inv Hproj. 
  - inv Hctx. repeat split; eauto. intros Hc. eapply Hd; eauto.
  - inv Hctx. inv H12.
    repeat split; eauto.
    + intros Hc. inv Hc. eauto.
    + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
      constructor. intros y Hc. eapply Hd.
      inv Hc. inv H3. eauto. 
    + (* TODO : make lemma *)
      edestruct Hfun as [tau' [t' [vs' [Hget Hfun']]]].
      rewrite Hget in H10; inv H10.
      do 3 eexists. rewrite M.gso; [ | now intros Heq; subst; eapply Hd; eauto ].
      split; eauto. intros f v Hnin Hin Hget''.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hget' Hcc']]]]]]]]]]; eauto.
      subst. repeat eexists; eauto.
      rewrite M.gso. eassumption. 
      intros Hc. subst; eapply Hd; eauto.
    + eapply env_inv_extend_r. now intros Heq; subst; eapply Hd; eauto.
      eassumption.
    + intros v Hget. eexists. rewrite M.gss. split; eauto.
      edestruct Hfun as [tau' [t' [vs' [Hget' Hfun']]]].
      rewrite Hget' in H10; inv H10.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hget'' Hcc']]]]]]]]]]; eauto.
      subst. rewrite Hget'' in H11. inv H11.
      now rewrite cc_approx_val_eq in *.
  - inv Hctx. inv H12.
    repeat split; eauto.
    + intros Hc. inv Hc. eauto.
    + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
      constructor. intros y Hc. eapply Hd.
      inv Hc. inv H4. eauto. 
    + edestruct Hfun as [tau' [t' [vs' [Hget Hfun']]]].
      rewrite Hget in H10; inv H10.
      do 3 eexists. rewrite M.gso; [ | now intros Heq; subst; eapply Hd; eauto ].
      split; eauto. intros f v' Hnin Hin Hget''.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hget' Hcc']]]]]]]]]]; eauto.
      subst. repeat eexists; eauto.
      rewrite M.gso. eassumption. 
      intros Hc. subst; eapply Hd; eauto.
    + eapply env_inv_extend_r. now intros Heq; subst; eapply Hd; eauto.
      eassumption.
    + intros v' Hget. eexists. rewrite M.gss. split; eauto.
      edestruct Henv as [tau' [t' [vs' [Hget' Henv']]]].
      rewrite Hget' in H10; inv H10.
      edestruct Henv' as [v'' [Hnth Hcc']]; eauto.
      rewrite H11 in Hnth. now inv Hnth.
Qed.

Lemma project_var_not_In_free_set  Scope Funs Γ FVs x x' C S S'  :
  project_var Scope Funs Γ FVs S x x' C S' ->
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  ~ In _ S' x'.
Proof.
  intros Hproj Hd. inv Hproj; intros Hc.
  - eapply Hd. eauto.
  - inv Hc. exfalso. eauto.
  - inv Hc. exfalso. eauto.    
Qed.

Lemma project_var_free_set_Included Scope Funs Γ FVs x x' C S S' :
  project_var Scope Funs Γ FVs S x x' C S' ->
  Included _ S' S.
Proof.
  intros Hproj. inv Hproj.
  - now apply Included_refl.
  - now apply Subset_Setminus.
  - now apply Subset_Setminus.
Qed.

Lemma project_vars_free_set_Included Scope Funs Γ FVs xs xs' C S S' :
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  Included _ S' S.
Proof.
  intros Hproj. induction Hproj.
  - now apply Included_refl.
  - eapply Included_trans. eassumption.
    eapply project_var_free_set_Included. eassumption. 
Qed.

Lemma project_vars_not_In_free_set  Scope Funs Γ FVs xs xs' C S S'  :
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  Disjoint _ S' (FromList xs').
Proof.
  intros Hproj Hd. induction Hproj.
  - constructor.  intros x Hc. inv Hc. rewrite FromList_nil in H0.
    eapply not_In_Empty_set. eassumption. 
  - rewrite FromList_cons. eapply Disjoint_sym.
    eapply Disjoint_Union.
    + eapply Disjoint_sym. eapply Disjoint_Included_l.
      eapply project_vars_free_set_Included. eassumption.
      eapply Disjoint_Singleton.
      eapply project_var_not_In_free_set; eassumption. 
    + eapply Disjoint_sym. eapply IHHproj.
      eapply Disjoint_Included_l.
      eapply project_var_free_set_Included. eassumption.
      eassumption.
Qed.

Lemma getlist_set_neq {A} xs x (v : A) rho :
  ~ List.In x xs ->
  getlist xs (M.set x v rho) = getlist xs rho. 
Proof.
  intros Hin.
  revert rho. induction xs; intros rho.
  - reflexivity.
  - simpl. rewrite M.gso.
    + rewrite IHxs. reflexivity.
      intros Hin'. eapply Hin. now constructor 2.
    + intros Heq; subst. eapply Hin. now constructor.
Qed.

Lemma ctx_to_rho_comp_ctx C C1 C2 rho rho' :
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

Lemma ctx_to_rho_comp_ctx_f C1 C2 rho1 rho2 rho3 :
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


Lemma project_var_get Scope Funs Γ FVs S1 x x' C1 S2 rho1 rho2 y:
  project_var Scope Funs Γ FVs S1 x x' C1 S2 ->
  ctx_to_rho C1 rho1 rho2 ->
  ~ In _ S1 y ->
  M.get y rho1 = M.get y rho2. 
Proof.
  intros Hvar Hctx Hin. inv Hvar.
  - inv Hctx. reflexivity.
  - inv Hctx. inv H12.
    destruct (Coqlib.peq y x'); subst.
    contradiction.
    now rewrite M.gso.
  - inv Hctx. inv H12.
    destruct (Coqlib.peq y x'); subst.
    contradiction.
    now rewrite M.gso.
Qed.    

Lemma project_vars_get Scope Funs Γ FVs S1 xs xs' C1 S2 rho1 rho2 y:
  project_vars Scope Funs Γ FVs S1 xs xs' C1 S2 ->
  ctx_to_rho C1 rho1 rho2 ->
  ~ In _ S1 y ->
  M.get y rho1 = M.get y rho2. 
Proof.
  revert Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y.
  induction xs; intros Scope Funs Γ FVs S1 xs' C1 S2 rho1 rho2 y Hproj Hctx Hnin.
  - inv Hproj. inv Hctx. reflexivity.
  - inv Hproj.  
    edestruct ctx_to_rho_comp_ctx as [rho'' [Hctx1 Hctx2]]; eauto.
    rewrite <- comp_ctx_f_correct. reflexivity.
    eapply project_var_get in Hctx1; eauto. 
    eapply IHxs in Hctx2; eauto.
    rewrite Hctx1, <- Hctx2. reflexivity.
    inv H6. eauto.
    intros Hc. inv Hc. eauto.
    intros Hc. inv Hc. eauto.
Qed.

Lemma project_var_getlist Scope Funs Γ FVs S1 x x' C1 S2 rho1 rho2 ys :
  project_var Scope Funs Γ FVs S1 x x' C1 S2 ->
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


Lemma project_vars_getlist Scope Funs Γ FVs S1 xs xs' C1 S2 rho1 rho2 ys :
  project_vars Scope Funs Γ FVs S1 xs xs' C1 S2 ->
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

Lemma project_vars_correct k rho1 rho2 rho2'
      Scope Funs Γ FVs xs xs' C S S'  :
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  cc_approx_env_P Scope k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  env_inv k rho1 rho2 Scope Funs Γ FVs ->
  ctx_to_rho C rho2 rho2' ->
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs Γ /\
  env_inv k rho1 rho2' Scope Funs Γ FVs /\
  (forall vs,
     getlist xs rho1 = Some vs ->
     exists vs', getlist xs' rho2' = Some vs' /\
            Forall2 (cc_approx_val k) vs vs').
Proof.
  revert k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S.
  induction xs;
    intros k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S Hproj Hcc Hfun Henv Hctx Hd.
  - inv Hproj. inv Hctx. repeat split; eauto. 
    eexists. split. reflexivity. 
    inv H. now constructor. 
  - inv Hproj.
    edestruct ctx_to_rho_comp_ctx as [rho'' [Hctx1 Hctx2]]; eauto.
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

Lemma ctx_to_rho_cc_approx_exp k rho1 rho2 rho2' C e e' :
  ctx_to_rho C rho2 rho2' ->
  cc_approx_exp k (e, rho1) (e', rho2') ->
  cc_approx_exp k (e, rho1) (C |[ e' ]|, rho2).
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

Lemma Union_Included {A} S1 S2 S :
  Included A S1 S ->
  Included A S2 S ->
  Included A (Union A S1 S2) S.
Proof. 
  intros H1 H2 x Hin; inv Hin; eauto.
Qed.

Lemma Singleton_Included {A} x S :
  In A S x ->
  Included A (Singleton A x) S.
Proof. 
  intros H x' Hin; inv Hin; eauto.
Qed.

Lemma project_var_In_Union Scope Funs Γ FVs S x x' C S' :
  project_var Scope Funs Γ FVs S x x' C S' ->
  In _ (Union var Scope (Union var Funs (FromList FVs))) x.
Proof.
  intros Hvar. inv Hvar; eauto.
  right; right. eapply nthN_In. eassumption.
Qed.

Lemma project_vars_In_Union Scope Funs Γ FVs S xs xs' C S' :
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  Included var (FromList xs) (Union var Scope (Union var Funs (FromList FVs))).
Proof.
  intros Hvar. induction Hvar; eauto.
  - rewrite FromList_nil. now apply Included_Empty_set.
  - rewrite FromList_cons.
    eapply Union_Included; [| eassumption ].
    eapply Singleton_Included. eapply project_var_In_Union.
    eassumption.
Qed.

Lemma project_var_ctx_to_rho Scope Funs Γ FVs x x' C S S' v1 k rho1 rho2 :
  project_var Scope Funs Γ FVs S x x' C S' ->
  env_inv k rho1 rho2 Scope Funs Γ FVs ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  M.get x rho1 = Some v1 ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros Hproj [t' [tau' [vs' [Hget3' Henv]]]]
         [t [tau [vs [Hget3 Hfun]]]] Hget1; inv Hproj.
  - eexists; econstructor; eauto.
  - edestruct Hfun as
        [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]]; eauto.
    eexists; econstructor; eauto. constructor.
  - rewrite Hget3 in Hget3'; inv Hget3'.
    edestruct Henv as [y [Hnth Hcc]]; eauto.
    eexists. econstructor; eauto. constructor. 
Qed.

Lemma project_var_not_In Scope Funs Γ FVs S x x' C S' :
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
      
  project_var Scope Funs Γ FVs S x x' C S' ->
  ~ In _ S x.
Proof.
  intros Hd  Hproj. inv Hproj; intros Hin; try now eapply Hd; eauto.
  eapply nthN_In in H1. eapply Hd. eauto.
Qed.

Lemma project_vars_Disjoint Scope Funs Γ FVs S xs xs' C S' :
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->      
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  Disjoint _ S (FromList xs).
Proof.
  revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
  - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
  - inv Hproj. rewrite FromList_cons.
    eapply Disjoint_sym; eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Singleton. eapply project_var_not_In; eauto.
    inv H6.
    + eapply IHxs; [| eassumption ]. eauto.
    + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y')) (FromList xs)).
      { eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Subset_Setminus. }
      eapply Disjoint_Included_l with (s3 := Union _ S (Singleton _ y')).
      now apply Included_Union_l.
      rewrite (@Union_Setminus _ _ _ _).
      eapply Disjoint_Union; eauto.
      eapply project_vars_In_Union in H10. 
      constructor. intros x Hc. inv Hc.
      inv H2. eapply Hd. constructor.
      eassumption. eapply H10 in H3. inv H3; eauto.
      inv H2; eauto.
    + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y')) (FromList xs)).
      { eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Subset_Setminus. }
      eapply Disjoint_Included_l with (s3 := Union _ S (Singleton _ y')).
      now apply Included_Union_l.
      rewrite (@Union_Setminus _ _ _ _).
      eapply Disjoint_Union; eauto.
      eapply project_vars_In_Union in H10.  
      constructor. intros x Hc. inv Hc.
      inv H3. eapply Hd. constructor.
      eassumption. eapply H10 in H4. inv H4; eauto.
      inv H3; eauto.
Qed.

Lemma project_vars_ctx_to_rho Scope Funs Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  project_vars Scope Funs Γ FVs S xs xs' C S' ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->
  env_inv k rho1 rho2 Scope Funs Γ FVs ->
  getlist xs rho1 = Some vs1 ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros HD Hvars Hfun [tau [t [vs [Hget Henv]]]].
  assert (HD' := Hvars).
  apply project_vars_Disjoint in HD'; [ | eassumption ]. 
  revert Scope Funs Γ FVs xs' C S S' vs1 tau t vs k
         rho1 rho2  HD HD' Hvars Hfun Hget Henv. 
  induction xs;
    intros Scope Funs Γ FVs xs' C S S' vs1 tau t vs k
           rho1 rho2 HD  HD' Hvars Hfun Hget Hclo Hgetlist.
  - inv Hvars. eexists; econstructor; eauto.
  - inv Hvars. simpl in Hgetlist.
    destruct (M.get a rho1) eqn:Hgeta1; try discriminate. 
    destruct (getlist xs rho1) eqn:Hgetlist1; try discriminate.
    edestruct project_var_ctx_to_rho with (rho1 := rho1) as [rho2' Hctx1]; eauto.
    now do 3 eexists; split; eauto. 
    edestruct IHxs with (rho2 := rho2') as [rho2'' Hctx2];
      [|  | eassumption | | | eassumption | eassumption | ].
    + eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included. eassumption.
    + rewrite FromList_cons in HD'.
      eapply Disjoint_Included_l.
      * eapply project_var_free_set_Included. eassumption.
      * eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_Union_r.
    + do 3 eexists; split.
      erewrite <- project_var_get; eauto.
      intros Hin. eapply HD. eauto.
      intros f v' Hnin Hin Hgetv'.
      edestruct Hfun as [tau1 [t1 [vs' [Hget1 Hfun']]]].
      rewrite Hget1 in Hget. inv Hget.
      edestruct Hfun' as
          [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
        eauto.
      subst. repeat eexists; eauto.
      erewrite <- project_var_get; eauto. 
      intros Hin'. eapply HD. eauto.
    + erewrite <- project_var_get; eauto. 
      intros Hin. eapply HD. eauto.
    + exists rho2''. eapply ctx_to_rho_comp_ctx_f; eassumption.
Qed.

(* Lemma bstep_e_ctx_app rho C e1 e2 v c : *)
(*   (forall rho v c, bstep_e rho e1 v c -> bstep_e rho e2 v c) -> *)
(*   bstep_e rho (C |[ e1 ]|) v c-> *)
(*   bstep_e rho (C |[ e2 ]|) v c. *)
(* Proof.   *)
(*   revert rho e1 e2 v c. *)
(*   induction C; eauto; intros rho e1 e2 v' c Hyp Hstep; inv Hstep; try (now econstructor; eauto). *)
(*   - apply findtag_append_spec in H3. *)
(*     edestruct H3 as [Hfind | [Hfind Hnin]]. *)
(*     + simpl. econstructor; eauto. *)
(*       now eapply findtag_append_Some.  *)
(*     + simpl in Hfind. edestruct (M.elt_eq t t0) eqn:Heq; subst. *)
(*       * inv Hfind. simpl; econstructor; [| | eapply IHC ]; eauto. *)
(*         rewrite findtag_append_not_In; [| eassumption ]. *)
(*         simpl; now rewrite Heq. *)
(*       * inv Hfind. simpl; econstructor; eauto. *)
(*         rewrite findtag_append_not_In; [| eassumption ]. *)
(*         simpl; now rewrite Heq. *)
(*   - admit. *)
(* Admitted. *)

Lemma Complement_Disjoint {A} S1 S2 :
  Included A S1 S2 ->
  Disjoint A (Complement _ S2) S1.
Proof.   
  intros Hin. constructor. intros x Hin'.
  inv Hin'. eauto.
Qed.

Lemma make_closures_correct k rho1 rho2 rho2' B Scope Funs FVs Γ Γ' C :
  make_closures B Γ' C ->
  unique_functions B ->
  ~ In _ (name_in_fundefs B) Γ ->
  ~ In _ (name_in_fundefs B) Γ' ->
  Included _ (name_in_fundefs B) Scope ->
  cc_approx_env_P (Setminus _ Scope (name_in_fundefs B)) k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs Γ ->  
  env_inv k rho1 rho2 Scope Funs Γ FVs ->
  Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) Γ' ->
  ctx_to_rho C rho2 rho2' ->
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs Γ /\
  env_inv k rho1 rho2' Scope Funs Γ FVs.
Proof.
  intros Hmake. revert k rho1 rho2 rho2' Scope Funs FVs Γ.
  induction Hmake;
    intros k rho1 rho2 rho2' Scope Funs FVs Γ1 Hun Hnin1 Hnin2
           Hsub Hcc Hfun Henv Hfun' Hctx.
  - inv Hctx. repeat split; eauto.
    simpl in *.
    now rewrite Setminus_Empty_set_Same_set in Hcc. 
  - eapply ctx_to_rho_comp_ctx in Hctx; [| apply Constr_cc; constructor ].
    destruct Hctx as [rho2'' [Hctx1 Hctx2]].
    inv Hctx1. inv H9. inv Hun.
    (* destruct Hfun as [tau1 [t1 [vs [Hget Hfun]]]]. *)
    edestruct IHHmake as [Hcc1 [Hfun1 Henv1]];
      [ eassumption | | | | | | | | eassumption | ].
    + intros Hc. eapply Hnin1. right. now apply Hc. 
    + intros Hc. eapply Hnin2. right. now apply Hc. 
    + eapply Included_trans; [| eassumption ].
      now eapply Included_Union_r.
    + eapply cc_approx_env_P_antimon;
      [| now apply (@Included_Union_Setminus _ _ (Singleton var f) _) ].
      rewrite Setminus_Union, (Union_sym (name_in_fundefs B)).
      eapply cc_approx_env_P_union.
      eapply cc_approx_env_P_not_in_P_r. eassumption.
      intros Hc. inv Hc. now eauto.
      intros f' Hs v Hget'. inv Hs.
      edestruct Hfun' as [tau2 [t2 [vs2 [Hget2 Hfun2]]]]. 
      edestruct Hfun2
        as [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2' [t2' [Heq' [Hget2' Happrox2]]]]]]]]]]; eauto.
      now eapply not_In_Empty_set. now left; eauto.
      subst. eexists; split.
      rewrite M.gss. reflexivity.
      rewrite H8 in Hget2'. inv Hget2'. rewrite H7 in Hget2. inv Hget2.
      rewrite cc_approx_val_eq in *. now eauto.
    + eapply Fun_inv_set_In_Scope_r_not_Γ ; [| | eassumption ].
      * eapply Hsub. now left. 
      * intros Hc; subst. eapply Hnin1. left; eauto.
    + eapply env_inv_extend_r; [| eassumption ].
      intros Hc; subst. eapply Hnin1. left; eauto.
    + edestruct Hfun' as [tau2 [t2 [vs2 [Hget2 Hfun2]]]]. 
      do 3 eexists; split; eauto.
      rewrite M.gso. eassumption.
      intros Hc; subst. eapply Hnin2. left; eauto.
      intros f' v' _ Hnin Hgetf. 
      edestruct Hfun2
        as [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2' [t2' [Heq' [Hget2' Happrox2]]]]]]]]]]; eauto.
      now eapply not_In_Empty_set. now right; eauto.
      repeat eexists; eauto. 
      rewrite M.gso. eassumption.
      intros Hc; subst; eauto.
    + eauto.
Qed. 

Lemma make_closures_ctx_to_rho B Γ C k rho1 rho2  :
  make_closures B Γ C ->
  unique_functions B ->
  ~ In _ (name_in_fundefs B) Γ ->
  Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) Γ ->
  (forall f, In _ (name_in_fundefs B) f -> exists v, M.get f rho1 = Some v) ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros Hclo. revert rho1 rho2. induction Hclo; intros rho1 rho2 Hun Hnin Hfun Hyp. 
  - eexists; constructor. 
  - destruct (Hyp f) as [v' Hget'].
    now left; eauto.
    edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
    edestruct Hfun' as
        [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]]; eauto.
    now apply not_In_Empty_set.
    now left; eauto. inv Hun.
    edestruct IHHclo as [rho2' Hctx]; [ eassumption | | | | now eexists; econstructor; eauto]. 
    + intros Hc; eapply Hnin; right; eauto.
    + eapply Fun_inv_set_not_In_Funs_r_not_Γ; [ eassumption | | ].
      intros Hc; subst. eapply Hnin; now left. 
      do 3 eexists; split; eauto; intros.
      edestruct Hfun' as
          [rho1'' [B1' [f1' [rho2'' [B2' [f2' [tau2' [t2' [Heq'' [Hget2' Happrox2']]]]]]]]]]; eauto.
      right; eauto. 
      subst. repeat eexists; eauto.
    + intros. eapply Hyp. right; eauto.
Qed.

Lemma getlist_nth_get (xs : list var) (vs : list val) rho (x : var) N :
  getlist xs rho = Some vs ->
  nthN xs N = Some x ->
  exists v, nthN vs N = Some v /\ M.get x rho = Some v. 
Proof.
  revert vs N; induction xs; intros vs N Hget Hnth.
  - inv Hnth. 
  - simpl in Hget.
    destruct (M.get a rho) eqn:Hget'; try discriminate.
    destruct (getlist xs rho) eqn:Hgetlist'; try discriminate.
    inv Hget. destruct N. 
    + inv Hnth. eexists; simpl; eauto.
    + edestruct IHxs as [v' [Hnth1 Hget1]]; eauto. 
Qed.

Lemma In_getlist (xs : list var) (rho : env) :
  (forall x, List.In x xs -> exists v, M.get x rho = Some v) ->
  exists vs, getlist xs rho = Some vs. 
Proof.                                            
  intros H. induction xs. 
  - eexists; simpl; eauto.
  - edestruct IHxs. 
    + intros x Hin. eapply H. now constructor 2. 
    + edestruct H. now constructor. 
      eexists. simpl. erewrite H1, H0. 
      reflexivity. 
Qed.

Lemma Fun_inv_def_funs_l k rho rho' B1 B1' Scope Funs Γ:
  Fun_inv k rho rho' Scope Funs Γ ->
  Fun_inv k (def_funs B1 B1' rho rho) rho'
          (Union _ (name_in_fundefs B1')  Scope) Funs Γ.
Proof.
  intros [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto.
  intros f v' Hnin Hin Hget'.
  rewrite def_funs_neq in Hget'; eauto.
Qed.

Lemma Fun_inv_def_funs_r k rho rho' B1 B1' Scope Funs Γ:
  ~ In _ (name_in_fundefs B1') Γ ->
  Fun_inv k rho rho' Scope Funs Γ ->
  Fun_inv k rho (def_funs B1 B1' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs Γ.
Proof.
  intros Hin [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  intros f v' Hnin Hin' Hget'.
  edestruct Hfun as
      [rho1' [B2 [f1 [rho2' [B2' [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]]; eauto.
  repeat eexists; eauto.
  rewrite def_funs_neq; eauto.
Qed.

Instance Fun_inv_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff)
         (Fun_inv).
Proof.
  constructor; subst; intros [tau [t [vs [Hget Hfun]]]]; do 3 eexists; split; eauto;
  intros; eapply Hfun; eauto; intros Hc; eapply H; eapply H2; eauto.
Qed.

Lemma Fun_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs Γ:
  ~ In _ (name_in_fundefs B1') Γ ->
  Same_set _ (name_in_fundefs B1') (name_in_fundefs B2') ->
  Fun_inv k rho rho' Scope Funs Γ ->
  Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs Γ.
Proof.
  intros Hin HS [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  intros Hc. eapply Hin. now eapply HS.
  intros f v' Hnin Hin' Hget'.
  rewrite def_funs_neq in Hget'; eauto.
  edestruct Hfun as
      [rho1' [B3 [f1 [rho2' [B3' [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]]; eauto.
  repeat eexists; eauto.
  rewrite def_funs_neq; eauto.
  intros Hc. eapply Hnin. left. now rewrite HS.
Qed.

Lemma cc_approx_env_P_def_funs_not_In_P_l k rho1 rho2 S B B' :
  Disjoint _ S (name_in_fundefs B') ->
  cc_approx_env_P S k rho1 rho2 ->
  cc_approx_env_P S k (def_funs B B' rho1 rho1) rho2.
Proof.
  intros Hd Hcc x HS v Hget. eapply Hcc; eauto. 
  erewrite <- def_funs_neq. eassumption.  
  intros Hc. eapply Hd; constructor; eauto.
Qed.

Lemma cc_approx_env_P_def_funs_not_In_P_r k rho1 rho2 S B B' :
  Disjoint _ S (name_in_fundefs B') ->
  cc_approx_env_P S k rho1 rho2 ->
  cc_approx_env_P S k rho1 (def_funs B B' rho2 rho2).
Proof.
  intros Hd Hcc x HS v Hget.
  edestruct Hcc as [v' [Hget' Hcc']]; eauto.
  eexists; split; eauto.
  rewrite def_funs_neq. eassumption.
  intros Hc. eapply Hd; constructor; eauto.
Qed.

Lemma env_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs Γ FVs:
  ~ In _ (name_in_fundefs B1') Γ ->
  Same_set _ (name_in_fundefs B1') (name_in_fundefs B2') ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  env_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs Γ FVs.
Proof.
  intros Hin HS [t [tau [v [Hget Henv]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  intros Hc. eapply Hin. now eapply HS.
  intros f N v' Hnin Hnin' Hnth Hget'.
  rewrite def_funs_neq in Hget'; eauto.
Qed.

Corollary Fun_inv_def_funs' k rho rho' B1 B1' B2 B2' Scope Funs Γ:
  ~ In _ (name_in_fundefs B1') Γ ->
  Same_set _ (name_in_fundefs B1') (name_in_fundefs B2') ->
  Fun_inv k rho rho' Scope Funs Γ ->
  Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
          (Union _ (name_in_fundefs B2') Scope) Funs Γ.
Proof.
  intros Hin HS Hf. rewrite <- HS. now apply Fun_inv_def_funs.
Qed.

Lemma closure_conversion_correct k rho rho' e e' Scope Funs Γ FVs :
  cc_approx_env_P Scope k rho rho' ->
  ~ In _ (bound_var e) Γ ->
  vars_in_env (occurs_free e) rho ->
  fundefs_names_unique e ->
  Fun_inv k rho rho' Scope Funs Γ ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  Closure_conversion Scope Funs Γ FVs e e' ->
  cc_approx_exp k (e, rho) (e', rho').
Proof.
  revert k e rho rho' e' Scope Funs Γ FVs.
  induction k as [k IHk] using lt_wf_rec1.
  induction e using exp_ind';
    intros rho1 rho2 e' Scope Funs Γ FVs Happrox Hnin HFVs Hun Hfun Henv Hcc.
  - (* Case Econstr *)
    inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H11; eauto.
    inv H11. 
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | | | eassumption | eassumption | eassumption | ]. 
    + eapply cc_approx_env_P_extend with (v2 := Vconstr tau' t0 v').
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.
      rewrite cc_approx_val_eq. constructor; eauto.
      now eapply Forall2_Forall2_asym_included.
    + eapply vars_in_env_antimon; [| eapply vars_in_env_extend; eassumption ].
      eapply occurs_free_Econstr_Included. 
    + intros f Hfin. eauto.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Included_Union_r.
    + eapply env_inv_extend_In_Scope_l. now constructor.
      eapply env_inv_extend_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply env_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
  - (* Case [Ecase x []] *)
    inv Hcc. destruct pats'; [| now inv H7 ].
    intros v1 c1 Hleq Hstep. inv Hstep. inv H3. 
  - (* Case [Ecase x ((c, p) :: pats] *)
    inv Hcc. destruct pats'; [ now inv H7 |].
    inversion H7 as [ | [c1 p1] [c2 p2] l1 l2 [Heq Hcc] Hall ]; simpl in Heq; subst. 
    intros v1 c1 Hleq Hstep. inv Hstep.
    simpl in H3.  destruct (M.elt_eq c2 t) eqn:Heq; subst. 
    { inv H3. inv H5. 
      - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct vcon; try contradiction. inv Happrox2.
        edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | | 
          | eassumption | eassumption | eassumption | eassumption | eassumption | ].
        + eapply vars_in_env_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        + intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor. 
        + repeat eexists; [| eassumption ].
          econstructor; eauto. simpl. now rewrite Heq.
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H1 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
          [| now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
           | | | eassumption | eassumption | eassumption
           | repeat eexists; [| eassumption ]; econstructor; eauto;
             econstructor; eauto;
             [ rewrite M.gss ; reflexivity | simpl; now rewrite Heq ] ].
        + eapply cc_approx_env_P_not_in_P_r; now eauto.
        + eapply vars_in_env_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        + intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor. 
        + eapply Fun_inv_set_not_In_Funs_r_not_Γ. now eauto.
          intros Heq'; subst. now eauto. eassumption.
        + eapply env_inv_extend_r. intros Hc. subst. now eauto.
          eassumption. }
    { inv H3. assert (H5' := H5). inv H5. 
      - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct vcon; try contradiction. inv Happrox2.
        edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
          | eassumption | eassumption | now econstructor; eauto
          | eassumption | now econstructor; eauto | ].
        + eapply vars_in_env_antimon; [| eassumption ].
          intros x Hin. inv Hin; eauto.
        + intros f Hfin. eapply Hun. inv Hfin. 
          econstructor; eauto. constructor 2. eassumption.
        + inv Hstep2. repeat eexists; [| eassumption ].
          econstructor; eauto. simpl. rewrite Hget' in H5. inv H5.
          now rewrite Heq. 
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H1 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
          | eassumption | eassumption | now econstructor; eauto | eassumption
          | now econstructor; eauto | ].
        + eapply vars_in_env_antimon; [|  eassumption ].
          intros x Hin. inv Hin; eauto.
        + intros f Hfin. eapply Hun. inv Hfin.
          econstructor; eauto. constructor 2. eassumption.
        + inv Hstep2; rewrite Hget in H16; inv H16; rewrite Hnth' in H17; inv H17.
          inv H18. repeat eexists; [| eassumption ]; econstructor; eauto.
          econstructor; eauto. simpl.
          rewrite M.gss in H10. inv H10. now rewrite Heq. }
  - (* Case Eproj *)
    inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
    edestruct project_var_correct as [Hnin' [Happ [Hfun' [Henv' Hvar]]]]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    rewrite cc_approx_val_eq in Happ'. destruct v'; try contradiction.
    inv Happ'. eapply ctx_to_rho_cc_approx_exp; eauto.
    intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H11; eauto.
    inv H11. edestruct (@Forall2_asym_nthN val) as [v2' [Hnth2 Happ2]]; eauto.
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | | | eassumption | eassumption | eassumption | ]. 
    + eapply cc_approx_env_P_extend; [| eassumption ].
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.      
    + eapply vars_in_env_antimon; [| eapply vars_in_env_extend; eassumption ].
      eapply occurs_free_Eproj_Included. 
    + intros f Hfin. eauto.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Included_Union_r.
    + eapply env_inv_extend_In_Scope_l. now constructor.
      eapply env_inv_extend_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply env_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
  - (* Case Efun -- the hardest one! *) 
    inv Hcc.
    assert (Ha : exists vs, getlist FVs' rho1 = Some vs).
    { eapply In_getlist. intros x Hin. eapply HFVs. 
      rewrite occurs_free_Efun, H1. eauto. }
    destruct Ha as [vs Hgetlist].
    intros v1 c1 Hleq Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    assert (Hsuf :
              cc_approx_exp k (e, def_funs f2 f2 rho1 rho1)
                            (C |[ e'0 ]|, def_funs B' B' (M.set Γ' (Vconstr tau t v') rho2')
                                       (M.set Γ' (Vconstr tau t v') rho2'))).
    { edestruct make_closures_ctx_to_rho as [rho2'' Htp_rho']; eauto.
      - eapply closure_conversion_fundefs_correct; eauto.
        + intros f Hfin. inv Hfin; eauto.
        + eapply vars_in_env_antimon; [| eassumption ].
          intros x H. eapply Free_Efun2. eassumption. 
        + edestruct Hvar as [vs' [Hgetlist' Hall]]; eauto.
          intros x N v _ _ Hnth Hget. rewrite Hget' in Hgetlist'; inv Hgetlist'.
          edestruct getlist_nth_get as [v' [Hnth' Hget'']].
          now apply Hgetlist. eassumption.
          edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
          eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
      - intros. now eapply get_def_funs_In_names.
      - edestruct make_closures_correct with
          (Scope := Union var (name_in_fundefs f2) Scope)
          (Γ := Γ)
          (rho1 := def_funs f2 f2 rho1 rho1)
          (rho2 := def_funs B' B' (M.set Γ' (Vconstr tau t v') rho2')
                            (M.set Γ' (Vconstr tau t v') rho2'))
          as [Hcc'' [Hfun'' Henv'']].
        + eauto.
        + eauto.
        + intros Hc. eapply Hnin. constructor.
          now eapply name_in_fundefs_bound_var_fundefs.
        + eauto.
        + eapply Included_Union_l.
        + eapply cc_approx_env_P_def_funs_not_In_P_l.
          eapply Disjoint_Setminus. now apply Included_refl.
          eapply cc_approx_env_P_def_funs_not_In_P_r.
          eapply Disjoint_Setminus. rewrite <- Closure_conversion_fundefs_name_in_fundefs.
          now apply Included_refl. eauto.
          eapply cc_approx_env_P_not_in_P_r.
          eapply cc_approx_env_P_antimon. eassumption.
          rewrite Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r.
          eapply Setminus_Included. now apply Included_refl.
          intros Hin. inv Hin. eapply H2. inv H; eauto.
        + eapply Fun_inv_def_funs.
          * intros Hc. eapply Hnin. constructor.
            now eapply name_in_fundefs_bound_var_fundefs.
          * eapply Closure_conversion_fundefs_name_in_fundefs. eassumption.
          * eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ].
            intros Hc. eapply H2. eauto.
            intros Hc. eapply H2. subst. eauto.
        + eapply env_inv_def_funs.
          * intros Hc. eapply Hnin. constructor.
            now eapply name_in_fundefs_bound_var_fundefs.
          * eapply Closure_conversion_fundefs_name_in_fundefs. eassumption.
          * eapply  env_inv_extend_r.
            intros Hc. eapply H2. subst. eauto.
            eassumption. 
        + eapply closure_conversion_fundefs_correct; eauto.
          * intros f Hfin. inv Hfin; eauto.
          * eapply vars_in_env_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption. 
          * edestruct Hvar as [vs' [Hgetlist' Hall]]; eauto.
            intros x N v _ _ Hnth Hget. rewrite Hget' in Hgetlist'; inv Hgetlist'.
            edestruct getlist_nth_get as [v' [Hnth' Hget'']].
            now apply Hgetlist. eassumption.
            edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
            eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
        + eauto.
        + eapply ctx_to_rho_cc_approx_exp; eauto.
          eapply IHe; eauto.
          * eapply vars_in_env_antimon.
            eapply Included_trans. now eapply occurs_free_Efun_Included.
            rewrite Union_sym. now apply Included_refl.
            apply vars_in_env_def_funs. eassumption.
          * intros f Hfin; eauto. }
    intros v1' c1' Hleq' Hstep'. inv Hstep'.
    edestruct Hsuf as [v2' [c2' [Hstep2' Hcc2']]]; [| eassumption |]; eauto.
    repeat eexists; eauto. econstructor; eauto.
    econstructor; eauto.
  - (* Case Eapp *)
    inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    + edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Complement_Disjoint. now apply Included_refl.      
      simpl. rewrite H4, H8. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      eapply Complement_Disjoint. now apply Included_refl.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H4, H8. reflexivity.
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
      destruct (getlist ys' rho2') eqn:Hgetlist'; try discriminate. inv Hget'.
      inv Happ'. rewrite cc_approx_val_eq in H5. destruct v0; try contradiction.
      eapply ctx_to_rho_cc_approx_exp with (e := Eapp v l); eauto.
      * intros v1' c1' Hleq' Hstep'.
        inv Hstep'. rewrite H4 in H6. inv H6.
        rewrite H8 in H13; inv H13.
        admit. (* the relation needs tweaking *)
        rewrite H4 in H3. congruence.
      * constructor; eauto.
    + edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Complement_Disjoint. now apply Included_refl.      
      simpl. rewrite H3, H4. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      eapply Complement_Disjoint. now apply Included_refl.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H3, H4. reflexivity.
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
      destruct (getlist ys' rho2') eqn:Hgetlist'; try discriminate. inv Hget'.
      inv Happ'. rewrite cc_approx_val_eq in H10. destruct v0; try contradiction.
      eapply ctx_to_rho_cc_approx_exp with (e := Eapp v l); eauto.
      * intros v1' c1' Hleq' Hstep'.
        inv Hstep'.
        { rewrite H4 in H16. inv H16. 
          rewrite H3 in H11; inv H11. }
        { rewrite H4 in H11. inv H11. 
          rewrite H3 in H6; inv H6.
          destruct l1; try contradiction. destruct v0, l1; try contradiction.
          destruct v2; try contradiction.
          rewrite H14 in H5. inv H5. 
          rewrite H8 in H16. inv H16. eapply bstep_e_deterministic in H19; eauto. inv H19.
          assert (Hlen := List_util.Forall2_length _ _ _ H13).
          edestruct H10 with (vs2 := l0) (j := k - 1)
            as [t2' [Γ' [xs2 [e2 [rho2'' [Hfind [Hset Hyp]]]]]]]; eauto.
          edestruct Hyp as [v2' [c2 [Hstep2 Hcc']]]; try eassumption. omega.
          eapply List_util.Forall2_monotonic; [| eassumption ].
          intros. eapply cc_approx_val_monotonic. eassumption. omega. omega.
          repeat eexists; eauto. econstructor. eassumption. reflexivity.
          econstructor. rewrite M.gso. eassumption.
          intros Hc; subst. eapply project_vars_not_In_free_set. eauto.
          eapply Complement_Disjoint. now apply Included_refl.
          constructor. now eapply H2. rewrite FromList_cons. now eauto.
          reflexivity.
          eapply BStep_app_fun. rewrite M.gso. rewrite M.gss. reflexivity.
          now eauto. simpl. rewrite M.gss.
          rewrite getlist_set_neq. rewrite getlist_set_neq.
          rewrite Hgetlist'. reflexivity. 
          intros Hin. eapply project_vars_not_In_free_set. eassumption.
          eapply Complement_Disjoint. now apply Included_refl.
          constructor. eapply H2. rewrite FromList_cons. now eauto.
          intros Hin. eapply project_vars_not_In_free_set. eassumption.
          eapply Complement_Disjoint. now apply Included_refl.
          constructor. eapply H7. rewrite FromList_cons. now eauto.
          eassumption. simpl in Hset. eauto. eassumption.
          eapply cc_approx_val_monotonic. eassumption. omega. }
        * econstructor; eauto. 
  - inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    eapply Complement_Disjoint. now apply Included_refl.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H13; eauto.
    inv H11.
    edestruct Prim_axiom as [vs' [Hf' Hcc]]; eauto.
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | | | eassumption | eassumption | eassumption | ]. 
    + eapply cc_approx_env_P_extend; [| eassumption ].
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.
    + eapply vars_in_env_antimon; [| eapply vars_in_env_extend; eassumption ].
      eapply occurs_free_Eprim_Included. 
    + intros f Hfin. eauto.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Included_Union_r.
    + eapply env_inv_extend_In_Scope_l. now constructor.
      eapply env_inv_extend_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply env_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
Admitted.