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

Lemma Fun_inv_extend k rho rho' Scope Funs Γ
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


Lemma closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
      Scope Γ FVs Funs' FVs' t tau vs:
  (* The IH *)
  (forall m : nat,
     m < k ->
     forall (e : exp) (rho rho' : env) (e' : exp)
       (Scope Funs : Ensemble var) (Γ : var) (FVs : list M.elt),
       cc_approx_env_P Scope m rho rho' ->
       ~ In var (bound_var e) Γ ->
       Fun_inv m rho rho' Scope Funs Γ ->
       env_inv m rho rho' Scope Funs Γ FVs ->
       Closure_conversion Scope Funs Γ FVs e e' ->
       cc_approx_exp m (e, rho) (e', rho')) ->
  Same_set _ (occurs_free_fundefs B1) (FromList FVs) ->
  Closure_conversion_fundefs (name_in_fundefs B1) FVs B1 B2 ->
  Closure_conversion_fundefs Funs' FVs' B1' B2' ->
  ~ In _ (name_in_fundefs B1) Γ ->
  ~ In _ (name_in_fundefs B1') Γ ->
  closure_env k rho (Empty_set _) (Empty_set _) vs FVs ->
  Fun_inv k (def_funs B1 B1' rho rho)
          (M.set Γ (Vconstr tau t vs) (def_funs B2 B2' rho' rho'))
          Scope (name_in_fundefs B1') Γ.
Proof.
  revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t tau vs.
  induction k as [k IHk] using lt_wf_rec1.
  induction B1';
    intros rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t' tau' vs
           IHe Hs Hcc Hcc' Hnin Hnin' Henv.
  - inv Hcc'. simpl.
    eapply Fun_inv_extend.
    + eapply IHB1'; eauto.
      intros Hc. apply Hnin'.
      simpl; eauto.
    + intros Hc. apply Hnin'. subst. simpl; eauto.
    + exists tau', t.
      rewrite cc_approx_val_eq.
      intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
      edestruct setlist_length
      with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset']. eassumption.
      now eauto.
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
      * assert
          (Fun_inv j (def_funs B1 B1 rho rho)
                   (M.set Γ (Vconstr tau' t' vs) (def_funs B2 B2 rho' rho'))
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
        eassumption. now eauto. now eauto.
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
  - do 3 eexists. rewrite M.gss. split; eauto.
    intros. inv H0.
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

Lemma closure_conversion_correct k rho rho' e e' Scope Funs Γ FVs :
  cc_approx_env_P Scope k rho rho' ->
  ~ In _ (bound_var e) Γ ->
  Fun_inv k rho rho' Scope Funs Γ ->
  env_inv k rho rho' Scope Funs Γ FVs ->
  Closure_conversion Scope Funs Γ FVs e e' ->
  cc_approx_exp k (e, rho) (e', rho').
Proof.
  revert k e rho rho' e' Scope Funs Γ FVs.
  induction k as [k IHk] using lt_wf_rec1.
  induction e using exp_ind';
    intros rho rho' e' Scope Funs Γ FVs Happrox Hnin Hfun Henv Hcc.
  - (* Case Econstr. Induction on l and the similar to Eproj *) 
    admit.
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
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto
          | eassumption | eassumption | eassumption | eassumption | eassumption | ].
        repeat eexists; [| eassumption ].
        econstructor; eauto. simpl. now rewrite Heq.
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1 [B1 [f1 [rho2 [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H1 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
          [| now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto
           | | | eassumption | eassumption | eassumption
           | repeat eexists; [| eassumption ]; econstructor; eauto;
             econstructor; eauto;
             [ rewrite M.gss ; reflexivity | simpl; now rewrite Heq ] ].
        + eapply cc_approx_env_P_not_in_P_r; now eauto.
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
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto
          | eassumption | eassumption | now econstructor; eauto
          | eassumption | now econstructor; eauto | ].
        inv Hstep2. repeat eexists; [| eassumption ].
        econstructor; eauto. simpl. rewrite Hget' in H5. inv H5.
        now rewrite Heq. 
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1 [B1 [f1 [rho2 [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H1 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto
          | eassumption | eassumption | now econstructor; eauto | eassumption
          | now econstructor; eauto | ].
        inv Hstep2; rewrite Hget in H16; inv H16; rewrite Hnth' in H17; inv H17.
        inv H18. repeat eexists; [| eassumption ]; econstructor; eauto.
        econstructor; eauto. simpl.
        rewrite M.gss in H10. inv H10. now rewrite Heq. }
  - (* Case Eproj *)
    inv Hcc. inv H9.
    + intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
      rewrite cc_approx_val_eq in Happrox2.
      destruct vcon; try contradiction. inv Happrox2.
      edestruct (@Forall2_asym_nthN val) as [v0' [Hnth' Happrox3]]; eauto.
      edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | eassumption | eassumption | eassumption | ].
      * eapply cc_approx_env_P_extend; [| eassumption ].
        rewrite Setminus_Union_distr,
        Setminus_Empty_set, Union_Empty_set_r. 
        eapply cc_approx_env_P_antimon; [ eassumption |].
        eapply Setminus_Included. now apply Included_refl.      
      * eapply Fun_inv_set_In_Scope_l. now eauto.
        eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_mon; [ | now eauto ].
        eapply Included_Union_r.
      * eapply env_inv_extend_In_Scope_l. now constructor.
        eapply env_inv_extend_r. intros Hc. eapply Hnin.
        subst. now eauto. now eapply env_inv_extend_Scope.
      * repeat eexists; [| eassumption ].
        econstructor; eauto.
    + intros v1 c1 Hleq Hstep. inv Hstep. simpl.
      edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
      edestruct Hfun' as
          [rho1 [B1 [f1 [rho2 [B2 [f2 [tau2 [t2 [Heq [Hget2 Happrox2]]]]]]]]]]; [| | now apply H11 | ];
      eauto.
      congruence.
    + simpl. intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
      edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
      rewrite cc_approx_val_eq in Happrox2.
      destruct v'; try contradiction. inv Happrox2.
      edestruct (@Forall2_asym_nthN val) as [v0' [Hnth'' Happrox3]]; eauto.
      edestruct IHe as [v2' [c2 [Hstep2 Happrox2]]];
        [ | now eauto | | | eassumption | eassumption | eassumption |
          repeat eexists; [| eassumption ]; econstructor; eauto;
          econstructor; eauto; rewrite M.gss; reflexivity ].
      * eapply cc_approx_env_P_extend; [| eassumption ].
        rewrite Setminus_Union_distr,
        Setminus_Empty_set, Union_Empty_set_r.
        eapply cc_approx_env_P_not_in_P_r.
        eapply cc_approx_env_P_antimon; eauto. eapply Setminus_Included.
        now eapply Included_refl. intros Hin. inv Hin. eapply H2. eauto. 
      * eapply Fun_inv_set_In_Scope_l. now eauto.
        eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_set_not_In_Funs_r_not_Γ. now eauto.
        intros Heq; subst. now eauto.
        eapply Fun_inv_mon; [ | now eauto ]. eapply Included_Union_r.
      * eapply env_inv_extend_In_Scope_l. now constructor.
        eapply env_inv_extend_r. intros Hc. subst. now eauto.
        eapply env_inv_extend_r. intros Hc. subst. now eauto.
        now apply env_inv_extend_Scope. 
  - (* Case Efun -- the hardest one! *)
    inv Hcc.
    (* edestruct Henv as [tau' [t' [vs' [Hget Hclo]]]].  *)
    eapply closure_conversion_fundefs_correct with
    (rho := rho) (rho' := rho') in H3; eauto.
Abort.