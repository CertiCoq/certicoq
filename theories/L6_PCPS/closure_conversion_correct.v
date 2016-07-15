Require Import cps cps_util set_util hoisting identifiers ctx
        Ensembles_util List_util closure_conversion eval logical_relations alpha_conv.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope alpha_scope.

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

(** Invariant about the values of free variables. *)
Definition closure_env k rho Scope Funs vs FVs : Prop :=
  forall (x : var) N (v : val),
    ~ In _ Scope x ->
    ~ In _ Funs x -> 
    nthN FVs N = Some x ->
    M.get x rho = Some v ->
    exists (v' : val),  nthN vs N = Some v' /\
                   cc_approx_val k v v'.

(** Invariant about the free variables *) 
Definition FV_inv k rho rho' Scope Funs Γ FVs : Prop :=
  exists tau t vs,
    M.get Γ rho' = Some (Vconstr tau t vs) /\
    closure_env k rho Scope Funs vs FVs.

(** Invariant about the functions in the current function definition *)
Definition Fun_inv k (rho rho' : env) Scope Funs σ Γ : Prop :=
  exists tau t vs,
    M.get Γ rho' = Some (Vconstr tau t vs) /\
    forall f v,
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho = Some v  ->
      exists  rho1 B1 f1 rho2 B2 f2 tau' t',
        v = (Vfun rho1 B1 f1) /\
        ~ In _ Scope (σ f) /\
        M.get (σ f) rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val k (Vfun rho1 B1 f1)
                      (Vconstr tau' t' [(Vfun rho2 B2 f2) ; (Vconstr tau t vs)]).

(** The variables in S are defined in the environment. Will be used to state
    that the free variables of an expression are present in the environment *)
Definition binding_in_map {A} (S : Ensemble M.elt) (map : M.t A) : Prop :=
  forall x, In _ S x -> exists v, M.get x map = Some v. 

(** * Lemmas about Fun_inv *)

(** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
Lemma Fun_inv_set k rho rho' Scope Funs σ Γ f rho1 B1 f1 rho2 B2 f2 tau t vs:
  Fun_inv k rho rho' Scope Funs σ Γ ->
  (σ f) <> Γ ->
  ~ In _ Scope (σ f) ->
  ~ In _ (image σ Funs) (σ f) ->
  M.get Γ rho' = Some (Vconstr tau t vs) ->
  (exists tau' t',
     cc_approx_val k (Vfun rho1 B1 f1)
                   (Vconstr tau' t' [(Vfun rho2 B2 f2) ; (Vconstr tau t vs)])) ->
  Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
          (M.set (σ f) (Vfun rho2 B2 f2) rho')
          Scope (Union _ (Singleton _ f) Funs) σ Γ.
Proof.
  intros Hinv Hneq Heq Hinj Hget Hv. edestruct Hinv as [tau' [t' [vs' [Hget' Hyp]]]]. 
  do 3 eexists. rewrite M.gso; eauto. split; [ eassumption |].
  intros f'' v Hnin' Hin Hget''. rewrite Hget in Hget'. inv Hget'.
  rewrite M.gsspec in Hget''. destruct (Coqlib.peq f'' f); subst.
  - inv Hget''.
    edestruct Hv as [tau1 [t1 Happrox]]; eauto. 
    repeat eexists; eauto. unfold extend. rewrite M.gss; eauto.
  - edestruct Hyp with (f := f'') as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [tau2 [t2 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
    subst; eauto.
    + inv Hin; eauto. inv H. congruence.
    + subst. repeat eexists; eauto. rewrite M.gso. now eauto. 
      intros Hc. inv Hin. inv H. congruence. eapply Hinj. 
      rewrite <- Hc. eexists; eauto.
Qed.

(** Rename the environment parameter *)
Lemma Fun_inv_rename k rho1 rho2 Scope Funs σ Γ Γ' v :
  ~ In _ (image σ Funs) Γ ->  ~ In _ (image σ Funs) Γ' ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
  Fun_inv k rho1 (M.set Γ' v rho2) Scope Funs σ Γ'.
Proof.
  intros Hnin Hnin' [tau [t [vs [Hget H]]]].
  rewrite M.gss in Hget. inv Hget.
  do 3 eexists. rewrite M.gss; split; [ now eauto |].
  intros f v Hninf Hin Hget.
  edestruct H as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin'' [Hget' Happrox']]]]]]]]]]]; eauto.
  rewrite M.gsspec in Hget'.
  destruct (Coqlib.peq (σ f) Γ); subst.
  - exfalso. eapply Hnin. eexists. eauto.
  - destruct (Coqlib.peq (σ f) Γ'); subst.
    + exfalso. eapply Hnin'. eexists. eauto.
    + repeat eexists; eauto. rewrite M.gso; eauto.
Qed.

(** Extend [Scope] with a set that does not shadow the new function names *)
Lemma Fun_inv_mon k rho1 rho2 Scope Scope' Funs σ Γ :
  Disjoint _ (image σ Funs) Scope' ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  Fun_inv k rho1 rho2 (Union _ Scope' Scope) Funs σ Γ.
Proof.
  intros Hd [tau [t [vs [Hget H]]]].
  do 3 eexists. split; [ now eauto |].
  intros f c Hnin Hin Hget'.
  edestruct H as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin'' [Hget'' Happrox']]]]]]]]]]]; eauto.
  repeat eexists; eauto.
  intros Hc; inv Hc; eauto. eapply Hd. constructor; eauto.
  eexists; eauto.
Qed.

(** Extend the first environment with a variable in [Scope] *)
Lemma Fun_inv_set_In_Scope_l k rho1 rho2 Scope Funs σ Γ x v :
  In _ Scope x ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  Fun_inv k (M.set x v rho1) rho2 Scope Funs σ Γ.
Proof.
  intros Hin [tau [t [vs [Hget H]]]].
  do 3 eexists. split; [ now eauto |].
  intros f v' Hninf Hin' Hget'.
  rewrite M.gsspec in Hget'.
  destruct (Coqlib.peq f x); subst; [ contradiction |].
  edestruct H as [v'' [tau' [t' [Hget'' Happrox']]]]; eauto.
Qed.

(** Extend the second environment with a variable in [Scope] *)
Lemma Fun_inv_set_In_Scope_r k rho1 rho2 Scope Funs σ Γ x v v' :
  In _ Scope x ->  ~ In _ (image σ Funs) x ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
  Fun_inv k rho1 (M.set Γ v (M.set x v' rho2)) Scope Funs σ Γ.
Proof.
  intros Hin Hnin [tau [t [vs [Hget H]]]].
  rewrite M.gss in Hget. inversion Hget. subst v.
  do 3 eexists. rewrite M.gss; split; [ now eauto |].
  intros f v1 Hninf Hin' Hget'.
  edestruct H as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq' [Hnin' [Hget'' Happrox']]]]]]]]]]]; eauto.
  rewrite M.gsspec in Hget''.
  destruct (Coqlib.peq (σ f) Γ).
  - congruence.
  - repeat eexists; try eassumption.
    rewrite M.gso; eauto. rewrite M.gso. eassumption. 
    intros Heq''; subst. eapply Hnin. eexists; eauto.
Qed.

(** Extend the second environment with a variable in [Scope] that is different
    from [Γ] *)
Lemma Fun_inv_set_In_Scope_r_not_Γ k rho1 rho2 Scope Funs σ Γ x v :
  In _ Scope x -> Γ <> x ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  Fun_inv k rho1 (M.set x v rho2) Scope Funs σ Γ.
Proof. 
  intros Hin Hneq  [tau [t [vs [Hget H]]]].
  do 3 eexists. rewrite M.gso; [| now eauto ].
  split; [ now eauto |].
  intros f v' Hninf Hin' Hget'. 
  edestruct H
    as [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin'' [Hget'' Happrox']]]]]]]]]]]; eauto.
  destruct (Coqlib.peq (σ f) x); subst. contradiction. 
  do 8 eexists. rewrite M.gso; eauto.
Qed.


(** Extend the second environment with a variable not in [Funs] that is different
    from Γ *)
Lemma Fun_inv_set_not_In_Funs_r_not_Γ k rho1 rho2 Scope Funs σ Γ x v :
   ~ In _ (image σ Funs) x ->
   x <> Γ -> 
   Fun_inv k rho1 rho2 Scope Funs σ Γ ->
   Fun_inv k rho1 (M.set x v rho2) Scope Funs σ Γ.
Proof. 
  intros Hnin Hneq[tau [t [vs [Hget H]]]].
  do 3 eexists. rewrite M.gso; [| now eauto ].
  split; [ now eauto |].
  intros f v' Hninf Hin' Hget'.
  edestruct H
    as [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin' [Hget'' Happrox']]]]]]]]]]]; eauto.
  destruct (Coqlib.peq (σ f) x); subst.
  exfalso. eapply Hnin. now eexists; eauto.
  do 8 eexists. rewrite M.gso; eauto.
Qed.

(** Extend the first environment with a list of variables in [Scope] *)
Lemma Fun_inv_setlist_In_Scope_l k rho1 rho1' rho2 Scope Funs σ Γ xs vs :
  Included _ (FromList xs) Scope ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  setlist xs vs rho1 = Some rho1' ->
  Fun_inv k rho1' rho2 Scope Funs σ Γ.
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

(** Extend the second environment with a list of variables in [Scope] *)
Lemma Fun_inv_setlist_In_Scope_r k rho1 rho2 rho2' Scope Funs σ Γ xs vs v :
  Included _ (FromList xs) Scope -> Disjoint _ (image σ Funs) (FromList xs) ->
  Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
  setlist xs vs rho2 = Some rho2' ->
  Fun_inv k rho1 (M.set Γ v rho2') Scope Funs σ Γ.
Proof.
  revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
  - intros Hinc Hd Hfun Hset. inv Hset.
    destruct vs; [ congruence | discriminate ].
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
Lemma Fun_inv_reset k rho rho' B v Scope Funs σ Γ :
  ~ In _ (name_in_fundefs B) Γ ->
  Fun_inv k rho
          (def_funs B B (M.set Γ v rho') (M.set Γ v rho')) Scope Funs σ Γ ->
  Fun_inv k rho
          (M.set Γ v (def_funs B B  (M.set Γ v rho') (M.set Γ v rho')))
          Scope Funs σ Γ.
Proof. 
  intros Hin [tau [t [vs [Hget Hfun]]]]. 
  rewrite def_funs_neq in Hget; eauto. rewrite M.gss in Hget.
  inv Hget.
  do 3 eexists. rewrite M.gss. split; eauto.
  intros f v Hnin Hin' Hget.
  edestruct Hfun as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin' [Hget' Hcc]]]]]]]]]]]; eauto.
  subst. eapply def_funs_spec in Hget'.
  destruct Hget' as [[Hname Heq] | [Hname Hget']].
  - inv Heq. repeat eexists; eauto.
    rewrite M.gso.
    rewrite def_funs_eq. reflexivity. eassumption.
    intros Hc; subst; eauto.
  - rewrite M.gsspec in Hget'.
    destruct (Coqlib.peq (σ f) Γ).
    + subst. inv Hget'.
    + repeat eexists; eauto. rewrite M.gso. 
      rewrite def_funs_neq; eauto. 
      rewrite M.gso. eassumption.
      intros Hc; subst; eauto.
      intros Hc; subst; eauto.
Qed.

Instance Fun_inv_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==>
                   Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
         (Fun_inv).
Proof.
  constructor; subst; intros [tau [t [vs [Hget Hfun]]]];
  do 3 eexists; split; eauto; intros;
  edestruct Hfun as
      [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin' [Hget' Hcc]]]]]]]]]]];
    try rewrite H2; eauto;
  repeat eexists; try (now rewrite <- H2; eauto); try rewrite H2; eauto.
Qed.

(** Define a block of functions in the first environment and put the in the
    current scope *)
Lemma Fun_inv_def_funs_l k rho rho' B1 B1' Scope Funs σ Γ:
  Disjoint _ (image σ Funs) (name_in_fundefs B1') -> 
  Fun_inv k rho rho' Scope Funs σ Γ ->
  Fun_inv k (def_funs B1 B1' rho rho) rho'
          (Union _ (name_in_fundefs B1')  Scope) Funs σ Γ.
Proof.
  intros Hd [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto.
  intros f v' Hnin Hin Hget'.
  rewrite def_funs_neq in Hget'; eauto.
   edestruct Hfun as
      [rhof1 [B1'' [f1 [rhof2 [B2 [f2 [tau' [t' [Heq [Hnin' [Hget'' Hcc]]]]]]]]]]];
    eauto.
   repeat eexists; eauto. intros Hc; inv Hc; eauto.
   eapply Hd. econstructor; eauto. now eexists; eauto.
Qed.

(** Define a block of functions in the second environment and put the in the
    current scope *)
Lemma Fun_inv_def_funs_r k rho rho' B1 B1' Scope Funs σ Γ:
  ~ In _ (name_in_fundefs B1') Γ ->
  Disjoint _ (image σ Funs) (name_in_fundefs B1') -> 
  Fun_inv k rho rho' Scope Funs σ Γ ->
  Fun_inv k rho (def_funs B1 B1' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs σ Γ.
Proof.
  intros Hin Hd [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  intros f v' Hnin Hin' Hget'.
  edestruct Hfun as
      [rho1' [B2 [f1 [rho2' [B2' [f2 [tau2 [t2 [Heq' [Hnin' [Hget2 Happrox2]]]]]]]]]]]; eauto.
  repeat eexists; eauto.
  intros Hc; inv Hc; eauto.
  eapply Hd. econstructor; eauto. now eexists; eauto.
  rewrite def_funs_neq; eauto.
  intros Hc. eapply Hd. constructor; eauto. now eexists; eauto.
Qed.

(** Define a block of functions in both environments and put the in the
    current scope *)
Lemma Fun_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs σ Γ:
  ~ In _ (name_in_fundefs B2') Γ -> ~ In _ (name_in_fundefs B1') Γ ->
  Disjoint _ (image σ Funs) (name_in_fundefs B1') ->
  Disjoint _ (image σ Funs) (name_in_fundefs B2') ->
  (* Same_set _ (name_in_fundefs B1') (name_in_fundefs B2') -> *)
  Fun_inv k rho rho' Scope Funs σ Γ ->
  Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs σ Γ.
Proof.
  intros Hnin Hnin' Hd Hd' [t [tau [v [Hget Hfun]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  (* intros Hc. eapply Hnin. now eapply HS. *)
  intros f v' Hnin'' Hin' Hget'.
  rewrite def_funs_neq in Hget'; eauto.
  edestruct Hfun as
      [rho1' [B3 [f1 [rho2' [B3' [f2 [tau2 [t2 [Heq' [Hnin2 [Hget2 Happrox2]]]]]]]]]]]; eauto.
  repeat eexists; eauto.
  intros Hc; inv Hc; eauto.
  eapply Hd. econstructor; eauto. now eexists; eauto.
  rewrite def_funs_neq; eauto.
  intros Hc. eapply Hd'. econstructor; eauto. now eexists; eauto.
Qed.

(** * Lemmas about FV_inv *)

(** Extend the first environment with a variable in [Scope] *)
Lemma FV_inv_set_In_Scope_l k rho rho' x v Scope Funs FVs Γ :
  In var Scope x ->
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k (M.set x v rho) rho' Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. intros y n v' Hnin Hnin' Hnth Hget'.
  rewrite M.gsspec in Hget'. destruct (Coqlib.peq y x); subst.
  - contradiction. 
  - eauto. 
Qed.

(** Extend the second environment with a variable in [Scope] that is not [Γ].
    XXX : deprecated. See [FV_inv_set_r] *)
Lemma FV_inv_set_In_Scope_r k rho rho' x v Scope Funs FVs Γ :
  In var Scope x ->
  x <> Γ ->
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k rho (M.set x v rho') Scope Funs Γ FVs.
Proof.
  intros Hin Hneq HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. rewrite M.gso; eauto.
Qed.

(** Extend the first environment with a variable not in [FVs] *)
Lemma FV_inv_set_not_In_FVs_l k rho rho' x v Scope Funs Γ FVs :
  ~ List.In x FVs ->
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k (M.set x v rho) rho' Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. intros y n v' Hnin Hnin' Hnth Hget'.
  rewrite M.gsspec in Hget'. destruct (Coqlib.peq y x); subst.
  - inv Hget. eapply H; eauto.
    eapply nthN_In in Hnth.
    contradiction.
  - eauto.
Qed.

(** Extend the second environment with a variable that is not [Γ] *)
Lemma FV_inv_set_r k rho rho' x v Scope Funs Γ FVs :
  x <> Γ ->
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k rho (M.set x v rho') Scope Funs Γ FVs.
Proof.
  intros Hin HInv. destruct HInv as [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. 
  rewrite M.gso; eauto. 
Qed.

(** Extend the [Scope]. TODO : replace with monotonicity property? *)
Lemma FV_inv_extend_Scope k rho rho' Scope Funs Γ FVs x :
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k rho rho' (Union _ (Singleton _ x) Scope) Funs Γ FVs.
Proof.
  intros [tau [t  [vs [Hget H]]]].
  do 3 eexists; split; eauto. 
  intros y N v Hnin Hnin' Hnth Hget'. eapply H; eauto.
Qed.

(** Define a block of functions in both environments and put the in the
    current scope *)
Lemma FV_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs Γ FVs:
  ~ In _ (name_in_fundefs B1') Γ ->
  ~ In _ (name_in_fundefs B2') Γ ->
  FV_inv k rho rho' Scope Funs Γ FVs ->
  FV_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
          (Union _ (name_in_fundefs B1') Scope) Funs Γ FVs.
Proof.
  intros Hnin Hnin' [t [tau [v [Hget Henv]]]].
  do 3 eexists. split; eauto. 
  rewrite def_funs_neq; eauto.
  intros f N v' Hnin1 Hnin1' Hnth Hget'.
  rewrite def_funs_neq in Hget'; eauto.
Qed.

(** * Lemmas about [binding_in_map] *)

(** [binding_in_map] is anti-monotonic on its first argument *)
Lemma binding_in_map_antimon {A} S S' (rho : M.t A) :
  Included _ S' S ->
  binding_in_map S rho ->
  binding_in_map S' rho.
Proof.
  intros Hin Hv x Hs. eauto.
Qed.

(** Extend the environment with a variable and put it in the set *)
Lemma binding_in_map_set {A} x (v : A) S rho :
  binding_in_map S rho ->
  binding_in_map (Union _ S (Singleton _ x)) (M.set x v rho).
Proof. 
  intros H x' Hs. inv Hs.
  - edestruct H; eauto.
    destruct (Coqlib.peq x' x) eqn:Heq'.
    + eexists. simpl. now rewrite M.gsspec, Heq'.
    + eexists. simpl. rewrite M.gsspec, Heq'.
      eassumption.
  - inv H0. eexists. rewrite M.gss. eauto.
Qed.

(** Extend the environment with a list of variables and put them in the set *)
Lemma binding_in_map_setlist xs vs S (rho rho' : env) :
  binding_in_map S rho ->
  setlist xs vs rho = Some rho' ->
  binding_in_map (Union _ (FromList xs) S) rho'.
Proof.
  intros H Hset x' Hs.
  destruct (Decidable_FromList xs). destruct (Dec x').
  - eapply get_setlist_In_xs; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite <- setlist_not_In; eauto.
Qed.

(** Extend the environment with a block of functions and put them in the set *)
Lemma binding_in_map_def_funs B' B rho S  :
  binding_in_map S rho ->
  binding_in_map (Union _ (name_in_fundefs B) S) (def_funs B' B rho rho).
Proof.
  intros H x' Hs.
  destruct (Decidable_name_in_fundefs B). destruct (Dec x').
  - eexists. rewrite def_funs_eq; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite def_funs_neq; eauto.
Qed.


(** * Interpretation of evaluation contexts as environments *)

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

(** * Various lemmas about [Closure_conversion_fundefs] *)

Lemma image_Union {A B} S1 S2 (g : A -> B) :
  Same_set _ (image g (Union _ S1 S2)) (Union _ (image g S1) (image g S2)).
Proof. 
  split; intros x Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    left. eexists; eauto.
    right. eexists; eauto.
  - inv Hi; destruct H as [x' [Hin Heq]]; subst;
    eexists; split; eauto.
Qed.

Lemma image_Singleton {A B} x (g : A -> B) :
  Same_set _ (image g (Singleton _ x)) (Singleton _ (g x)).
Proof. 
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
    eauto.
  - destruct Hi as [x' [Hin Heq]]; subst. eexists; eauto.
Qed.

Lemma image_Empty_set {A B} (g : A -> B) :
  Same_set _ (image g (Empty_set _)) ((Empty_set _)).
Proof. 
  split; intros y Hi.
  - destruct Hi as [x' [Hin Heq]]; subst. inv Hin.
  - inv Hi.
Qed.

Lemma closure_conversion_fundefs_Same_set_image σ Funs FVs B1 B2  :
  Closure_conversion_fundefs Funs σ FVs B1 B2 ->
  Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2).
Proof. 
  intros Hcc. induction Hcc.  
  - simpl. rewrite image_Union, image_Singleton, IHHcc.
    apply Same_set_refl.
  - simpl. rewrite image_Empty_set. apply Same_set_refl.
Qed.

Lemma injectiveP_antimon {A B} (σ : A -> B) S S' :
  injectiveP σ S ->
  Included _ S' S ->
  injectiveP σ S'.
Proof. 
  intros Hinj Hinc x y Hin Hin' Heq. eauto.
Qed.

Lemma closure_conversion_fundefs_find_def σ Funs FVs B1 B2 f t1 xs e1 :
  injectiveP σ (name_in_fundefs B1) ->
  Closure_conversion_fundefs Funs σ FVs B1 B2 ->
  find_def f B1 = Some (t1, xs, e1) ->
  exists t2 Γ' C e2,
    ~ In var (Union var (image σ Funs) (Union _ (FromList xs) (bound_var e1))) Γ' /\
    find_def (σ f) B2 = Some (t2, Γ' :: xs, (C |[ e2 ]|)) /\
    Closure_conversion (FromList xs) Funs σ Γ' FVs e1 e2 C.
Proof.
  intros Hinj Hcc Hdef. induction Hcc.
  - simpl in Hdef. destruct (M.elt_eq f f0) eqn:Heq; subst.
    + inv Hdef. repeat eexists; eauto.
      simpl. rewrite Coqlib.peq_true. reflexivity.
    + edestruct IHHcc as [t2 [Γ'' [C' [e2 [Hnin [Hfind Hcc']]]]]]; eauto.
      eapply injectiveP_antimon. eassumption.
      now apply Included_Union_r.
      repeat eexists; eauto. simpl. rewrite Coqlib.peq_false. eassumption.
      intros Hc. eapply n. eapply Hinj; eauto.
      right. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct. now eauto.
      left; eauto.
  - inv Hdef.
Qed.

(** * Lemmas about [make_closures] *)

Lemma extend_gss f x x' :
  f {x ~> x'} x = x'.
Proof. 
  unfold extend. rewrite Coqlib.peq_true. reflexivity.
Qed.

Lemma extend_gso f x x' y :
  y <> x ->
  f {x ~> x'} y = f y.
Proof. 
  intros Heq. unfold extend. rewrite Coqlib.peq_false; eauto.
Qed.

Lemma image_extend_Included f x x' S :
  Included _ (image (f {x ~> x'}) S) (Union _ (image f S) (Singleton _ x')).
Proof.  
  intros y [y' [Hin Heq]]. unfold extend in Heq.
  destruct (Coqlib.peq y' x); subst; [ now eauto |] .
  left. eexists; eauto.
Qed.

Lemma image_monotonic {A B} (f : A -> B) S S' :
  Included _ S S' ->
  Included _ (image f S) (image f S').
Proof.
  intros Hin x [y [Hin' Heq]]; subst. eexists; eauto.
Qed.

Lemma make_closures_image_Included B S σ Γ C S' σ' :
  make_closures B S σ Γ C S' σ' ->
  Included _ (image σ' (name_in_fundefs B)) S.
Proof. 
  intros Hmc. induction Hmc.
  - rewrite image_Empty_set. apply Included_Empty_set.
  - simpl.
    rewrite image_Union, image_Singleton.
    apply Union_Included. apply Singleton_Included.
    now rewrite extend_gss.
    eapply Included_trans. now apply image_extend_Included.
    apply Union_Included.
    eapply Included_trans. eassumption. now eapply Subset_Setminus.
    now apply Singleton_Included.
Qed.

Lemma make_closures_free_set_Included B S σ Γ C S' σ' :
  make_closures B S σ Γ C S' σ' ->
  Included _  S' S.
Proof. 
  intros Hmc. induction Hmc.
  - now apply Included_refl.
  - eapply Included_trans. eassumption.
    now apply Subset_Setminus.
Qed.

Lemma injectiveP_extend f x x' S :
  injectiveP f S ->
  ~ In _ (image f (Setminus _ S (Singleton _ x))) x' ->
  injectiveP (f {x~>x'}) (Union _ (Singleton _ x) S).
Proof.
  intros Hinj Hnin.
  intros y y' Hin1 Hin2.
  destruct (Coqlib.peq x y); subst.
  - rewrite extend_gss. intros Heq.
    destruct (Coqlib.peq y y'); [ now eauto | ].
    rewrite extend_gso in Heq; [| now eauto ]. 
    exfalso. eapply Hnin. eexists; split; [| now eauto ].
    inv Hin2. inv H. congruence.
    constructor; eauto. intros Hc; inv Hc; congruence.
  - rewrite extend_gso; [| now eauto ].
    destruct (Coqlib.peq x y'); subst.
    + rewrite extend_gss. intros Heq. subst.
      exfalso. apply Hnin. eexists.
      split; [| reflexivity ].
      inv Hin1. inv H; congruence. 
      constructor; eauto. intros Hc; inv Hc; congruence.
    + rewrite extend_gso; [| now eauto ].
      intros Heq. eapply Hinj; eauto.
      inv Hin1. inv H; congruence. eassumption.
      inv Hin2. inv H; congruence. eassumption.
Qed.

Lemma make_closures_image_Disjoint B S σ Γ C S' σ' :
  make_closures B S σ Γ C S' σ' ->
  Disjoint _ (image σ' (name_in_fundefs B)) S'.
Proof. 
  intros Hmc. induction Hmc.
  - rewrite image_Empty_set. apply Disjoint_Empty_set_l.
  - simpl. rewrite image_Union, image_Singleton.
    rewrite extend_gss. eapply Disjoint_Union.
    + eapply Disjoint_Included_r.
      now eapply make_closures_free_set_Included; eauto.
      apply Disjoint_sym. apply Disjoint_Setminus. now apply Included_refl. 
    + eapply Disjoint_Included_l. now apply image_extend_Included.
      apply Disjoint_Union. eassumption.
      eapply Disjoint_Included_r. now eapply make_closures_free_set_Included; eauto.
      apply Disjoint_sym. eapply Disjoint_Setminus. now apply Included_refl.
Qed.

Lemma make_closures_injective B S σ Γ C S' σ' :
  Disjoint _ S (name_in_fundefs B) ->
  make_closures B S σ Γ C S' σ' ->
  injectiveP σ' (name_in_fundefs B).
Proof. 
  intros Hd Hmc. induction Hmc.
  - intros x y Hc. inv Hc. 
  - simpl. eapply injectiveP_extend. 
    + eapply IHHmc.
      eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [| eassumption ] ].
      now apply Included_Union_r.
      now apply Subset_Setminus.
    + eapply make_closures_image_Included in Hmc.
      intros Hc. 
      eapply Hmc; [| now apply Included_refl ].
      eapply image_monotonic; [ | eassumption ].
      now apply Subset_Setminus.
Qed.

(** * Lemmas about [project_var] and [project_vars] *)

Lemma project_var_free_set_Included Scope Funs σ Γ FVs x x' C S S' :
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  Included _ S' S.
Proof.
  intros Hproj. inv Hproj.
  - now apply Included_refl.
  - now apply Subset_Setminus.
  - now apply Subset_Setminus.
Qed.

Lemma project_vars_free_set_Included Scope Funs σ Γ FVs xs xs' C S S' :
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  Included _ S' S.
Proof.
  intros Hproj. induction Hproj.
  - now apply Included_refl.
  - eapply Included_trans. eassumption.
    eapply project_var_free_set_Included. eassumption. 
Qed.

Lemma project_var_not_In_free_set  Scope Funs σ Γ FVs x x' C S S'  :
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  Disjoint _ S (Union var Scope
                      (Union var (image σ Funs)
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  ~ In _ S' x'.
Proof.
  intros Hproj Hd. inv Hproj; intros Hc.
  - eapply Hd. eauto.
  - inv Hc. exfalso. eauto.
  - inv Hc. exfalso. eauto.    
Qed.

Lemma project_vars_not_In_free_set Scope Funs σ Γ FVs xs xs' C S S'  :
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  Disjoint _ S (Union var Scope
                      (Union var (image σ Funs)
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  Disjoint _ S' (FromList xs').
Proof.
  intros Hproj Hd. induction Hproj.
  - constructor. intros x Hc. inv Hc. rewrite FromList_nil in H0.
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

Lemma project_var_get Scope Funs σ Γ FVs S1 x x' C1 S2 rho1 rho2 y:
  project_var Scope Funs σ Γ FVs S1 x x' C1 S2 ->
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

Lemma project_vars_get Scope Funs σ Γ FVs S1 xs xs' C1 S2 rho1 rho2 y:
  project_vars Scope Funs σ Γ FVs S1 xs xs' C1 S2 ->
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

Lemma project_var_getlist Scope Funs σ Γ FVs S1 x x' C1 S2 rho1 rho2 ys :
  project_var Scope Funs σ Γ FVs S1 x x' C1 S2 ->
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


Lemma project_vars_getlist Scope Funs σ Γ FVs S1 xs xs' C1 S2 rho1 rho2 ys :
  project_vars Scope Funs σ Γ FVs S1 xs xs' C1 S2 ->
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

Lemma project_var_In_Union Scope Funs σ Γ FVs S x x' C S' :
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  In _ (Union var Scope (Union var Funs (FromList FVs))) x.
Proof.
  intros Hvar. inv Hvar; eauto.
  right; right. eapply nthN_In. eassumption.
Qed.

Lemma project_vars_In_Union Scope Funs σ Γ FVs S xs xs' C S' :
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  Included var (FromList xs) (Union var Scope (Union var Funs (FromList FVs))).
Proof.
  intros Hvar. induction Hvar; eauto.
  - rewrite FromList_nil. now apply Included_Empty_set.
  - rewrite FromList_cons.
    eapply Union_Included; [| eassumption ].
    eapply Singleton_Included. eapply project_var_In_Union.
    eassumption.
Qed.

Lemma project_var_not_In Scope Funs σ Γ FVs S x x' C S' :
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
      
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  ~ In _ S x.
Proof.
  intros Hd  Hproj. inv Hproj; intros Hin; try now eapply Hd; eauto.
  eapply nthN_In in H1. eapply Hd. eauto.
Qed.

Lemma project_vars_Disjoint Scope Funs σ Γ FVs S xs xs' C S' :
  Disjoint _ S (Union var Scope
                      (Union var Funs
                             (Union var (FromList FVs) (Singleton var Γ)))) ->      
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  Disjoint _ S (FromList xs).
Proof.
  revert xs' C S S'; induction xs; intros xs' C S S' Hd Hproj.
  - rewrite FromList_nil. now eapply Disjoint_Empty_set_r.
  - inv Hproj. rewrite FromList_cons.
    eapply Disjoint_sym; eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Singleton. eapply project_var_not_In; eauto.
    inv H7.
    + eapply IHxs; [| eassumption ]. eauto.
    + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y')) (FromList xs)).
      { eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Subset_Setminus. }
      eapply Disjoint_Included_l with (s3 := Union _ S (Singleton _ y')).
      now apply Included_Union_l.
      rewrite (@Union_Setminus _ _ _ _).
      eapply Disjoint_Union; eauto.
      eapply project_vars_In_Union in H11. 
      constructor. intros x Hc. inv Hc.
      inv H2. eapply Hd. constructor.
      eassumption. eapply H11 in H3. inv H3; eauto.
      inv H2; eauto.
    + assert (Hd1 : Disjoint _ (Setminus var S (Singleton var y')) (FromList xs)).
      { eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply Subset_Setminus. }
      eapply Disjoint_Included_l with (s3 := Union _ S (Singleton _ y')).
      now apply Included_Union_l.
      rewrite (@Union_Setminus _ _ _ _).
      eapply Disjoint_Union; eauto.
      eapply project_vars_In_Union in H11.  
      constructor. intros x Hc. inv Hc.
      inv H3. eapply Hd. constructor.
      eassumption. eapply H11 in H4. inv H4; eauto.
      inv H3; eauto.
Qed.


(** * Lemmas about the existance of the interpretation of an evaluation context *)

Lemma project_var_ctx_to_rho Scope Funs σ Γ FVs x x' C S S' v1 k rho1 rho2 :
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  FV_inv k rho1 rho2 Scope Funs Γ FVs ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  M.get x rho1 = Some v1 ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros Hproj [t' [tau' [vs' [Hget3' Henv]]]]
         [t [tau [vs [Hget3 Hfun]]]] Hget1; inv Hproj.
  - eexists; econstructor; eauto.
  - edestruct Hfun as
        [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hnin [Hget2 Happrox2]]]]]]]]]]]; eauto.
    eexists; econstructor; eauto.
    constructor.
  - rewrite Hget3 in Hget3'; inv Hget3'.
    edestruct Henv as [y [Hnth Hcc]]; eauto.
    eexists. econstructor; eauto. constructor. 
Qed.

Lemma make_closures_ctx_to_rho B S σ Γ C S' σ' k rho1 rho2 :
  make_closures B S σ Γ C S' σ' ->
  unique_functions B ->
  Disjoint _ S (name_in_fundefs B) ->
  ~ In _ (name_in_fundefs B) Γ ->
  Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ' Γ ->
  (forall f, In _ (name_in_fundefs B) f -> exists v, M.get f rho1 = Some v) ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros Hclo. revert rho1 rho2. induction Hclo; intros rho1 rho2 Hun Hd Hnin Hfun Hyp. 
  - eexists; constructor. 
  - destruct (Hyp f) as [v' Hget'].
    now left; eauto.
    edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
    edestruct Hfun' as
        [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2 [t2 [Heq' [Hnin' [Hget2 Happrox2]]]]]]]]]]]; eauto.
    now apply not_In_Empty_set.
    now left; eauto. inv Hun.
    edestruct IHHclo as [rho2' Hctx]; [ eassumption | | | | | ]. 
    + eapply Disjoint_Included_l. now apply Subset_Setminus.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply Included_Union_r.
    + intros Hc; eapply Hnin; right; eauto.
    + eapply Fun_inv_set_not_In_Funs_r_not_Γ with (x := f).
      intros Hin. eapply make_closures_image_Included in Hclo.
      eapply Hd. constructor; [| now left; eauto ].
      eapply Hclo. eassumption. 
      intros Hc; subst. eapply Hnin. now left; eauto.
      do 3 eexists; split; eauto; intros.
      edestruct Hfun' as
          [rho1'' [B1' [f1' [rho2'' [B2' [f2' [tau2' [t2' [Heq'' [Hnin'' [Hget2' Happrox2']]]]]]]]]]]; eauto.
      right; eauto.
      subst. repeat eexists; eauto. intros Hc; inv Hc.
      unfold extend in Hget2'. rewrite Coqlib.peq_false in Hget2'. eassumption.
      intros Hc; subst; contradiction.
    + intros. eapply Hyp. right; eauto.
    + eexists. econstructor; eauto.
      unfold extend in Hget2. rewrite Coqlib.peq_true in Hget2. eassumption.
Qed.

Lemma project_vars_ctx_to_rho Scope Funs σ Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
  Disjoint _ S (Union var Scope
                      (Union var (image σ Funs)
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  FV_inv k rho1 rho2 Scope Funs Γ FVs ->
  getlist xs rho1 = Some vs1 ->
  exists rho2', ctx_to_rho C rho2 rho2'.
Proof. 
  intros HD Hvars Hfun [tau [t [vs [Hget Henv]]]].
  assert (HD' := Hvars).
  (* apply project_vars_Disjoint in HD'; [ | eassumption ].  *)
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
      [| eassumption  | eassumption | | | eassumption | eassumption | ].
    + eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included. eassumption.
    + do 3 eexists; split.
      erewrite <- project_var_get; eauto.
      intros Hin. eapply HD. eauto.
      intros f v' Hnin Hin Hgetv'.
      edestruct Hfun as [tau1 [t1 [vs' [Hget1 Hfun']]]].
      rewrite Hget1 in Hget. inv Hget.
      edestruct Hfun' as
          [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2 [t2 [Heq' [Hnin2 [Hget2 Happrox2]]]]]]]]]]];
        eauto.
      subst. repeat eexists; eauto.
      erewrite <- project_var_get; eauto. 
      intros Hin'. eapply HD. constructor. now eauto.
      right. left. eexists. now eauto.
    + erewrite <- project_var_get; eauto.
      intros Hin. eapply HD. eauto.
    + exists rho2''. eapply ctx_to_rho_comp_ctx_f_r; eassumption.
Qed.

(** * Correctness lemmas *)

Lemma injectiveP_Union_Disjoint {A B} (f : A -> B) S1 S2 :
  injectiveP f (Union _ S1 S2) ->
  Disjoint _ S1 S2 ->
  Disjoint _ (image f S1) (image f S2).
Proof. 
  intros Hinj. constructor; intros x Hin. inv Hin. 
  destruct H0 as [y [Hin Heq]]. destruct H1 as [y' [Hin' Heq']].
  subst. eapply Hinj in Heq'; eauto. eapply H. subst; eauto.
Qed.

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
      rewrite !Union_assoc. now apply Included_Union_r.
  - inv H.
Qed.

(** Correctness of [closure_conversion_fundefs]. Basically un-nesting the nested
    induction that is required by the correctness of [Closure_conversion] *) 
Lemma Closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
      Scope Γ FVs Funs' σ FVs' t tau vs:
  (* The IH *)
  (forall m : nat,
        m < k ->
        forall (e : exp) (rho rho' : env) (e' : exp)
          (Scope Funs : Ensemble var) σ (Γ : var) (FVs : list var)
          (C : exp_ctx),
        cc_approx_env_P Scope m rho rho' ->
        ~ In var (bound_var e) Γ ->
        binding_in_map (occurs_free e) rho ->
        fundefs_names_unique e ->
        injectiveP σ Funs ->
        Disjoint var (image σ Funs) (bound_var e) ->
        Fun_inv m rho rho' Scope Funs σ Γ ->
        FV_inv m rho rho' Scope Funs Γ FVs ->
        Closure_conversion Scope Funs σ Γ FVs e e' C ->
        cc_approx_exp m (e, rho) (C |[ e' ]|, rho')) ->
  Same_set _ (occurs_free_fundefs B1) (FromList FVs) ->
  fundefs_names_unique_fundefs B1 ->
  fundefs_names_unique_fundefs B1' ->
  binding_in_map (occurs_free_fundefs B1) rho ->
  Closure_conversion_fundefs (name_in_fundefs B1) σ FVs B1 B2 ->
  Closure_conversion_fundefs Funs' σ FVs' B1' B2' ->
  Disjoint _ (image σ (name_in_fundefs B1)) (bound_var_fundefs B1) ->
  Disjoint _ (image σ (name_in_fundefs B1')) Scope ->
  Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2) ->
  injectiveP σ (name_in_fundefs B1) ->
  injectiveP σ (name_in_fundefs B1') ->
  ~ In _ (name_in_fundefs B1) Γ ->
  ~ In _ (name_in_fundefs B1') Γ ->
  ~ In _ (name_in_fundefs B2) Γ ->
  ~ In _ (name_in_fundefs B2') Γ ->
  closure_env k rho (Empty_set _) (Empty_set _) vs FVs ->
  Fun_inv k (def_funs B1 B1' rho rho)
          (def_funs B2 B2' (M.set Γ (Vconstr tau t vs) rho') (M.set Γ (Vconstr tau t vs) rho'))
          Scope (name_in_fundefs B1') σ Γ.
Proof.
  revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t tau vs.
  induction k as [k IHk] using lt_wf_rec1.
  induction B1'; 
    intros rho rho' B2 B1 B2' Scope Γ FVs Funs' FVs' t' tau' vs
           IHe Hs Hun Hun' Hfv Hcc Hcc' Hd Hd'' Hseq Hinj Hinj' Hnin1 Hnin1' Hnin2 Hnin2' Henv.
  - inv Hcc'. simpl.
    eapply Fun_inv_set. 
    + eapply IHB1'; eauto.
      * intros B H. inv H; eauto. specialize (Hun' (Fcons v t l e B1') (or_intror eq_refl)).
        inv Hun'; eauto.
      * eapply Disjoint_Included_l; [| eassumption ].
        eapply image_monotonic. now apply Included_Union_r.
      * eapply injectiveP_antimon. eassumption. now apply Included_Union_r.
      * intros Hc. apply Hnin1'. simpl; eauto.
      * intros Hc. apply Hnin2'. simpl; eauto.
    + intros Hc. eapply Hnin2'. subst. left. eauto.
    + intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
      left. eauto.
    + simpl in Hinj'. eapply injectiveP_Union_Disjoint in Hinj'.
      intros Hc. eapply Hinj'. constructor; eauto. eexists; eauto.
      eapply Disjoint_sym. eapply Disjoint_Singleton.
      specialize (Hun' (Fcons v t l e B1') (or_intror eq_refl)).
      inv Hun'; eauto.
    + rewrite def_funs_neq.
      rewrite M.gss. reflexivity.
      intros Hc. eapply Hnin2'. right. eauto.
    + exists tau', t.
      rewrite cc_approx_val_eq.
      intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.
      edestruct setlist_length
      with (rho' := def_funs B2 B2 (M.set Γ (Vconstr tau' t' vs) rho')
                             (M.set Γ (Vconstr tau' t' vs) rho')) as [rho2' Hset'].
      eassumption. now eauto.
      edestruct closure_conversion_fundefs_find_def
        as [t2 [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]]; [  |  | eassumption |].
      eassumption. eassumption.
      exists t2, Γ'', xs1. do 2 eexists.
      split. eassumption. split.
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
      * eapply Disjoint_Included_r; [| now apply Hd ].
        eapply Included_trans;
          [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
        rewrite !Union_assoc. now apply Included_Union_r.
      * assert
          (Fun_inv j (def_funs B1 B1 rho rho)
                   (def_funs B2 B2 (M.set Γ (Vconstr tau' t' vs) rho')
                             (M.set Γ (Vconstr tau' t' vs) rho'))
                   (FromList xs1) (name_in_fundefs B1) σ Γ).
        { eapply IHk; try eassumption.
          - intros. eapply IHe; eauto. omega. 
          - eapply Disjoint_Included_r; [| eassumption ].
            eapply Included_trans;
              [| now eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eauto ].
            apply Included_Union_mon_r. now apply Included_Union_l.
          - intros x1 N v1 Hnin3 Hnin4 Hnth Hget.
            edestruct Henv as [v2 [Hnth' Happ']]; eauto.
            eexists; split; eauto. eapply cc_approx_val_monotonic.
            eassumption. omega. } 
        eapply Fun_inv_rename with (Γ := Γ).
        intros Hin. eapply Hseq in Hin. contradiction.
        intros Hin. eapply Hnin''. left; eassumption.
        eapply Fun_inv_setlist_In_Scope_l; [ now apply Included_refl | |].
        eapply Fun_inv_setlist_In_Scope_r; [ now apply Included_refl | | | eassumption ].  
        eapply Disjoint_Included_r; [|  eassumption ].
        eapply Included_trans;
          [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
        right; eauto.
        eapply Fun_inv_reset; [| eassumption ]. eassumption. now eauto.
      * do 3 eexists. split.
        rewrite M.gss. reflexivity.
        intros x N v1 Hnin3 Hnin4 Hnth Hget'. 
        edestruct Henv as [v' [Hnth'' Hcc'']]; eauto.
        intros Hc. now inv Hc.
        intros Hc. now inv Hc.
        erewrite <- def_funs_neq.
        erewrite setlist_not_In. eassumption.
        now eauto. now eauto. now eauto.
        eexists; eauto. split. eassumption.
        eapply cc_approx_val_monotonic. eassumption. omega.
      * eassumption.
  - do 3 eexists.
    rewrite def_funs_neq. rewrite M.gss. split; eauto.
    intros. inv H0. inv Hcc'. simpl. eauto.
Qed.

(** Correctness of [project_var] *)
Lemma project_var_correct k rho1 rho2 rho2'
      Scope Funs σ Γ FVs x x' C S S'  :
  project_var Scope Funs σ Γ FVs S x x' C S' ->
  cc_approx_env_P Scope k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  FV_inv k rho1 rho2 Scope Funs Γ FVs ->
  ctx_to_rho C rho2 rho2' ->
  Disjoint _ S (Union var Scope
                      (Union var (image σ Funs)
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  ~ In _ S' x' /\
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs σ Γ /\
  FV_inv k rho1 rho2' Scope Funs Γ FVs /\
  cc_approx_var_env k rho1 rho2' x x'.
Proof.
  intros Hproj Hcc Hfun Henv Hctx Hd.
  inv Hproj.
  - inv Hctx. repeat split; eauto. intros Hc. eapply Hd; eauto.
  - inv Hctx. inv H12.
    repeat split; eauto.
    + intros Hc. inv Hc. eauto.
    + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
      intros Hc. eapply Hd. eauto.
    + (* TODO : make lemma *)
      edestruct Hfun as [tau' [t' [vs' [Hget Hfun']]]].
      rewrite Hget in H10; inv H10.
      do 3 eexists. rewrite M.gso; [ | now intros Heq; subst; eapply Hd; eauto ].
      split; eauto. intros f v Hnin Hin Hget''.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hnin' [Hget' Hcc']]]]]]]]]]]; eauto.
      subst. repeat eexists; eauto.
      rewrite M.gso. eassumption. 
      intros Hc. subst; eapply Hd; constructor; eauto. right; left.
      eexists; eauto.
    + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
      eassumption.
    + intros v Hget. eexists. rewrite M.gss. split; eauto.
      edestruct Hfun as [tau' [t' [vs' [Hget' Hfun']]]].
      rewrite Hget' in H10; inv H10.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hnin' [Hget'' Hcc']]]]]]]]]]]; eauto.
      subst. rewrite Hget'' in H11. inv H11.
      now rewrite cc_approx_val_eq in *.
  - inv Hctx. inv H12.
    repeat split; eauto.
    + intros Hc. inv Hc. eauto.
    + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
      intros Hc. eapply Hd. eauto.
    + edestruct Hfun as [tau' [t' [vs' [Hget Hfun']]]].
      rewrite Hget in H10; inv H10.
      do 3 eexists. rewrite M.gso; [ | now intros Heq; subst; eapply Hd; eauto ].
      split; eauto. intros f v' Hnin Hin Hget''.
      edestruct Hfun' as
          [rhof1 [B1 [f1 [rhof2 [B2 [f2 [tau'' [t'' [Heq [Hnin' [Hget' Hcc']]]]]]]]]]]; eauto.
      subst. repeat eexists; eauto.
      rewrite M.gso. eassumption. 
      intros Hc. subst; eapply Hd; eauto. constructor; eauto. right; left.
      eexists; eauto.
    + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
      eassumption.
    + intros v' Hget. eexists. rewrite M.gss. split; eauto.
      edestruct Henv as [tau' [t' [vs' [Hget' Henv']]]].
      rewrite Hget' in H10; inv H10.
      edestruct Henv' as [v'' [Hnth Hcc']]; eauto.
      rewrite H11 in Hnth. now inv Hnth.
Qed.

(** Correctness of [project_vars] *)
Lemma project_vars_correct k rho1 rho2 rho2'
      Scope Funs σ Γ FVs xs xs' C S S' :
  project_vars Scope Funs σ Γ FVs S xs xs' C S' ->
  cc_approx_env_P Scope k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs σ Γ ->
  FV_inv k rho1 rho2 Scope Funs Γ FVs ->
  ctx_to_rho C rho2 rho2' ->
  Disjoint _ S (Union var Scope
                      (Union var (image σ Funs)
                             (Union var (FromList FVs) (Singleton var Γ)))) ->
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs σ Γ /\
  FV_inv k rho1 rho2' Scope Funs Γ FVs /\
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
Lemma make_closures_correct k rho1 rho2 rho2' B S σ Γ' C S' σ' σ'' Scope Funs FVs Γ :
  make_closures B S σ Γ' C S' σ' ->
  unique_functions B ->
  ~ In _ (name_in_fundefs B) Γ ->
  ~ In _ (name_in_fundefs B) Γ' ->
  Included _ (name_in_fundefs B) Scope ->
  Disjoint _ S (name_in_fundefs B) ->
  cc_approx_env_P (Setminus _ Scope (name_in_fundefs B)) k rho1 rho2 ->
  Fun_inv k rho1 rho2 Scope Funs σ'' Γ ->  
  FV_inv k rho1 rho2 Scope Funs Γ FVs ->
  Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ' Γ' ->
  ctx_to_rho C rho2 rho2' ->
  cc_approx_env_P Scope k rho1 rho2' /\
  Fun_inv k rho1 rho2' Scope Funs σ'' Γ /\
  FV_inv k rho1 rho2' Scope Funs Γ FVs.
Proof.
  intros Hmake. revert k rho1 rho2 rho2' Scope Funs FVs Γ.
  induction Hmake;
    intros k rho1 rho2 rho2' Scope Funs FVs Γ1 Hun Hnin1 Hnin2
           Hsub Hd Hcc Hfun Henv Hfun' Hctx.
  - inv Hctx. repeat split; eauto.
    simpl in *.
    now rewrite Setminus_Empty_set_Same_set in Hcc. 
  - eapply ctx_to_rho_comp_ctx_l in Hctx; [| apply Constr_cc; constructor ].
    destruct Hctx as [rho2'' [Hctx1 Hctx2]].
    inv Hctx1. inv H10. inv Hun.
    edestruct IHHmake as [Hcc1 [Hfun1 Henv1]];
      [ eassumption | | | | | | | | | eassumption | ].  
    + intros Hc. eapply Hnin1. right. now apply Hc. 
    + intros Hc. eapply Hnin2. right. now apply Hc.
    + eapply Included_trans; [| now apply Hsub ].
      now eapply Included_Union_r.
    + eapply Disjoint_Included_l. now apply Subset_Setminus.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply Included_Union_r.
    + eapply cc_approx_env_P_antimon;
      [| now apply (@Included_Union_Setminus _ _ (Singleton var f) _) ]. 
      rewrite Setminus_Union, (Union_sym (name_in_fundefs B)).
      eapply cc_approx_env_P_union.
      eapply cc_approx_env_P_set_not_in_P_r. eassumption.
      intros Hc. inv Hc. now eauto.
      intros f'' Hs v Hget'. inv Hs.
      edestruct Hfun' as [tau2 [t2 [vs2 [Hget2 Hfun2]]]]. 
      edestruct Hfun2
        as [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2' [t2' [Heq' [Hnin2' [Hget2' Happrox2]]]]]]]]]]];
      [| | eassumption |]. now eapply not_In_Empty_set. now left; eauto.
      unfold extend in Hget2'. rewrite Coqlib.peq_true in Hget2'. 
      subst. eexists; split. 
      rewrite M.gss. reflexivity.
      rewrite H8 in Hget2. inv Hget2. rewrite H9 in Hget2'. inv Hget2'.
      rewrite cc_approx_val_eq in *. simpl. now eauto.
    + eapply Fun_inv_set_In_Scope_r_not_Γ ; [| | eassumption ].
      * eapply Hsub. now left. 
      * intros Hc; subst. eapply Hnin1. left; eauto.
    + eapply FV_inv_set_r; [| eassumption ].
      intros Hc; subst. eapply Hnin1. left; eauto.
    + edestruct Hfun' as [tau2 [t2 [vs2 [Hget2 Hfun2]]]]. 
      do 3 eexists; split; eauto.
      rewrite M.gso. eassumption.
      intros Hc; subst. eapply Hnin2. left; eauto.
      intros f'' v' _ Hnin Hgetf. 
      edestruct Hfun2
        as [rho1f' [B1 [f1 [rho2f' [B2 [f2 [tau2' [t2' [Heq' [Hnin2' [Hget2' Happrox2]]]]]]]]]]];
        [| | eassumption |].
      now eapply not_In_Empty_set. now right; eauto.
      repeat eexists; eauto. intros Hc; now inv Hc. 
      rewrite M.gso. unfold extend in Hget2'.  
      rewrite Coqlib.peq_false in Hget2'. eassumption.
      intros Hc; subst. contradiction.
      eapply make_closures_image_Included in Hmake. intros Hc; subst.
      eapply Hd. constructor; [| now left; eauto ].
      eapply Hmake. eexists; eauto. 
    + eauto.
Qed.

Lemma injectiveP_Union_not_In_image {A B} (f : A -> B) S1 S2 :
  injectiveP f (Union _ S1 S2) ->
  Disjoint _ S1 S2 ->
  Disjoint _ (image f S1) (image f S2).
Proof. 
  intros Hinj. constructor; intros x Hin. inv Hin. 
  destruct H0 as [y [Hin Heq]]. destruct H1 as [y' [Hin' Heq']].
  subst. eapply Hinj in Heq'; eauto. eapply H. subst; eauto.
Qed.

(** Correctness of [Closure_conversion] *)
Lemma Closure_conversion_correct k rho rho' e e' Scope Funs σ Γ FVs C :
  (* [Scope] invariant *)
  cc_approx_env_P Scope k rho rho' ->
  (* [Γ] (the current environment parameter) is not bound in e *)
  ~ In _ (bound_var e) Γ ->
  (* The free variables of e are defined in the environment *)
  binding_in_map (occurs_free e) rho ->
  (* The blocks of functions have unique function names *)
  fundefs_names_unique e ->
  (* function renaming is injective in the [Funs] subdomain *)
  injectiveP σ Funs ->
  (* function renaming codomain is not shadowed by other vars *)
  Disjoint _ (image σ Funs) (bound_var e) ->
  (* [Fun] invariant *)
  Fun_inv k rho rho' Scope Funs σ Γ ->
  (* Free variables invariant *)
  FV_inv k rho rho' Scope Funs Γ FVs ->
  (* [e'] is the closure conversion of [e] *)
  Closure_conversion Scope Funs σ Γ FVs e e' C ->
  cc_approx_exp k (e, rho) (C |[ e' ]|, rho').
Proof.
  revert k e rho rho' e' Scope Funs σ Γ FVs C.
  induction k as [k IHk] using lt_wf_rec1.
  induction e using exp_ind';
    intros rho1 rho2 e' Scope Funs σ Γ FVs C Happrox Hnin HFVs Hun Hinj Hd Hfun Henv Hcc.
  - (* Case Econstr *)
    inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    edestruct Hvar as [v' [Hget' Happ']]; eauto. 
    intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H9; eauto. inv H9.
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
      [| now eauto | | | eassumption | | | | eassumption | eassumption | eassumption | ]. 
    + eapply cc_approx_env_P_extend with (v2 := Vconstr tau' t0 v').
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.
      rewrite cc_approx_val_eq. constructor; eauto.
      now eapply Forall2_Forall2_asym_included.
    + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      eapply occurs_free_Econstr_Included. 
    + intros f Hfin. eauto.
    + eapply Disjoint_Included_r; [| eassumption ].
      rewrite bound_var_Econstr. now apply Included_Union_l.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Disjoint_Singleton. intros Hc. eapply Hd; constructor; eauto.
    + eapply FV_inv_set_In_Scope_l. now constructor.
      eapply FV_inv_set_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply FV_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
  - (* Case [Ecase x []] *)
    inv Hcc. destruct pats'; [| now inv H10 ].
    intros v1 c1 Hleq Hstep. inv Hstep. inv H4. 
  - (* Case [Ecase x ((c, p) :: pats] *)
    inv Hcc. destruct pats'; [ now inv H10 |]. 
    inversion H10 as [ | [c1 p1] [c2 p2] l1 l2 [Heq [C' [e' [Heq' Hcc]]]] Hall ];
      simpl in Heq, Heq'; subst.
    intros v1 c1 Hleq Hstep. inv Hstep.
    simpl in H4.  destruct (M.elt_eq c2 t) eqn:Heq; subst. 
    { inv H4. inv H7. 
      - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct vcon; try contradiction. inv Happrox2.
        edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
          | eassumption | | eassumption | eassumption
          | eassumption | eassumption | eassumption | ].
        + eapply binding_in_map_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        + intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor. 
        + eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Ecase_cons. now apply Included_Union_l.
        + repeat eexists; [| eassumption ].
          econstructor; eauto. simpl. now rewrite Heq.
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H2 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe as [v2 [c2 [Hstep2 Happrox2]]];
          [| now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | | 
           | eassumption | | | | eassumption | eassumption | eassumption
           | repeat eexists; [| eassumption ]; econstructor; eauto;
             econstructor; eauto;
             [ rewrite M.gss ; reflexivity | simpl; now rewrite Heq ] ].
        + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
          intros Hc. eapply H1. eauto.
        + eapply binding_in_map_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        + intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor.
        + eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Ecase_cons. now apply Included_Union_l.
        + eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ]. 
          intros Hc. eapply H1. now eauto.
          intros Heq'; subst. eapply H1. now eauto.
        + eapply FV_inv_set_r. intros Hc. subst. eapply H1. now eauto.
          eassumption. }
    { inv H4. assert (H7' := H7). inv H7. 
      - edestruct Happrox as [vcon [Hget' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct vcon; try contradiction. inv Happrox2.
        edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
          | eassumption | | eassumption | eassumption | now econstructor; eauto
          | eassumption | now econstructor; eauto | ].
        + eapply binding_in_map_antimon; [| eassumption ].
          intros x Hin. inv Hin; eauto.
        + intros f Hfin. eapply Hun. inv Hfin. 
          econstructor; eauto. constructor 2. eassumption.
        + eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Ecase_cons. now apply Included_Union_r.
        + inv Hstep2. repeat eexists; [| eassumption ].
          econstructor; eauto. simpl. rewrite Hget' in H6. inv H6.
          now rewrite Heq. 
      - edestruct Hfun as [tau1 [t1 [vs1 [Hget1 Hfun']]]].
        edestruct Hfun' as
            [rho1' [B1 [f1 [rho2' [B2 [f2 [tau2 [t2 [Heq' [Hget2 Happrox2]]]]]]]]]];
          [| | now apply H2 | ]; eauto. congruence.
      - edestruct Henv as [tau1 [t1 [vs1 [Hget Henv']]]]; eauto.
        edestruct Henv' as [v' [Hnth' Happrox2]]; eauto.
        rewrite cc_approx_val_eq in Happrox2.
        destruct v'; try contradiction. inv Happrox2.
        edestruct IHe0 as [v2 [c2' [Hstep2 Happrox2]]];
          [ eassumption
          | now intros Hc; eapply Hnin; rewrite bound_var_Ecase_cons; eauto | |
          | eassumption | | eassumption | eassumption | now econstructor; eauto
          | eassumption | now econstructor; eauto | ].
        + eapply binding_in_map_antimon; [|  eassumption ].
          intros x Hin. inv Hin; eauto.
        + intros f Hfin. eapply Hun. inv Hfin.
          econstructor; eauto. constructor 2. eassumption.
        + eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Ecase_cons. now apply Included_Union_r.
        + inv Hstep2; rewrite Hget in H17; inv H17; rewrite Hnth' in H18; inv H18.
          inv H19. repeat eexists; [| eassumption ]; econstructor; eauto.
          econstructor; eauto. simpl.
          rewrite M.gss in H11. inv H11. now rewrite Heq. }
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
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
      [| now eauto | | | eassumption | | |
       | eassumption | eassumption | eassumption | ].
    + eapply cc_approx_env_P_extend; [| eassumption ].
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.      
    + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      eapply occurs_free_Eproj_Included. 
    + intros f Hfin. eauto.
    + eapply Disjoint_Included_r; [| eassumption ].
      rewrite bound_var_Eproj. now apply Included_Union_l.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Disjoint_Included_r; [| eassumption ].
      rewrite bound_var_Eproj. now apply Included_Union_r.
    + eapply FV_inv_set_In_Scope_l. now constructor.
      eapply FV_inv_set_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply FV_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
  - (* Case Efun -- the hardest one! *) 
    inv Hcc.
    assert (Ha : exists vs, getlist FVs' rho1 = Some vs).
    { eapply In_getlist. intros x Hin. eapply HFVs. 
      rewrite occurs_free_Efun, H1. eauto. }
    destruct Ha as [vs Hgetlist].
    intros v1 c1 Hleq Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; [ | eassumption | | | | ]; eauto.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    assert (Hsuf :
              cc_approx_exp k (e, def_funs f2 f2 rho1 rho1)
                            (C0 |[ Ce |[ e'0 ]| ]|, def_funs B' B' (M.set Γ' (Vconstr tau t v') rho2')
                                       (M.set Γ' (Vconstr tau t v') rho2'))).
    { edestruct make_closures_ctx_to_rho as [rho2'' Htp_rho']; eauto.
      - eapply Disjoint_Included_r; [| eassumption ].
        apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
      - intros Hc. eapply H4. now eauto.
       - eapply Closure_conversion_fundefs_correct; eauto. 
        + intros f Hfin. inv Hfin; eauto.
        + intros f Hfin. inv Hfin; eauto.
        + eapply binding_in_map_antimon; [| eassumption ].
          intros x H. eapply Free_Efun2. eassumption.
        + eapply Disjoint_Included_l .
          eapply make_closures_image_Included; eassumption.
          eapply Disjoint_Included_r; [| eassumption ].
          now apply Included_Union_l.
        + now apply Disjoint_Empty_set_r. 
        + eapply closure_conversion_fundefs_Same_set_image. eassumption.
        + eapply make_closures_injective; [| eassumption ].
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
        + eapply make_closures_injective; [| eassumption ].
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
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
          edestruct getlist_nth_get as [v' [Hnth' Hget'']].
          now apply Hgetlist. eassumption.
          edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
          eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
      - intros g' Hin. eexists. now rewrite def_funs_eq.
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
        + intros Hc. eapply H4. now eauto.
        + eapply Included_Union_l.
        + eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
        + eapply cc_approx_env_P_def_funs_not_In_P_l.
          eapply Disjoint_Setminus. now apply Included_refl.
          eapply cc_approx_env_P_def_funs_not_In_P_r.
          erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); [| eassumption ].
          eapply Disjoint_Included_r.
          now eapply make_closures_image_Included; eauto.
          eapply Disjoint_Included_l; [| eapply Disjoint_sym; eassumption ].
          rewrite Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r.
          do 2 apply Included_Union_mon_r. eapply Included_Union_mon_l.
          now apply Subset_Setminus.
          eapply cc_approx_env_P_set_not_in_P_r.
          eapply cc_approx_env_P_antimon. eassumption.
          rewrite Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r.
          eapply Setminus_Included. now apply Included_refl.
          intros Hin. inv Hin. inv H. eauto. eapply H4. eauto.
        + eapply Fun_inv_def_funs.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].            
            eapply H6. constructor.
            eapply make_closures_image_Included. eassumption. eassumption.
            rewrite !Union_assoc. now apply Included_Union_r.
          * intros Hc. eapply Hnin. rewrite bound_var_Efun.
            eapply Included_Union_l. now apply name_in_fundefs_bound_var_fundefs.
          * eapply Disjoint_Included_r; [| eassumption ].
            rewrite bound_var_Efun. apply Included_Union_mon_l.
            now apply name_in_fundefs_bound_var_fundefs.
          * erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].   
            eapply Disjoint_Included_r.
            eapply make_closures_image_Included. eassumption.
            eapply Disjoint_Included_l; [| eapply Disjoint_sym; eassumption ].
            do 3 apply Included_Union_mon_r. eapply Included_Union_l.
          * eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | ].
             intros Hc. eapply H4. now eauto.
            intros Hc. subst. eapply H4. constructor. now eauto.
            now eauto. now eauto.
        + eapply FV_inv_def_funs.
          * intros Hc. eapply Hnin. constructor. 
            now eapply name_in_fundefs_bound_var_fundefs.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].            
            eapply H6. constructor.
            eapply make_closures_image_Included. eassumption. eassumption.
            rewrite !Union_assoc. now apply Included_Union_r.
          * eapply  FV_inv_set_r.
            intros Hc. subst. eapply H4. constructor; eauto.
            eassumption. 
        + eapply Closure_conversion_fundefs_correct; eauto.
          * intros f Hfin. inv Hfin; eauto.
          * intros f Hfin. inv Hfin; eauto.
          * eapply binding_in_map_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption.
          * eapply Disjoint_Included_l.
            eapply make_closures_image_Included. eassumption.
            eapply Disjoint_Included_r; [| eassumption ].
            now apply Included_Union_l.
          * now apply Disjoint_Empty_set_r.
          * eapply closure_conversion_fundefs_Same_set_image. eassumption.
          * eapply make_closures_injective; [| eassumption].
            eapply Disjoint_Included_r; [| eassumption ].
            apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
          * eapply make_closures_injective; [| eassumption].
            eapply Disjoint_Included_r; [| eassumption ].
            apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
          * intros Hc. eapply H4. now eauto.
          * intros Hc. eapply H4. now eauto.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].            
            eapply H6. constructor.
            eapply make_closures_image_Included. eassumption. eassumption.
            now eauto.
          * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].            
            eapply H6. constructor.
            eapply make_closures_image_Included. eassumption. eassumption.
            now eauto.
          * edestruct Hvar as [vs' [Hgetlist' Hall]]; eauto.
            intros x N v _ _ Hnth Hget. rewrite Hget' in Hgetlist'; inv Hgetlist'.
            edestruct getlist_nth_get as [v' [Hnth' Hget'']].
            now apply Hgetlist. eassumption.
            edestruct (@Forall2_nthN val) as [v'' [Hget''' Hcc'']]. eassumption.
            eassumption. rewrite Hget in Hget''. inv Hget''. eauto.
        + eauto.
        + eapply ctx_to_rho_cc_approx_exp; eauto.
          eapply IHe; eauto. 
          * eapply binding_in_map_antimon.
            eapply Included_trans. now eapply occurs_free_Efun_Included.
            rewrite Union_sym. now apply Included_refl.
            apply binding_in_map_def_funs. eassumption.
          * intros f Hfin; eauto.
          * eapply Disjoint_Included_r; [| eassumption ].
            rewrite bound_var_Efun. now apply Included_Union_r. }
    intros v1' c1' Hleq' Hstep'. inv Hstep'.
    edestruct Hsuf as [v2' [c2' [Hstep2' Hcc2']]]; [| eassumption |]; eauto.
    repeat eexists; eauto. econstructor; eauto.
    econstructor; eauto.
  - (* Case Eapp *)
    inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    + edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      simpl. rewrite H5, H8. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H5, H8. reflexivity.
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
      destruct (getlist ys' rho2') eqn:Hgetlist'; try discriminate. inv Hget'.
      inv Happ'. rewrite cc_approx_val_eq in H6. destruct v0; try contradiction.
      eapply ctx_to_rho_cc_approx_exp with (e := Eapp v l); eauto.
      * intros v1' c1' Hleq' Hstep'.
        inv Hstep'. rewrite H5 in H7. inv H7.
        rewrite H8 in H14; inv H14.
        admit. (* the semantics/relation needs tweaking *)
        rewrite H5 in H4. congruence.
      * constructor; eauto.
    + edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
      simpl. rewrite H4, H5. reflexivity.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto.
      simpl. rewrite H4, H5. reflexivity.
      simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
      destruct (getlist ys' rho2') eqn:Hgetlist'; try discriminate. inv Hget'.
      inv Happ'. rewrite cc_approx_val_eq in H10. destruct v0; try contradiction.
      eapply ctx_to_rho_cc_approx_exp with (e := Eapp v l); eauto.
      * intros v1' c1' Hleq' Hstep'. inv Hstep'.
        { rewrite H5 in H17. inv H17. rewrite H4 in H11; inv H11. }
        { rewrite H5 in H11. inv H11. rewrite H4 in H7; inv H7.
          destruct l1; try contradiction. destruct v0, l1; try contradiction.
          destruct v2; try contradiction.
          rewrite H15 in H6. inv H6. 
          rewrite H8 in H17. inv H17. eapply bstep_e_deterministic in H20; eauto. inv H20.
          assert (Hlen := List_util.Forall2_length _ _ _ H14).
          edestruct H10 with (vs2 := l0) (j := k - 1)
            as [t2' [Γ' [xs2 [e2 [rho2'' [Hfind [Hset Hyp]]]]]]]; eauto.
          edestruct Hyp as [v2' [c2 [Hstep2 Hcc']]]; try eassumption. omega.
          eapply List_util.Forall2_monotonic; [| eassumption ].
          intros. eapply cc_approx_val_monotonic. eassumption. omega. omega.
          repeat eexists; eauto. econstructor. eassumption. reflexivity.
          econstructor. rewrite M.gso. eassumption.
          intros Hc; subst. eapply project_vars_not_In_free_set; [ now eauto | now eauto | ].
          constructor. now eapply H3. rewrite FromList_cons. now eauto.
          reflexivity.
          eapply BStep_app_fun. rewrite M.gso. rewrite M.gss. reflexivity.
          now eauto. simpl. rewrite M.gss.
          rewrite getlist_set_neq. rewrite getlist_set_neq.
          rewrite Hgetlist'. reflexivity. 
          intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption. 
          constructor. eapply H3. rewrite FromList_cons. now eauto.
          intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption.
          constructor. now eauto. rewrite FromList_cons. now eauto.
          eassumption. simpl in Hset. eauto. eassumption.
          eapply cc_approx_val_monotonic. eassumption. omega. }
        * econstructor; eauto. 
  - inv Hcc.
    intros v1 c1 Hleq Hstep. inv Hstep.
    edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
    edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
    edestruct Hvar as [v' [Hget' Happ']]; eauto.
    eapply ctx_to_rho_cc_approx_exp; eauto.
    intros v1' c1' Hleq' Hstep'. eapply bstep_e_deterministic in H14; eauto.
    inv H14.
    edestruct Prim_axiom as [vs' [Hf' Hcc]]; eauto.
    edestruct IHe as [v2'' [c2 [Hstep2 Happrox2]]];
        [| now eauto | | | eassumption | | | | eassumption | eassumption | eassumption | ]. 
    + eapply cc_approx_env_P_extend; [| eassumption ].
      rewrite Setminus_Union_distr,
      Setminus_Empty_set, Union_Empty_set_r. 
      eapply cc_approx_env_P_antimon; [ eassumption |].
      eapply Setminus_Included. now apply Included_refl.
    + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
      eapply occurs_free_Eprim_Included. 
    + intros f Hfin. eauto.
    + eapply Disjoint_Included_r; [| eassumption ].
      rewrite bound_var_Eprim. now apply Included_Union_l.
    + eapply Fun_inv_set_In_Scope_l. now eauto.
      eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
      intros Heq; subst. now eauto.
      eapply Fun_inv_mon; [ | now eauto ].
      eapply Disjoint_Singleton. intros Hc. eapply Hd; constructor; eauto.
    + eapply FV_inv_set_In_Scope_l. now constructor.
      eapply FV_inv_set_r. intros Hc. eapply Hnin.
      subst. now eauto. now eapply FV_inv_extend_Scope.
    + repeat eexists; [| eassumption ].
      econstructor; eauto.
Admitted.

(** * Correspondance of the relational and the computational definitions of closure conversion *)

Require Import hoare ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad alpha_conv List_util.

Open Scope alpha_scope.

Section CC_correct.
  Context (utag : tag) (* Tag for types with unique constructor *)
          (env_tag : tag) (* Tag for the type of environments *)
          (tag_bij : tag -> tag) (* mapping from function tags to closure 
                                    records tags *)
          (unknown_type : type).


  Open Scope ctx_scope.

  (** All the variables greater or equal to x are in S (i.e. the "fresh" set) *)
  Definition fresh (S : Ensemble var) (x : var) :=
    forall y, (x <= y)%positive -> In _ S y.

  (** Free variable map invariant *)
  Definition FVmap_inv (FVmap : VarInfoMap) Scope Funs FVs : Prop :=
    Same_set _ Scope (fun x => exists t, M.get x FVmap = Some (BoundVar t)) /\
    Same_set _ (Setminus _ Funs Scope)
             (fun x => exists x' t t', M.get x FVmap = Some (MRFun x' t t')) /\
    forall N x, (nthN FVs N = Some x /\ ~ In _ Scope x /\ ~ In _ Funs x) <->
           (exists t, M.get x FVmap = Some (FVar N t)).

  (** Function names substitution *)
  Definition subst (FVmap : VarInfoMap) x : var :=
    match M.get x FVmap with
      | Some (MRFun x' _ _) => x'
      | _ => x
    end.

  Opaque bind ret.

  (** A function that corresponds to an evaluation context *)
  Definition is_exp_ctx (f : exp -> exp) C : Prop := 
    forall e, f e = app_ctx_f C e. 

  (** Set of variables not in the map *)
  Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) := 
    forall x : M.elt, In M.elt S x -> M.get x map = None.

  (** Spec for [get_name] *)
  Lemma get_name_fresh S :
    {{ fun s => fresh S (fst s) }}
      get_name
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (fst s') }}.  
  Proof.   
    eapply pre_post_mp_l.
    eapply bind_triple. eapply get_triple.
    intros [x d] [x' d'].
    eapply pre_post_mp_l. eapply bind_triple.
    eapply put_triple. intros u [x'' d'']. eapply return_triple.
    intros [x''' d'''] Heq1 [Heq2 Heq3] H. inv Heq1. inv Heq2. inv Heq3. 
    split; eauto. intros y Hleq.
    constructor.
    - eapply H. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. eapply Pos.le_nlt in Hleq.
      eapply Hleq. zify. omega.
  Qed.
  
  Lemma fresh_monotonic S S' x :
    Included _ S S' ->
    fresh S x ->
    fresh S' x.
  Proof.
    intros Hinc Hf x' Hleq. eapply Hinc. eapply Hf. eassumption.
  Qed.

  (** Spec for [get_var] *)
  Lemma get_var_project_var_sound Scope Funs Γ FVs FVmap S x :
    binding_in_map (Singleton _ x) FVmap ->
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (fst s) }}
      get_var utag x FVmap Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (fst s') /\
           let '(x', _, f) := t in
           (forall σ, f_eq σ (subst FVmap) ->
                 project_var Scope Funs σ Γ FVs S x x' C S') /\
           (subst FVmap) x' = x' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hin Hnin Minv. destruct Minv as [Minv1 [Minv2 Minv3]]. 
    unfold get_var. edestruct (Hin x) as [inf Hget]; eauto. 
    destruct inf; rewrite Hget. 
    - eapply bind_triple.
      + eapply get_name_fresh.     
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        eexists (Eproj_c x' t n Γ Hole_c). repeat eexists. 
        * eassumption.
        * edestruct Minv3 as [H1 [H2 [H3 H4]]]. now repeat eexists; eauto.
          econstructor 3; eauto.
          eapply Hf. zify; omega.
        * unfold subst. rewrite Hnin; eauto.
          left. eapply Hf. zify; omega.
    - eapply bind_triple.
      + eapply get_name_fresh.  
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        edestruct Minv2 as [H1 H2]; eauto. 
        exists (Econstr_c x' t0 utag [v; Γ] Hole_c). repeat eexists.
        * eassumption.
        * intros σ Hfeq.
          replace v with (σ x) by (rewrite Hfeq; unfold subst; rewrite Hget; reflexivity).
          econstructor; eauto.
          intros Hc. eapply Minv1 in Hc. destruct Hc as [t' Heq]. congruence.
          eapply H2. repeat eexists; eauto.
          eapply Hf. zify; omega.
        * unfold subst. rewrite Hnin; eauto.
          left. eapply Hf. zify; omega.
    - eapply return_triple. intros [s d] Hin'.      
      exists Hole_c. repeat eexists. 
      + eassumption. 
      + constructor. eapply Minv1. eexists; eauto.
      + unfold subst. rewrite Hget; eauto.
  Qed.

  Lemma FVmap_inv_set_bound FVmap Scope Funs FVs x t :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x (BoundVar t) FVmap) (Union _ (Singleton _ x) Scope) Funs FVs.
  Proof. 
    intros [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + eexists. now rewrite M.gsspec, Coqlib.peq_true.
      + inv Hin. inv H; congruence.
        eapply H1 in H. edestruct H as [t' Heq].
        eexists.  rewrite M.gsspec, Coqlib.peq_false; eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + eauto.
      + edestruct Hin as [t' Heq]. rewrite M.gsspec, Coqlib.peq_false in Heq; [| now eauto ].
        right. eapply H1. eexists; eauto.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + exfalso. eauto.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x' [t' [t'' Heq]]].
        * constructor; eauto.
        * eexists.  rewrite M.gsspec, Coqlib.peq_false; eauto.
    - eapply H2. destruct H as [x' [t' [t'' Heq]]].
      destruct (Coqlib.peq x x0); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + repeat eexists. rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
    - intros Hc. destruct H as [x' [t' [t'' Heq]]].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + inv Hc. inv H; congruence.
        eapply H2; eauto. repeat eexists.
        rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
    - intros [Hnth [Hnin Hnin']].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto. 
      + edestruct H3 as [[t' Heq] _].
        now repeat split; eauto.
        eexists. rewrite M.gsspec, Coqlib.peq_false; eauto.
    - edestruct H as [t' Heq]. 
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + eapply H3; eauto.
        rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
    - edestruct H as [t' Heq]. 
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + intros Hc. inv Hc. inv H0; congruence.
        rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
        edestruct H3 as [_ [_ [Hc _]]].
        eapply H3 in H0; eauto. contradiction.
    - edestruct H as [t' Heq]. 
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + intros Hc.
        rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
        edestruct H3 as [_ [_ [_ Hc']]].
        eapply H3 in Hc; eauto. contradiction.
  Qed.

  Lemma FVmap_inv_set_funs FVmap Scope Funs FVs x x' t t' :
    ~ In _ Scope x ->
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x (MRFun x' t t') FVmap) Scope (Union _ (Singleton _ x) Funs) FVs.
  Proof. 
    intros Hnin [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + contradiction.
      + eapply H1 in Hin. edestruct Hin as [t'' Heq].
        eexists.  rewrite M.gsspec, Coqlib.peq_false; eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + edestruct Hin as [t'' Heq]. rewrite M.gss in Heq; congruence.
      + edestruct Hin as [t'' Heq]. rewrite M.gso in Heq; [| now eauto ].
        eapply H1. eexists; eauto.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + repeat eexists. rewrite M.gss. reflexivity.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x'' [t'' [t''' Heq]]].
        inv H. inv H4; congruence. constructor; eassumption.
        repeat eexists. rewrite M.gso; eassumption.
    - destruct (Coqlib.peq x0 x); subst; eauto. right.
      eapply H2. edestruct H as [x'' [t1 [t2 Hget]]].
      rewrite M.gso in Hget; [| now eauto ].
      repeat eexists; eauto. 
    - destruct H as [x'' [t1 [t2 Hget]]].
      destruct (Coqlib.peq x0 x); subst; eauto.
      rewrite M.gso in Hget; [| now eauto ].
      intros Hc. apply H1 in Hc. edestruct Hc as [t3 Hget']. congruence.
    - intros [Hnth [Hnin1 Hnin2]].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [[t1 Heq] _].
        now repeat split; eauto.
        eexists. rewrite M.gsspec, Coqlib.peq_false; eauto.
    - edestruct H as [t1 Heq].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gsspec, Coqlib.peq_true in Heq. congruence.
      + eapply H3; eauto.
        rewrite M.gsspec, Coqlib.peq_false in Heq; eauto.
    - edestruct H as [t1 Heq].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + intros Hc.
        rewrite M.gso in Heq; eauto. eapply H1 in Hc. 
        edestruct Hc as [t2 Heq']. congruence.
    - edestruct H as [t1 Heq].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + intros Hc.
        rewrite M.gso in Heq; eauto.
        inv Hc. inv H0; congruence.
        edestruct H2 as [H2' _].  edestruct (H2' x0) as [y [t2 [t3 Hge']]].
        constructor. eauto. intros Hc. eapply H1 in Hc. 
        edestruct Hc as [t2 Heq']. congruence.
        congruence.
  Qed.

  (** Spec for [get_vars] *)
  Lemma get_vars_project_vars_sound Scope Funs Γ FVs FVmap S xs :
    binding_in_map (FromList xs) FVmap ->
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (fst s) }}
      get_vars utag xs FVmap Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (fst s') /\
           let '(xs', f) := t in
           (forall σ,
              f_eq σ (subst FVmap) ->
              project_vars Scope Funs σ Γ FVs S xs xs' C S') /\
           Forall2 (fun x x' => (subst FVmap) x = x') xs' xs' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hb1 Hb2 Hfv. eapply pre_post_mp_l.
    revert S Hb1 Hb2 Hfv. induction xs; intros S Hb1 Hb2 Hfv. 
    - eapply return_triple. intros [x' d'] _ Hf.
      eexists Hole_c. repeat eexists; eauto.
      constructor.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; eauto.
        intros x Hin. eapply Hb1. 
        inv Hin. constructor. eauto.
      + intros [[x tau] f] [x' d']. eapply pre_eq_state.
        intros [x'' d''] [C [S' [Hf [Hproj [Hsub Hctx]]]]].
        eapply pre_post_mp_l. eapply bind_triple.
        eapply (IHxs S'); eauto.
        intros y Hin. eapply Hb1. 
        constructor 2. eassumption.
        intros z Hin. eapply Hb2. inversion Hin; eauto.
        left. eapply project_var_free_set_Included. eapply Hproj.
        reflexivity. eassumption.
        intros [xs' f'] [x''' d''']. eapply return_triple. 
        intros [x'''' d''''] Hyp Heq'. inversion Heq'.
        destruct Hyp as [C' [S'' [Hf' [Hproj' [Hsub'  Hctx']]]]]; eauto.
        now rewrite <- H0; eauto.
        exists (comp_ctx_f C C'), S''.
        split; [ eassumption |].
        split. intros σ Heq. econstructor. eapply Hproj. eassumption.
        eapply Hproj'. eassumption.
        split. 
        * constructor; eauto.
        * intros e. rewrite <- app_ctx_f_fuse. congruence.
  Qed.

  (** Spec for [get_vars_with_types] *)
  Lemma get_vars_with_types_project_vars_sound Scope Funs Γ FVs FVmap S xs :
    binding_in_map (FromList xs) FVmap ->
    binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (fst s) }}
      get_vars_with_types utag xs FVmap Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (fst s') /\
           let '(xs', _, f) := t in
           (forall σ,
              f_eq σ (subst FVmap) ->
              project_vars Scope Funs σ Γ FVs S xs xs' C S') /\
           Forall2 (fun x x' => (subst FVmap) x = x') xs' xs' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hb1 Hb2 Hfv. eapply pre_post_mp_l.
    revert S Hb1 Hb2 Hfv. induction xs; intros S Hb1 Hb2 Hfv. 
    - eapply return_triple. intros [x' d'] _ Hf.
      eexists Hole_c. repeat eexists; eauto. constructor.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; eauto.
        intros x Hin. eapply Hb1. 
        inv Hin. constructor. eauto.
      + intros [[x tau] f] [x' d']. eapply pre_eq_state.
        intros [x'' d''] [C [S' [Hf [Hproj [Hsub Hctx]]]]].
        eapply pre_post_mp_l. eapply bind_triple.
        eapply (IHxs S'); eauto.
        intros y Hin. eapply Hb1. 
        constructor 2. eassumption.
        intros z Hin. eapply Hb2. inversion Hin; eauto.
        left. eapply project_var_free_set_Included. eapply Hproj.
        reflexivity. eassumption.
        intros [[xs' ts'] f'] [x''' d''']. eapply return_triple. 
        intros [x'''' d''''] Hyp Heq. inversion Heq.
        destruct Hyp as [C' [S'' [Hf' [Hproj' [Hsub' Hctx']]]]]; eauto.
        now rewrite <- H0; eauto.
        exists (comp_ctx_f C C'), S''.
        split; [ eassumption |].
        split. intros σ Hfeq. econstructor. eapply Hproj. eassumption.
        eapply Hproj'. eassumption.
        split. 
        * constructor; eauto.
        * intros e. rewrite <- app_ctx_f_fuse. congruence.
  Qed.

  Lemma subst_BoundVar_f_eq FVmap x t :
    f_eq ((subst FVmap) {x ~> x}) (subst (M.set x (BoundVar t) FVmap)).
  Proof.  
    intros x'. unfold subst, extend. rewrite M.gsspec.
    destruct (Coqlib.peq x' x). now eauto.
    reflexivity. 
  Qed.

  Definition new_function_names FVmap : Ensemble var :=
    fun x => exists y t1 t2, M.get y FVmap = Some (MRFun x t1 t2).

  Lemma not_In_new_function_names_injective FVmap f:
    ~ In _ (new_function_names FVmap) f ->
    injective (subst FVmap) ->
    injective ((subst FVmap) {f ~> f}).
  Proof.
    intros Hc Hinj x x' Heq. unfold extend in *.
    destruct (Coqlib.peq x x'); eauto.
    destruct (Coqlib.peq x f); eauto.
    - destruct (Coqlib.peq x' f); try congruence.
      exfalso. eapply Hc. 
      eexists x'. unfold subst in Heq.
      destruct (M.get x' FVmap) eqn:Heq'; eauto; try congruence.
      subst. destruct v; try congruence.
      eauto.
    - destruct (Coqlib.peq x' f); [| now eauto ].
      exfalso. eapply Hc. 
      eexists x. unfold subst in Heq.
      destruct (M.get x FVmap) eqn:Heq'; eauto; try congruence.
      subst. destruct v; try congruence.
      eauto.
  Qed.

  Lemma Disjoint_free_set FVmap Scope Funs FVs S :
    binding_not_in_map S FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    Disjoint _ S (Union var Scope
                        (Union var Funs (FromList FVs))).
  Proof.             
    intros Hb [Hinv1 [Hinv2 Hinv3]].
    constructor. intros x Hc. inv Hc. 
    assert (Hdec1 : Decidable Scope).
    { eapply Decidable_Same_set.
      apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [t' Hc]; congruence. 
      - right. intros [t' Hc]. congruence. }
    assert (Hdec2 : Decidable (Setminus _ Funs Scope)).
    { eapply Decidable_Same_set.
      apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [y [t' [t'' Hc]]]; congruence. 
      - right. intros [y [t' [t'' Hc]]]; congruence. }
    destruct Hdec1, Hdec2.
    destruct (Dec x). 
    - eapply Hinv1 in H1. destruct H1 as [t Heq].
      rewrite Hb in Heq; eauto. congruence.
    - destruct (Dec0 x).
      + eapply Hinv2 in H2. destruct H2 as [y [t [t' Heq]]].
        rewrite Hb in Heq; eauto. congruence.
      + inv H0; try contradiction.
        inv H3. eapply H2; constructor; eauto.
        unfold In, FromList in H0.        
        edestruct In_nthN as [N Hnth]; [ eassumption |].
        edestruct Hinv3 as [[t H'] _].
        repeat split; eauto. intros Hin. eapply H2; constructor; eauto.
        rewrite Hb in H'; eauto. congruence.
  Qed.
  
  Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
    Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
  Proof. 
    intros Hin Hb x Hin'. eauto.
  Qed.

  Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
    binding_not_in_map S map ->
    ~ In _ S x ->
    binding_not_in_map S (M.set x v map). 
  Proof. 
    intros HB Hnin x' Hin.
    rewrite M.gsspec. destruct (Coqlib.peq x' x); subst; try contradiction. 
    eauto. 
  Qed.

  Lemma new_function_names_set_BoundVar FVmap x t :
    Included _ (new_function_names (M.set x (BoundVar t) FVmap)) (new_function_names FVmap).
  Proof.
    unfold new_function_names. intros x' [y [t' [t'' Hin]]].
    rewrite M.gsspec in Hin. destruct (Coqlib.peq y x); try congruence.  
    eauto.
  Qed.

  Import MonadNotation.

  Transparent bind ret.

  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase {S} m1 (m2 : state S (var * type * (exp -> exp))) y :
    st_eq
      (ys <- m1 ;; 
       ys' <- ret (y :: ys) ;;
       t1 <- m2 ;;
       let '(x, _ , f) := t1 in
       ret (Ecase x ys', f))
      (fe <- (ys <- m1 ;;
             t1 <- m2 ;;
             let '(x, _, f1) := t1 in    
             ret (Ecase x ys, f1)) ;;
       match fe with
         | (Ecase x ys, f) =>
           ret (Ecase x (y :: ys), f)
         | _ => ret fe
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s).
    destruct (runState m2 s0). destruct p as [[x tau] f].
    reflexivity.
  Qed.

  Opaque bind ret.

  Lemma get_typeinfo_preserves_prop tau P :
    {{ fun s => P (fst s) }} get_typeinfo tau {{ fun _ _ s => P (fst s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x t] [x' t'].
    destruct (TDict.get tau t); eapply return_triple;
    intros [x'' t''] H HP; inv H; inv H0; inv H1; eauto.
  Qed.

  Lemma set_typeinfo_preserves_prop t P :
    {{ fun s => P (fst s) }} set_typeinfo t {{ fun _ _ s => P (fst s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x d] [x' d'].
    destruct (TDict.hash t d).
    eapply pre_post_mp_l. eapply bind_triple. eapply put_triple.
    intros u [x'' d'']. eapply return_triple.
    intros [x''' t'''] H1 [H2 H3] HP; inv H1; inv H2; inv H3; eauto.
  Qed.
  
  Instance FVmap_inv_Scope_Proper :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq2.
      intros H. rewrite <- Heq2. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq2.
      intros H. rewrite Heq2. eapply H3. eassumption. 
  Qed.

  Instance FVmap_inv_Funs_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq3; eauto.
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq3.
      intros H. rewrite <- Heq3. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq3; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq3.
      intros H. rewrite Heq3. eapply H3. eassumption. 
  Qed.

  Lemma FVmapInv_add_params FVmap xs ts Scope Funs FVs :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (add_params xs ts FVmap) (Union _ Scope (FromList xs)) Funs FVs. 
  Proof. 
    revert FVmap ts Scope. induction xs; intros FVmap ts Scope Hinv.
    - rewrite FromList_nil, Union_Empty_set_l. eauto.
    - rewrite FromList_cons.
      rewrite Union_assoc; rewrite Union_sym with (s2 := Singleton M.elt a), <- Union_assoc. 
      destruct ts; eapply FVmap_inv_set_bound; eauto.
  Qed.

  Lemma binding_in_map_add_params S FVmap xs ts :
    binding_in_map S FVmap ->
    binding_in_map (Union _ S  (FromList xs)) (add_params xs ts FVmap).
  Proof.
    revert S FVmap ts. induction xs; intros S FVmap ts Hb.
    - intros x. rewrite FromList_nil, Union_Empty_set_l. eauto.
    - intros x. rewrite FromList_cons.
      rewrite Union_sym with (s2 := FromList xs), Union_assoc.
      simpl. destruct ts; eapply binding_in_map_set; eauto. 
  Qed.

  Lemma binding_not_in_map_add_params S FVmap xs ts :
    binding_not_in_map S FVmap ->
    Disjoint _ S (FromList xs) ->
    binding_not_in_map S (add_params xs ts FVmap).
  Proof.
    revert S FVmap ts. induction xs; intros S FVmap ts Hb Hd.
    - eauto.
    - rewrite FromList_cons in Hd.
      destruct ts; simpl; eapply binding_not_in_map_set_not_In_S; eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
  Qed.

  Lemma new_function_names_add_params FVmap xs ts :
    Included  _ (new_function_names (add_params xs ts FVmap)) (new_function_names FVmap).
  Proof.
    revert FVmap ts. induction xs; intros FVmap ts; simpl. 
    - apply Included_refl.
    - destruct ts;
      (eapply Included_trans;
       [ eapply new_function_names_set_BoundVar | eapply IHxs ]).
  Qed.

  Lemma injective_add_params FVmap xs ts :
    Disjoint _ (new_function_names FVmap) (FromList xs) ->
    injective (subst FVmap) ->
    injective (subst (add_params xs ts FVmap)).
  Proof. 
    revert FVmap ts. induction xs; intros FVmap ts Hd Hinj.
    - eassumption. 
    - simpl. destruct ts; rewrite <- subst_BoundVar_f_eq;
      eapply not_In_new_function_names_injective.
      + intros Hc. eapply Hd. constructor.
        eapply new_function_names_add_params. eassumption. 
        rewrite FromList_cons. eauto.
      + eapply IHxs. constructor. intros x Hin. 
        inv Hin. eapply Hd. constructor; eauto.
        rewrite FromList_cons. eauto.
        eassumption.
      + intros Hc. eapply Hd. constructor.
        eapply new_function_names_add_params. eassumption. 
        rewrite FromList_cons. eauto.
      + eapply IHxs. constructor. intros x Hin. 
        inv Hin. eapply Hd. constructor; eauto.
        rewrite FromList_cons. eauto.
        eassumption.
  Qed.

  Lemma construct_lst_injection_add_params FVmap xs ts :
    Disjoint _ (new_function_names FVmap) (FromList xs) ->
    injective (subst FVmap) ->
    exists f,
      f_eq f (subst (add_params xs ts FVmap)) /\
      construct_lst_injection (subst FVmap) xs xs f.
  Proof.
    revert FVmap ts. induction xs; intros FVmap ts Hd Hinj.  
    - eexists. split. simpl. reflexivity. constructor.
    - assert (Hinj' : injective (subst (add_params (a :: xs) ts FVmap))).
      { apply injective_add_params; eauto. }
      rewrite FromList_cons in Hd.
      destruct ts; edestruct IHxs as [f [Heq Hinj'']]. 
      + eapply Disjoint_Included_r; [ | eassumption ].
        now apply Included_Union_r. 
      + eassumption.
      + eexists (f {a ~> a}). split. 
        simpl. rewrite Heq. eapply subst_BoundVar_f_eq.
        constructor. eassumption. 
        rewrite Heq. simpl in Hinj'. rewrite subst_BoundVar_f_eq.
        eassumption.
      + eapply Disjoint_Included_r; [ | eassumption ].
        now apply Included_Union_r. 
      + eassumption.
      + eexists (f {a ~> a}). split. 
        simpl. rewrite Heq. eapply subst_BoundVar_f_eq.
        constructor. eassumption. 
        rewrite Heq. simpl in Hinj'. rewrite subst_BoundVar_f_eq.
        eassumption.
  Qed.
          
  Lemma FVmap_inv_empty :
    FVmap_inv (Maps.PTree.empty VarInfo) (Empty_set M.elt) (Empty_set M.elt) [].
  Proof.
    repeat split; (try now intros Hc; inv Hc); (try now intros x Hc; inv Hc). 
    intros x Hx. destruct Hx as [t Hget]. rewrite M.gempty in Hget. now inv Hget.
    destruct H as [x' [t [t' Hget]]]. rewrite M.gempty in Hget. now inv Hget.
    destruct H as [t Hget]. rewrite M.gempty in Hget. now inv Hget.
  Qed.
  
  Lemma nthN_app {A} (l1 l2 : list A) N :
    (nthN (l1 ++ l2) N = nthN l1 N) \/
    (nthN (l1 ++ l2) N = nthN l2 (N - N.of_nat (length l1))%N /\ (N.of_nat (length l1) <= N)%N).
  Proof. 
    revert N; induction l1; intros N.
    - right. rewrite app_nil_l, N.sub_0_r. split; eauto. simpl. zify; omega.
    - destruct N; [now eauto |].
      destruct (IHl1 ((N.pos p)-1)%N) as [H1 | [H2 H3]].
      now eauto.
      replace (N.of_nat (length (a :: l1))) with (1 + N.of_nat (length l1))%N.
      replace (N.pos p - (1 + N.of_nat (length l1)))%N with
      (N.pos p - 1 - N.of_nat (length l1))%N.
      right. split. now eauto. zify. omega. 
      zify; omega. 
      simpl (length _). rewrite Nnat.Nat2N.inj_succ.
      zify. omega. 
  Qed.
  
  Lemma nthN_is_Some_length {A} (l : list A) N x :
    nthN l N = Some x ->
    (N < N.of_nat (length l))%N.
  Proof. 
    revert N. induction l; intros N Heq.
    - inv Heq. 
    - destruct N. inv Heq.
      unfold length. rewrite Nnat.Nat2N.inj_succ. zify. omega. 
      assert (Hlt : ((N.pos p)-1 < N.of_nat (length l))%N) by eauto.
      simpl (length _). rewrite Nnat.Nat2N.inj_succ.
      zify. omega. 
  Qed.
  
  Lemma nthN_app_geq {A} (l1 l2 : list A) N :
    (N.of_nat (length l1) <= N)%N ->
    nthN (l1 ++ l2) N = nthN l2 (N - N.of_nat (length l1))%N.
  Proof.
    revert N. induction l1; intros N Heq.
    - simpl. rewrite N.sub_0_r. reflexivity.
    - simpl length in *. 
      destruct N. 
      zify. omega.
      rewrite Nnat.Nat2N.inj_succ.
      rewrite <- N.add_1_l, N_as_DT.sub_add_distr. 
      rewrite <- IHl1.
      reflexivity. zify. omega. 
  Qed.
  
  Lemma nthN_is_Some_app {A} (l1 l2 : list A) N x :
    nthN l1 N = Some x ->
    nthN (l1 ++ l2) N = Some x.
  Proof.
    revert N. induction l1; intros N Heq.
    - inv Heq.
    - destruct N. inv Heq. reflexivity.
      simpl. eauto.
  Qed.
  
  Lemma FVmap_inv_set_free_var FVmap Scope Funs FVs x n t:
    FVmap_inv FVmap Scope Funs FVs ->
    N.of_nat (length FVs) = n ->
    ~ In _ Scope x -> ~ In  _ Funs x -> ~ List.In x FVs ->
    FVmap_inv (Maps.PTree.set x (FVar n t) FVmap) Scope Funs (FVs ++ [x]). 
  Proof.  
    intros [H1 [H2 H3]] Hlen Hnin1 Hnin2.
    split; [| split ]. 
    - split.
      + intros x' Hin. assert (Hin' := Hin).
        eapply H1 in Hin. edestruct Hin as [t' Heq].
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [t' Hget]. eapply H1. 
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence.
        now eauto.
    - split.
      + intros x' Hin. assert (Hin' := Hin). inv Hin'. 
        eapply H2 in Hin. edestruct Hin as [y [t1 [t2 Heq]]].
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [y [t1 [t2 Hget]]]. eapply H2. 
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence.
        now eauto.
    - intros N x'. split.
      + intros [Hnth [Hnin1' Hnin2']].
        destruct (nthN_app FVs [x] N) as [Hn | [Hn Hlen']].
        * destruct (Coqlib.peq x' x); subst.
          exfalso. eapply H. eapply nthN_In. rewrite <- Hnth. now eauto.
          edestruct H3 as [[t' Hget] _].
          repeat split; eauto. rewrite <- Hnth. now eauto.
          eexists. now rewrite M.gso; eauto.
        * subst. rewrite Hnth in Hn. eapply nthN_is_Some_length in Hnth.
          rewrite app_length in Hnth. simpl length in *.
          destruct (N - N.of_nat (length FVs))%N eqn:Heq; simpl in Hn; try congruence.
          inv Hn. eexists. rewrite M.gss; eauto.
          repeat f_equal. zify. omega. 
      + subst. intros [t' Hget].
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        * subst. inv Hget. repeat split; eauto.
          rewrite nthN_app_geq. rewrite N.sub_diag. reflexivity. 
          zify; omega. 
        * edestruct H3 as [_ [H1' [H2' H3']]].
          now eexists; eauto.
          repeat split; eauto. apply nthN_is_Some_app. eassumption.
  Qed.

  Lemma make_env_spec fv FVmap_o Γ_n Γ_o Scope Funs FVs S :
    binding_in_map (FromList (PS.elements fv)) FVmap_o ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ_o)) FVmap_o ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    {{ fun s => fresh S (fst s) }}
      make_env utag env_tag fv (Maps.PTree.empty VarInfo) FVmap_o Γ_n Γ_o 
    {{ fun s t  s' =>
         let '(_, FVmap_n, f) := t in
         exists C S' FVs' tau t,
           fresh S' (fst s') /\
           (forall σ, f_eq σ (subst FVmap_o) ->
                 project_vars Scope Funs σ Γ_o FVs S (PS.elements fv) FVs' C S') /\
           Forall2 (fun (x : M.elt) (x' : var) => subst FVmap_o x = x')
                   FVs' FVs' /\
           is_exp_ctx f (comp_ctx_f C (Econstr_c Γ_n tau t FVs' Hole_c)) /\
           FVmap_inv FVmap_n (Empty_set _) (Empty_set _) (PS.elements fv)
     }}.
  Proof.
    intros Hb1 Hb2 Minv. eapply bind_triple. 
    - eapply get_vars_with_types_project_vars_sound; eauto.
    - intros [[xs ts] f] s1.
      eapply pre_existential. intros C1. eapply pre_existential. intros S'.
      eapply pre_uncurry_r. intros [Hvars [Hall Hctx]].
      eapply bind_triple. now eapply set_typeinfo_preserves_prop.
      intros tau s2. eapply return_triple.
      intros s3 Hf. do 6 eexists. eassumption. 
      repeat (split; [ eassumption |]). split.
      + intros e. rewrite Hctx. rewrite <- app_ctx_f_fuse.
        f_equal. reflexivity.
      + clear.
        assert (He : FVmap_inv (Maps.PTree.empty VarInfo)
                               (Empty_set M.elt) (Empty_set M.elt) (@nil PS.elt))
          by apply FVmap_inv_empty.
        assert (Hlen : N.of_nat (@length PS.elt []) = 0%N) by eauto.
        assert (Hnin : forall x, List.In x (PS.elements fv) -> ~ List.In x (@nil PS.elt))
          by (intros x H1 H2; inv H2).
        assert (Hdup :  NoDupA eq (PS.elements fv)) by apply PS.elements_spec2w.
        replace (PS.elements fv) with ([] ++ PS.elements fv) at 2 by reflexivity.
        revert Hlen He Hnin Hdup. generalize (Maps.PTree.empty VarInfo) as FVmap_i.
        generalize (@nil PS.elt). generalize 0%N. 
        induction (PS.elements fv); intros n vars FVmap_i Hlen Hinv Hnin Hdup.
        * rewrite app_nil_r. simpl. assumption.
        * simpl. replace (vars ++ a :: l) with ((vars ++ [a]) ++ l).
          eapply IHl. rewrite app_length. simpl. zify. omega. 
          eapply FVmap_inv_set_free_var. now eauto. eassumption. 
          now intros Hc; inv Hc. now intros Hc; inv Hc. 
          eapply Hnin. constructor. reflexivity.
          intros x Hin Hc. eapply Hnin.  
          now constructor 2; eauto. inv Hdup.
          apply Coqlib.in_app in Hc. inv Hc; eauto. inv H. 
          exfalso. eapply H1. eapply In_InA. eauto. now eapply Pos.eq_equiv. 
          eassumption. now inv H0. now inv Hdup.
          rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma subst_MRFun_f_eq (FVmap : VarInfoMap) (x x' : var) (t t': type) :
    f_eq ((subst FVmap) {x ~> x'}) (subst (M.set x (MRFun x' t t') FVmap)).
  Proof.
    unfold subst. intros y. unfold extend.
    rewrite M.gsspec. destruct (Coqlib.peq y x); eauto.
  Qed.

  Instance image_Proper {A B} : Proper (f_eq ==> Logic.eq ==> Same_set _) (@image A B).
  Proof.
    intros x1 x2 Heq s1 s2 Heq'; subst.
    split; intros x [y1 [Hin Heq']]; subst;
    eexists; eauto.
  Qed.

  Lemma make_full_closure_spec B FVmap_n FVmap_o Γ Scope Funs FVs FVs' typ S :
    FVmap_inv FVmap_o Scope Funs FVs ->
    FVmap_inv FVmap_n (Empty_set _) (Empty_set _) FVs' ->
    {{ fun s => fresh S (fst s) }}
      make_full_closure utag tag_bij unknown_type B FVmap_n FVmap_o Γ typ
    {{ fun s t s' =>
         let '(FVmap_n', FVmap_o', f) := t in
         exists C σ S',
           fresh S' (fst s') /\
           make_closures B S id Γ C S' σ /\
           f_eq σ (subst FVmap_n') /\
           is_exp_ctx f C /\
           FVmap_inv FVmap_o' (Union _ (name_in_fundefs B) Scope) Funs FVs /\
           FVmap_inv FVmap_n' (Empty_set _) (name_in_fundefs B) FVs'
     }}.
  Proof.
    revert FVmap_n FVmap_o Γ Scope Funs FVs FVs' typ S.
    induction B; intros FVmap_n FVmap_o Γ Scope Funs FVs FVs' typ S Minv_o Minv_n.
    - eapply bind_triple; [ now apply get_name_fresh |].
      intros x s1. eapply pre_uncurry_l. intros Hx.
      eapply bind_triple; [ eapply IHB; eassumption |].
      intros [[FVmap_n' FVmap_o'] f] _.
      eapply pre_existential. intros C.  eapply pre_existential. intros σ.
      eapply pre_existential. intros S'.
      eapply pre_uncurry_r. intros [Hclo [Hfeq [Hctx [Minv_o' Minv_n']]]].
      eapply bind_triple; [ now apply get_typeinfo_preserves_prop |].
      intros t_inf s2.
      eapply bind_triple with
      (post' := fun _ _ s =>  fresh S' (fst s)).
      + destruct t_inf; try now apply return_triple. 
        eapply bind_triple. now apply set_typeinfo_preserves_prop.
        intros. eapply bind_triple. now apply set_typeinfo_preserves_prop.
        intros. now apply return_triple. 
      + intros [typ' typ''] _. apply return_triple. 
        intros s3 Hf. do 3 eexists.
        split. eassumption. 
        split. econstructor. eassumption. eapply Hx. zify; omega.
        split. setoid_rewrite <- subst_MRFun_f_eq.
        eapply f_eq_extend; eauto.
        split. intros e'. simpl. rewrite Hctx. reflexivity.
        split.
        simpl. rewrite <- Union_assoc. eapply FVmap_inv_set_bound. eassumption.
        simpl. apply FVmap_inv_set_funs. now apply not_In_Empty_set.
        eassumption. 
    - eapply return_triple. intros s Hs. do 3 eexists.
      split. eassumption. split. now constructor.
      split.
      intros x. unfold subst. destruct (M.get x FVmap_n) eqn:Heq; eauto.
      destruct v; eauto. destruct Minv_n as [H1 [H2 H3]].
      exfalso. rewrite Setminus_Empty_set in H2. eapply not_In_Empty_set.
      eapply H2. now repeat eexists; eauto.
      split. intros e. reflexivity.
      split. rewrite Union_Empty_set_r. eassumption. 
      eassumption. 
  Qed.

  Lemma image_extend_not_In f x x' S :
    ~ In _ S x ->
    Same_set _ (image (f {x ~> x'} ) S) (image f S).
  Proof.    
    intros Hnin.
    split; intros y [y' [Hin Heq]]. rewrite extend_gso in Heq.
    now eexists; eauto. intros Hc. subst. contradiction.
    eexists; split; eauto. rewrite extend_gso. now eauto.
    intros Hc. subst. contradiction.
  Qed.

  Definition feq_subdomain {A B} (f1 f2 : A -> B) S :=
    forall x, In _ S x -> f1 x = f2 x.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs Γ FVs FVmap S
       (* The invariant the relates [FVmap] and [Scope], [Funs], [FV] *)
       (Minv : FVmap_inv FVmap Scope Funs FVs)
       (* [FVmap] contains all the free variables *)
       (Hbin1 : binding_in_map (occurs_free e) FVmap)
       (* [FVmap] does not contain the variables in [S] or [Γ] *)
       (Hbin2 : binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap)
       (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
       (HD1 : Disjoint _ S (Union _ (bound_var e)
                                  (Union _ (occurs_free e) (Singleton _ Γ))))
       (* The current environment argument is fresh *)
       (HD2 : ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ)
       (* (* Τhe new function names in the substitution are fresh *) *)
       (HD3 : Disjoint _ (image (subst FVmap) (Setminus _ Funs Scope))
                       (Union _ (occurs_free e) (bound_var e))),
       {{ fun s => True }}
         exp_closure_conv utag env_tag tag_bij unknown_type e FVmap Γ
       {{ fun s ef s' =>
            fresh S (fst s) ->
            exists C σ, is_exp_ctx (snd ef) C /\
                   f_eq (subst FVmap) σ /\
                   Closure_conversion Scope Funs σ Γ FVs e (fst ef) C /\
                   fresh S (fst s')
       }}) /\
    (forall B FVmap Funs FVs S
       (Minv : FVmap_inv FVmap (Empty_set _) Funs FVs)
       (Hbin1 : binding_in_map (Union _ (occurs_free_fundefs B) (name_in_fundefs B)) FVmap)
       (Hbin2 : binding_not_in_map S FVmap)
       (HD1 : Disjoint _ S (Union _ Funs (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))))
       (HD2 : Disjoint _ (image (subst FVmap) Funs) (Union _ (bound_var_fundefs B) (occurs_free_fundefs B)))
       (Hinc : Included _ (name_in_fundefs B) Funs),
       {{ fun s => True }}
         fundefs_closure_conv utag env_tag tag_bij unknown_type B FVmap
       {{ fun s B' s' =>
            fresh S (fst s) ->       
            exists σ, Closure_conversion_fundefs Funs σ FVs B B' /\
                 fresh S (fst s')
       }}).
  Proof.
(*    eapply exp_def_mutual_ind; intros.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ | eassumption | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_eq_state.
        intros [x'' d''] [C [S' [Hf [Hproj [Hsub  Hctx]]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v (BoundVar t) FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Econstr_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. eapply project_vars_free_set_Included; eauto.
          eapply Hproj. reflexivity. 
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.  
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * rewrite bound_var_Econstr, occurs_free_Econstr in HD1.
          eapply Disjoint_Included_l. eapply project_vars_free_set_Included.
          eapply Hproj. reflexivity.
          eapply Disjoint_Included_r; [| eassumption ]. rewrite <- Union_assoc.
          apply Included_Union_compat. now apply Included_refl.
          rewrite Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite Union_sym, <- Union_assoc. eapply Included_Union_mon_r.
          rewrite <- (@Union_Setminus _ _ _ _). now apply Included_Union_l.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Econstr, occurs_free_Econstr.
          destruct (Coqlib.peq Γ v); subst;  eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * rewrite <- subst_BoundVar_f_eq. rewrite image_extend_not_In.
          eapply Disjoint_Included_l. eapply image_monotonic.
          eapply Included_Setminus_compat. now eapply Included_refl.
          now apply Included_Union_r.
          eapply Disjoint_Included_r; [| eassumption].
          rewrite bound_var_Econstr, occurs_free_Econstr.
          rewrite <- !Union_assoc. apply Included_Union_mon_r.
          rewrite !Union_assoc, (Union_sym _ (Singleton var v)), !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite (@Setminus_Union_Included _ _ _ _ _).
          now apply Included_Union_r. now apply Included_refl.
          intros Hc. inv Hc. eauto.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst.
          edestruct (Hf' Hf) as [C' [σ [Hctx' [Hfeq [Hcc Hf'']]]]]; eauto.
          do 2 eexists. split. eapply Hctx. split.
          rewrite <- f_eq_extend_same, subst_BoundVar_f_eq. eassumption.
          unfold subst. rewrite Hbin2. reflexivity. eassumption.
          Focus 2.
          split. simpl. rewrite Hctx'. econstructor. 
          rewrite !Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym. 
          rewrite <- Union_assoc. eapply Disjoint_free_set. ; [| eassumption ].
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_Included_r; [| eassumption ]. do 2 apply Included_Union_mon_r.
          now apply Included_refl.
          eassumption. eassumption. 
          split. eassumption. constructor. eassumption.
          eapply not_In_new_function_names_injective.
          intros Hc. eapply HD3; eauto. eassumption.
          rewrite subst_BoundVar_f_eq. rewrite HC''. now eauto.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple with (post' := fun _ l i => l = [] /\ fresh S (fst i)).
      + eapply return_triple; eauto. 
      + intros pats' s2.
        eapply bind_triple.
        * eapply frame_rule. eapply get_var_project_var_sound; eauto.
          intros x Hx. eapply Hbin1. rewrite occurs_free_Ecase_nil. eassumption.
        * intros [[x tau] f] s. eapply return_triple.
          intros s' [Heq [C [C' [S' [Hf [Hproj [Hsub [Halpha Hctx]]]]]]]]. rewrite Heq.
          eexists. split; eauto. split. econstructor. eexists. split. econstructor.
          rewrite !Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym. 
          rewrite <- Union_assoc. eapply Disjoint_free_set; [| eassumption ].
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_Included_r; [| eassumption ]. do 2 apply Included_Union_mon_r.
          now apply Included_refl.
          eassumption. now constructor.
          split. eassumption. now constructor.
          eapply fresh_monotonic. now eapply project_var_free_set_Included; eauto.
          eassumption.
    - unfold exp_closure_conv. setoid_rewrite assoc.
      eapply bind_triple.
      + eapply H; [ eassumption | eassumption | | eassumption | | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite bound_var_Ecase_cons. now apply Included_Union_l.
          rewrite occurs_free_Ecase_cons.
          apply Included_Union_compat. now apply Included_Union_l.
          now apply Included_refl.
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite occurs_free_Ecase_cons. now apply Included_Union_l.
          rewrite bound_var_Ecase_cons. now apply Included_Union_l.
      + intros [e' f'] s'.  simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. 
        eapply pre_post_mp_l. eapply bind_triple. 
        eapply H0 with (FVmap := FVmap) (Γ := Γ);
          [ eassumption | eassumption | | eassumption | | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Ecase_cons. apply Included_Union_mon_r.
          now apply Included_Union_r.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite bound_var_Ecase_cons. now apply Included_Union_r.
          rewrite occurs_free_Ecase_cons.
          apply Included_Union_compat. apply Included_Union_mon_r.
          now apply Included_Union_r.
          now apply Included_refl.
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite occurs_free_Ecase_cons. apply Included_Union_mon_r.
          now apply Included_Union_r.
          rewrite bound_var_Ecase_cons. now apply Included_Union_r.
        * intros [e'' f s''].   
          edestruct e''; eapply return_triple; intros s''' Hcc1 Hcc2 Hf;
          edestruct (Hcc2 Hf) as [C2 [Hctx1 [[e2 [C2' [Hc2' [Ha2 Ha2']]]] Hf'']]];
          edestruct (Hcc1 Hf'') as [C1 [Hctx2 [[e1 [C1' [Hcc1' [Ha1 Ha1']]]] Hf''']]];
          inv Hcc1'; inv Ha1'.
          eexists. repeat split.
          eassumption.
          repeat eexists.
          eapply CC_Ecase with (pats' := (c, (C2' |[ e2 ]|)) :: pats'); eauto.
          econstructor; [| eassumption ]. split; eauto. repeat eexists; eauto.
          eassumption. econstructor; eauto.
          econstructor; [| eassumption ]. split; eauto.
          rewrite Hctx1. now eauto.
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; [ eassumption | | eassumption | eassumption ].
        intros x Hx. inv Hx. eapply Hbin1. eauto.
      + intros [[x tau] f] s. eapply pre_eq_state.
        intros [x'' d''] [C [C' [S' [Hf [Hproj [Hsub [Halpha Hctx]]]]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v (BoundVar t) FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * rewrite <- subst_BoundVar_f_eq. eapply not_In_new_function_names_injective.
          intros Hc. eapply HD3. now eauto. assumption.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eproj_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption. clear Hsub.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * rewrite bound_var_Eproj, occurs_free_Eproj in HD1.
          eapply Disjoint_Included_l. now eapply project_var_free_set_Included; eauto.
          eapply Disjoint_Included_r; [| eassumption ]. rewrite <- Union_assoc.
          apply Included_Union_compat. now apply Included_refl.
          rewrite Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite Union_sym, <- Union_assoc. eapply Included_Union_mon_r.
          rewrite <- (@Union_Setminus _ _ _ _). now apply Included_Union_l.
        * intros Hc. clear Hsub. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eproj, occurs_free_Eproj.
          destruct (Coqlib.peq Γ v); subst;  eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * eapply Disjoint_Included_l;[ now apply new_function_names_set_BoundVar | ].
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Eproj, occurs_free_Eproj.
          rewrite <- !Union_assoc. apply Included_Union_mon_r.
          rewrite !Union_assoc, (Union_sym _ (Singleton var v)), !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite (@Setminus_Union_Included _ _ _ _ _).
          now apply Included_Union_r. now apply Included_refl.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst s'.
          edestruct (Hf' Hf) as [C'' [HC'' [[e'' [Ce [Hcc [Ha1 Ha2]]]] Hf'']]]; eauto. 
          exists C'. split. now eauto. split. do 2 eexists. split.
          econstructor.
          rewrite !Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym. 
          rewrite <- Union_assoc. eapply Disjoint_free_set; [| eassumption ].
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_Included_r; [| eassumption ]. do 2 apply Included_Union_mon_r.
          now apply Included_refl.
          eassumption. eassumption. 
          split. eassumption. constructor. eassumption.
          eapply not_In_new_function_names_injective.
          intros Hc. eapply HD3; eauto. eassumption.
          rewrite subst_BoundVar_f_eq. rewrite HC''. now eauto.
          eapply fresh_monotonic. now eapply project_var_free_set_Included; eauto.
          eassumption.
    - admit.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_var_project_var_sound; [ eassumption | | eassumption | eassumption ].
        intros x Hx. eapply Hbin1. inv Hx. eauto.
      + intros [[x tau] f] s1. eapply pre_existential. intros C1.
        eapply pre_existential. intros C2. eapply pre_existential. intros S'. 
        eapply pre_uncurry_r. intros [Hvar [Hsubst [Haplha Hctx]]].
        eapply bind_triple.
        * eapply get_vars_project_vars_sound; [ eassumption | | | eassumption ].
          intros x' Hx'. eapply Hbin1. now eauto.
          eapply binding_not_in_map_antimon; [| eassumption ].
          eapply Included_Union_compat; [| now apply Included_refl ].
          now eapply project_var_free_set_Included; eauto.
        * intros [xs f'] _. eapply pre_existential. intros C1'.
          eapply pre_existential. intros C2'. eapply pre_existential. intros S''. 
          eapply pre_uncurry_r. intros [Hvars [Hall [Halpha' Hctx']]]. eapply bind_triple.
          eapply get_name_fresh.
          intros x' i. eapply pre_uncurry_l. intros Hf1.
          eapply bind_triple.
          now eapply get_name_fresh. 
          intros x'' s2. eapply pre_uncurry_l. intros Hf2. 
          eapply bind_triple. eapply get_typeinfo_preserves_prop.
          intros tinf s3. eapply return_triple.
          intros s4 Hf3. simpl. exists (comp_ctx_f C2 C2').
          split. intros e. rewrite <- app_ctx_f_fuse. congruence.
          split; eauto.
          repeat eexists. 
          econstructor;
            [ | econstructor; eassumption | eapply Hf1; now apply Pos.le_refl
              | eapply Hf2; now apply Pos.le_refl
              | intros Hc; subst x';  eapply Hf2;
                [ now apply Pos.le_refl | now eauto ]].
          rewrite !Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym. 
          rewrite <- Union_assoc. eapply Disjoint_free_set; [| eassumption ].
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_Included_r; [| eassumption ]. do 2 apply Included_Union_mon_r.
          now apply Included_refl.
          intros e e' He. rewrite <- !app_ctx_f_fuse. now eauto.
          assert (Hinj' : injective ((subst FVmap) {x' ~> x'})).
          { rewrite f_eq_extend_same. eassumption.
            unfold subst. rewrite Hbin2; eauto.
            left. eapply project_var_free_set_Included. eassumption.
            eapply project_vars_free_set_Included. eassumption.
            eapply Hf1. zify; omega. }
          econstructor. eassumption. eassumption.
          econstructor. eapply extend_same. eassumption.
          rewrite f_eq_extend_same. eassumption.
          eapply extend_same. unfold subst. rewrite Hbin2. reflexivity.
          left. eapply project_var_free_set_Included. eassumption.
          eapply project_vars_free_set_Included. eassumption.
          eapply Hf2. zify; omega. 
          constructor. constructor. do 2 eapply extend_same.
          unfold subst. rewrite Hbin2. reflexivity.
          left. eapply project_var_free_set_Included. eassumption.
          eapply project_vars_free_set_Included. eassumption.
          eapply Hf2. zify; omega.
          eapply Forall2_same. intros z Hin. do 2 eapply extend_same.
          eapply Forall_forall with (P := fun z => subst FVmap z = z).
          eapply Forall2_Forall with (P := fun z z' => subst FVmap z = z').
          eassumption. eassumption.
          do 2 eapply extend_same.
          unfold subst. rewrite Hbin2. reflexivity.
          left. eapply project_var_free_set_Included. eassumption.
          eapply project_vars_free_set_Included. eassumption.
          eapply Hf1. zify. omega.
          eapply fresh_monotonic; [| eassumption ]. 
          do 2 eapply Setminus_Included. eapply Included_trans.
          now eapply project_vars_free_set_Included; eauto.
          now eapply project_var_free_set_Included; eauto.
    - eapply pre_post_mp_r. eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ eassumption | | eassumption | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_eq_state.
        intros [x'' d''] [C [C' [S' [Hf [Hproj [Hsub [Halpha Hctx]]]]]]].
        eapply pre_post_mp_l.
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v (BoundVar t) FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * rewrite <- subst_BoundVar_f_eq. eapply not_In_new_function_names_injective.
          intros Hc. eapply HD3. now eauto. assumption.
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eprim_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_vars_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.  
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * rewrite bound_var_Eprim, occurs_free_Eprim in HD1.
          eapply Disjoint_Included_l. now eapply project_vars_free_set_Included; eauto.
          eapply Disjoint_Included_r; [| eassumption ]. rewrite <- Union_assoc.
          apply Included_Union_compat. now apply Included_refl.
          rewrite Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite Union_sym, <- Union_assoc. eapply Included_Union_mon_r.
          rewrite <- (@Union_Setminus _ _ _ _). now apply Included_Union_l.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eprim, occurs_free_Eprim.
          destruct (Coqlib.peq Γ v); subst;  eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * eapply Disjoint_Included_l;[ now apply new_function_names_set_BoundVar | ].
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite bound_var_Eprim, occurs_free_Eprim.
          rewrite <- !Union_assoc. apply Included_Union_mon_r.
          rewrite !Union_assoc, (Union_sym _ (Singleton var v)), !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          rewrite (@Setminus_Union_Included _ _ _ _ _).
          now apply Included_Union_r. now apply Included_refl.
        * intros e' s'. eapply return_triple. intros s'' Hf' Hcc. subst.
          edestruct (Hf' Hf) as [C'' [HC'' [[e'' [Ce [Hcc [Ha1 Ha2]]]] Hf'']]]; eauto. 
          exists C'. split. now eauto. split. do 2 eexists. split.
          econstructor. 
          rewrite !Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym. 
          rewrite <- Union_assoc. eapply Disjoint_free_set; [| eassumption ].
          eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l.
          eapply Disjoint_Included_r; [| eassumption ]. do 2 apply Included_Union_mon_r.
          now apply Included_refl.
          eassumption. eassumption. 
          split. eassumption. constructor. eassumption.
          eapply not_In_new_function_names_injective.
          intros Hc. eapply HD3; eauto. eassumption.
          rewrite subst_BoundVar_f_eq. rewrite HC''. now eauto.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - eapply pre_post_mp_r. eapply bind_triple.
      now apply get_typeinfo_preserves_prop.
      intros tau s1. eapply bind_triple. now apply get_name_fresh.
      intros x s2. apply pre_uncurry_l. intros Hf1. 
      eapply pre_post_mp_l. eapply bind_triple.
      assert (Hincl : Included var (Union var (bound_var e) (occurs_free e))
                               (Union var (bound_var_fundefs (Fcons v t l e f5))
                                      (occurs_free_fundefs (Fcons v t l e f5)))).
      { rewrite bound_var_fundefs_Fcons.
        rewrite !Union_assoc, Union_sym with (s4 := FromList l), Union_sym with (s4 := bound_var e), <- !Union_assoc.
        apply Included_Union_compat. now apply Included_refl.
        eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e f5).
        econstructor. now eauto. apply Included_Union_compat. now apply Included_refl. 
        simpl. rewrite <- Union_assoc. apply Included_Union_compat. now apply Included_refl. 
        apply Included_Union_compat; [| now apply Included_refl ].
        now eapply name_in_fundefs_bound_var_fundefs. }
      eapply H with (Scope := FromList l) (Funs := Funs) (FVs := FVs) (S := Setminus _ S (Singleton _ x)).
      + rewrite <- Union_Empty_set_r with (s := FromList l). eapply FVmapInv_add_params.
        eassumption.
      + eapply injective_add_params; [| eassumption].
        eapply Disjoint_Included_r; [| eassumption ]. left. eauto.
      + eapply binding_in_map_antimon; [| eapply binding_in_map_add_params; eassumption ].
        rewrite Union_sym. rewrite Union_sym with (s3 := occurs_free_fundefs _ ).
        eapply occurs_free_in_fun. constructor. eauto.
      + intros x'. rewrite <- (@Union_Setminus _ _ _ _), Union_Included_Same_set. 
        eapply binding_not_in_map_add_params. eassumption.
        constructor. intros y Hc. inv Hc. eapply HD1. constructor; eauto. now right; eauto.
        intros x'' Hc; inv Hc. eapply Hf1. zify; omega.
      + rewrite Union_assoc. eapply Disjoint_sym. eapply Disjoint_Union.
        eapply Disjoint_Included_r. now apply Subset_Setminus.
        eapply Disjoint_sym. eapply Disjoint_Included_r; [| eassumption ].
        apply Included_Union_mon_r. eassumption.
        eapply Disjoint_sym. eapply Disjoint_Setminus. now apply Included_refl.
      + intros Hc. eapply HD1. inv Hc.
        constructor; [ | now eauto ]; eapply Hf1; zify; omega.
        constructor. eapply Hf1; zify; omega. right.
        eapply occurs_free_in_fun with (B := Fcons v t l e f5) in H1; [| econstructor; now eauto ].
        inv H1; eauto. inv H2; eauto. left. now eapply name_in_fundefs_bound_var_fundefs. 
      + eapply Disjoint_Included_l. apply new_function_names_add_params.
        eapply Disjoint_Included_r; [| eassumption ]. rewrite Union_sym. eassumption. 
      + intros [e' f] s3. eapply pre_post_mp_l. eapply bind_triple.
        eapply H0 with (S := Setminus _ S (Singleton _ x)); [ eassumption | eassumption | | | | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          simpl. rewrite Union_assoc. apply Included_Union_compat.
          now apply occurs_free_fundefs_Fcons_Included. now apply Included_refl.
        * eapply binding_not_in_map_antimon. now apply Subset_Setminus.
          eassumption.
        * eapply Disjoint_Included_l. now apply Subset_Setminus.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite bound_var_fundefs_Fcons. rewrite Union_sym with (s4 := Singleton var v).
          do 2 rewrite <- Union_assoc. rewrite Union_sym with (s4 := Singleton var v).
          apply Included_Union_mon_r.
          apply Included_Union_compat. now apply Included_Union_r.
          now apply occurs_free_fundefs_Fcons_Included.
          (* TODO make this a lemma *)
        * eapply Disjoint_Included_r; [| eassumption ]. 
          rewrite bound_var_fundefs_Fcons. rewrite Union_sym with (s4 := Singleton var v).
          do 2 rewrite <- Union_assoc. rewrite Union_sym with (s4 := Singleton var v).
          apply Included_Union_mon_r.
          apply Included_Union_compat. now apply Included_Union_r.
          now apply occurs_free_fundefs_Fcons_Included.
        * eapply Included_trans; [| eassumption ]. now apply Included_Union_r.
        * intros B' s5.
          assert (Ha: exists v' tau1 tau2, Maps.PTree.get v FVmap = Some (MRFun v' tau1 tau2)).
          { destruct Minv as [_ [HM _]]. eapply HM. rewrite Setminus_Empty_set_Same_set.
            eapply Hinc. left; eauto. }
          destruct Ha as [v' [tau1 [tau2 Ha']]]. rewrite Ha'.
          eapply return_triple. intros s6 Hcc1 Hcc2 Hf.
          (* add params gives the same substitution *)
          edestruct (Hcc2 Hf) as [C1 [Hctx1 [[e'' [C1' [Hcc [Ha1 Ha2]]]] Hf1']]].
          destruct (Hcc1 Hf1') as [[B'' [Hcc1' Ha1']] Hf2'].
          split; [| eapply fresh_monotonic; [ now apply Subset_Setminus | eassumption ]].
          eexists. split. constructor; [| eassumption | eassumption ]. intros Hc.
          eapply HD1 with (x:=x). constructor. eapply Hf1. zify. omega.
          inv Hc; eauto. inv H1; now right; eauto.
          edestruct construct_lst_injection_add_params as [f' [Hfeq Hinj']].
          eapply Disjoint_Included_r; [| eassumption ]. left. now eauto. eassumption.
          rewrite <- Hfeq in Ha2. 
          econstructor. unfold subst. now rewrite Ha'. reflexivity. 
          eassumption. constructor. eassumption. 
          rewrite Hfeq. rewrite f_eq_extend_same. eapply injective_add_params.
          eapply Disjoint_Included_r; [| eassumption ]. left. now eauto. eassumption.
          eapply binding_not_in_map_add_params in Hbin2.  
          unfold subst. rewrite Hbin2. reflexivity. eapply Hf1. zify; omega.
          eapply Disjoint_Included_r; [| eassumption ]. now right; eauto.
          rewrite f_eq_extend_same, Hctx1. rewrite <- Hfeq in Ha1. now eauto.
          rewrite Hfeq. eapply binding_not_in_map_add_params in Hbin2.  
          unfold subst. rewrite Hbin2. reflexivity. eapply Hf1. zify; omega.
          eapply Disjoint_Included_r; [| eassumption ]. right. now eauto.      
    - eapply return_triple. intros Hc _ Hf.
      split; [| eassumption ]. eexists. now split; constructor.
    Admitted.
 *)
  Abort.

End CC_correct.
