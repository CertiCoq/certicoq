(* Correctness proof for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.tactics.
From CertiCoq.L6 Require Import cps size_cps cps_util set_util hoisting identifiers ctx
                       Ensembles_util List_util functions closure_conversion
                       closure_conversion_util eval logical_relations.
Require Import compcert.lib.Coqlib.
From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega
                        Sorting.Permutation ArithRing.
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
  Variable cenv : ctor_env.
  Variable clo_tag : ctor_tag.


  (** ** Semantics preservation proof *)

  (** We show observational approximation of the final results as well as an
    * upper bound on the concrete execution cost of the translated program *)


  (** *  Useful definitions and lemmas to express the upper bound. *)

  Definition max_exp_env (k : nat) (e : exp) (rho : env) :=
    max (sizeOf_exp e) (sizeOf_env k rho).

  
  Lemma max_exp_env_grt_1 k e rho :
    1 <= max_exp_env k e rho.
  Proof.
    unfold max_exp_env.
    eapply le_trans. now apply sizeOf_exp_grt_1.
    eapply Max.le_max_l.
  Qed.

  (** Lemmas used to establish the upper bound given the IH *)

  Lemma max_exp_env_Econstr k x t ys e rho :
    max_exp_env k e rho <= max_exp_env k (Econstr x t ys e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eproj k x t N y e rho :
    max_exp_env k e rho <= max_exp_env k (Eproj x t N y e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_hd k x c e l rho :
    max_exp_env k e rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_tl k x c e l rho :
    max_exp_env k (Ecase x l) rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eprim k x f ys e rho :
    max_exp_env k e rho <= max_exp_env k (Eprim x f ys e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Efun k B e rho :
    max_exp_env k e (def_funs B B rho rho) <= max_exp_env k (Efun B e) rho.
  Proof.
    unfold max_exp_env. eapply le_trans.
    - eapply NPeano.Nat.max_le_compat_l.
      now apply sizeOf_env_def_funs.
    - rewrite (Max.max_comm (sizeOf_env _ _)), Max.max_assoc.
      eapply NPeano.Nat.max_le_compat_r.
      eapply Nat.max_lub; simpl; omega.
  Qed.

  (** * Definition of the bounds *)

  (** Local predicate. Enforced only for the cost of the particular expressions
    * related. It's likely that the upper bound can be refined further *)

  Definition upper_boundL := 
    fun i (e1 : exp) (rho1 : env) (c1 c2 : nat) =>
      c2 <= 8 * c1 * (max_exp_env i e1 rho1) + 8 * sizeOf_exp e1.

  Definition lower_boundL := 
    fun (c1 c2 : nat) => c1 <= c2.
  
  Definition boundL (i : nat) (e1 : exp) (rho1 : env) (c1 : nat) (c2 : nat) : Prop :=
    lower_boundL c1 c2 /\ upper_boundL i e1 rho1 c1 c2.
  
  (* Global predicate. Enforced on values.  *)
  Definition boundG (k : nat) (p1 : exp * env * nat) (p2 : exp * env * nat) : Prop :=
    let '(e1, rho1, c1) := p1 in
    let '(e2, rho2, c2) := p2 in
    boundL k e1 rho1 c1 c2.
  
  (** Invariant about the values of free variables. *)
  Definition closure_env k rho Scope Funs GFuns vs FVs : Prop :=
      Forall2 (fun x v' => 
                 forall v, ~ In _ Scope x ->
                      ~ In _ Funs x ->
                      ~ In _ GFuns x ->
                      M.get x rho = Some v ->
                      cc_approx_val pr cenv clo_tag k boundG v v') FVs vs.
  
  (** Invariant about the free variables *) 
  Definition FV_inv k rho rho' Scope Funs GFuns c Γ FVs : Prop :=
    exists c' (vs : list val),
      M.get Γ rho' = Some (Vconstr c' vs) /\
      (FVs <> [] -> c' = c) /\ (* Because if FVs = [] we don't care about c' *)
      Forall2 (fun x v' => 
                 forall v, ~ In _ Scope x ->
                      ~ In _ Funs x ->
                      ~ In _ GFuns x ->
                      M.get x rho = Some v ->
                      cc_approx_val pr cenv clo_tag k boundG v v') FVs vs.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv k (rho rho' : env) Scope Funs σ Γ : Prop :=
    forall f v,
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho = Some v  ->
      exists env rho1 B1 f1 rho2 B2 f2,
        M.get Γ rho' = Some env /\
        v = (Vfun rho1 B1 f1) /\
        ~ In _ Scope (σ f) /\
        M.get (σ f) rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val pr cenv clo_tag k boundG
                      (Vfun rho1 B1 f1)
                      (Vconstr clo_tag [(Vfun rho2 B2 f2) ; env]).

  (** Invariant about the functions in the current function definition *)
  Definition GFun_inv k (rho rho' : env) Scope GFuns σ : Prop :=
    forall f v c,
      In var GFuns f ->
      M.get f rho = Some v  ->
      exists rho1 B1 f1 rho2 B2 f2,
        v = (Vfun rho1 B1 f1) /\
        ~ In _ Scope (σ f) /\ (* Check if needed *)
        M.get (σ f) rho' = Some (Vfun rho2 B2 f2) /\
        cc_approx_val pr cenv clo_tag k boundG
                      (Vfun rho1 B1 f1)
                      (Vconstr clo_tag [(Vfun rho2 B2 f2) ; (Vconstr c [])]).


  (** * Lemmas about Fun_inv *)

  (** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
  Lemma Fun_inv_set k rho rho' Scope Funs σ Γ f rho1 B1 f1 rho2 B2 f2 env:
    Fun_inv k rho rho' Scope Funs σ Γ ->
    (σ f) <> Γ ->
    ~ In _ Scope (σ f) ->
    ~ In _ (image σ (Setminus _ Funs Scope)) (σ f) ->
    M.get Γ rho' = Some env ->
    (cc_approx_val pr cenv clo_tag k boundG (Vfun rho1 B1 f1)
                   (Vconstr clo_tag [(Vfun rho2 B2 f2) ; env])) ->
    Fun_inv k (M.set f (Vfun rho1 B1 f1) rho)
            (M.set (σ f) (Vfun rho2 B2 f2) rho')
            Scope (Union _ (Singleton _ f) Funs) σ Γ.
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
  Lemma Fun_inv_rename k rho1 rho2 Scope Funs σ Γ Γ' v :
    ~ In _ (image σ (Setminus _ Funs Scope)) Γ ->  ~ In _ (image σ Funs) Γ' ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
    Fun_inv k rho1 (M.set Γ' v rho2) Scope Funs σ Γ'.
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
  Lemma Fun_inv_mon k rho1 rho2 Scope Scope' Funs σ Γ :
    Disjoint _ (image σ (Setminus _ Funs Scope)) Scope' ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Fun_inv k rho1 rho2 (Union _ Scope' Scope) Funs σ Γ.
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
  Lemma Fun_inv_set_In_Scope_l k rho1 rho2 Scope Funs σ Γ x v :
    In _ Scope x ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Fun_inv k (M.set x v rho1) rho2 Scope Funs σ Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

    (** Extend the first environment with a variable in not in [Funs] *)
  Lemma Fun_inv_set_not_In_Funs_l k rho1 rho2 Scope Funs σ Γ x v :
    ~ In _ Funs x  ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Fun_inv k (M.set x v rho1) rho2 Scope Funs σ Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

  (** Extend the first environment with a variable in not in [Funs] *)
  Lemma Fun_inv_funs_monotonic k rho1 rho2 Scope Funs Funs' σ Γ :
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Funs' \subset Funs -> 
    Fun_inv k rho1 rho2 Scope Funs' σ Γ.
  Proof.
    intros Hin Hinv f v' Hninf Hinf Hget.
    eapply Hin; eauto.
  Qed.
  
  (** Extend the second environment with a variable in [Scope] *)
  Lemma Fun_inv_set_In_Scope_r k rho1 rho2 Scope Funs σ Γ x v v' :
    In _ Scope x ->  ~ In _ (image σ (Setminus _ Funs Scope)) x ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
    Fun_inv k rho1 (M.set Γ v (M.set x v' rho2)) Scope Funs σ Γ.
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
  Lemma Fun_inv_set_In_Scope_r_not_Γ k rho1 rho2 Scope Funs σ Γ x v :
    In _ Scope x -> Γ <> x ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs σ Γ.
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
  Lemma Fun_inv_set_not_In_Funs_r_not_Γ k rho1 rho2 Scope Funs σ Γ x v :
    ~ In _ (image σ (Setminus _ Funs Scope)) x ->
    x <> Γ -> 
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    Fun_inv k rho1 (M.set x v rho2) Scope Funs σ Γ.
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
  Lemma Fun_inv_set_lists_In_Scope_l k rho1 rho1' rho2 Scope Funs σ Γ xs vs :
    Included _ (FromList xs) Scope ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    set_lists xs vs rho1 = Some rho1' ->
    Fun_inv k rho1' rho2 Scope Funs σ Γ.
  Proof.
    revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
    - intros Hinc Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho1) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply Fun_inv_set_In_Scope_l.
      + rewrite FromList_cons in Hinc. 
        eapply Hinc. eauto.
      + eapply IHxs; eauto.
        rewrite FromList_cons in Hinc. 
        eapply Included_trans; [| eassumption ].
        eapply Included_Union_r.
  Qed.

  (** Extend the second environment with a list of variables in [Scope] *)
  Lemma Fun_inv_set_lists_In_Scope_r k rho1 rho2 rho2' Scope Funs σ Γ xs vs v :
    Included _ (FromList xs) Scope ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (FromList xs) ->
    Fun_inv k rho1 (M.set Γ v rho2) Scope Funs σ Γ ->
    set_lists xs vs rho2 = Some rho2' ->
    Fun_inv k rho1 (M.set Γ v rho2') Scope Funs σ Γ.
  Proof.
    revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
    - intros Hinc Hd Hfun Hset. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hd Hfun Hset.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho2) eqn:Heq; [ | discriminate ]. inv Hset.
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
    M.get Γ rho' = Some v ->
    Fun_inv k rho (def_funs B B rho' rho') Scope Funs σ Γ ->
    Fun_inv k rho (M.set Γ v (def_funs B B rho' rho')) Scope Funs σ Γ.
  Proof. 
    intros Hnin Hget Hinv f v1 Hninf Hinf Hget'.
    edestruct Hinv with (f := f) as
        [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
    rewrite def_funs_neq in Hget1; eauto. subst.
    repeat subst_exp.
    repeat eexists; eauto.
    now rewrite M.gss.
    eapply def_funs_spec in Hget2. destruct Hget2 as [[Hname Heq] | [Hname Hget'']].
    - inv Heq. rewrite M.gso.
      rewrite def_funs_eq. reflexivity. eassumption.
      intros Hc; subst; eauto.
    - destruct (peq (σ f) Γ); subst.
      rewrite M.gss. congruence.
      rewrite M.gso.
      rewrite def_funs_neq; eauto. 
      now intros Hc; subst; eauto.
  Qed.

  Global Instance Fun_inv_proper :
    Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Same_set var ==>
                     Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
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
  Lemma Fun_inv_def_funs_l k rho rho' B1 B1' Scope Funs σ Γ:
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') -> 
    Fun_inv k rho rho' Scope Funs σ Γ ->
    Fun_inv k (def_funs B1 B1' rho rho) rho'
            (Union _ (name_in_fundefs B1')  Scope) Funs σ Γ.
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
  Lemma Fun_inv_def_funs_r k rho rho' B1 B1' Scope Funs σ Γ:
    ~ In _ (name_in_fundefs B1') Γ ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') -> 
    Fun_inv k rho rho' Scope Funs σ Γ ->
    Fun_inv k rho (def_funs B1 B1' rho' rho')
            (Union _ (name_in_fundefs B1') Scope) Funs σ Γ.
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
  Lemma Fun_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs σ Γ:
    ~ In _ (name_in_fundefs B2') Γ -> ~ In _ (name_in_fundefs B1') Γ ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B1') ->
    Disjoint _ (image σ (Setminus _ Funs Scope)) (name_in_fundefs B2') ->
    Fun_inv k rho rho' Scope Funs σ Γ ->
    Fun_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
            (Union _ (name_in_fundefs B1') Scope) Funs σ Γ.
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
  Lemma FV_inv_set_In_Scope_l k rho rho' x v Scope Funs GFuns FVs c Γ :
    In var Scope x ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hin [g [c' [Hget [Hleq HInv]]]].
    destruct FVs.
    - inv HInv. exists g.
      eexists; repeat split; eauto.
    - do 2 eexists; repeat split; eauto.
      rewrite <- Hleq; eauto. congruence.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros z w Hin1 Hin2 He v1 Hnin1 Hnin2 Hnin3 Hget'.
      eapply He; eauto. rewrite M.gso in Hget'; eauto.
      intros Hc; subst; contradiction. 
  Qed.
  
  (** Extend the first environment with a variable not in [FVs] *)
  Lemma FV_inv_set_not_In_FVs_l k rho rho' x v Scope Funs GFuns c Γ FVs :
    ~ List.In x FVs ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k (M.set x v rho) rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hnin [c' [g [Hget [Hleq HInv]]]].
    destruct FVs.
    - inv HInv. exists c'.
      eexists; repeat split; eauto.
    - do 2 eexists; repeat split; eauto.
      rewrite <- Hleq; eauto. congruence.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros z w Hin1 Hin2 He v1 Hnin1 Hnin2 Hnin3 Hget'.
      eapply He; eauto. rewrite M.gso in Hget'; eauto.
      intros Hc; subst; contradiction. 
  Qed.
  
  (** Extend the second environment with a variable that is not [Γ] *)
  Lemma FV_inv_set_r k rho rho' x v Scope Funs GFuns c Γ FVs :
    x <> Γ ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho (M.set x v rho') Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hnin [c' [g [Hget HInv]]]. do 2 eexists; split; eauto.
    rewrite M.gso; eauto.
  Qed.


  (** Extend the [Scope] and remove from [GFuns] **)
  Lemma FV_inv_extend_Scope_GFuns k rho rho' Scope GFuns Funs c Γ FVs x :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho rho' (x |: Scope) Funs (GFuns \\ [set x]) c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros; eauto. eapply H1; eauto.
    intros Hc'; eapply H4. constructor; eauto.  
  Qed.

  Lemma FV_inv_monotonic k j rho rho' Scope GFuns Funs c Γ FVs :
    FV_inv j rho rho' Scope Funs GFuns c Γ FVs ->
    j >= k ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros; eauto. eapply cc_approx_val_monotonic. eauto. eassumption.
  Qed.

  Lemma FV_inv_antimonotonic_GFuns k rho rho' Scope GFuns1 GFuns2 Funs c Γ FVs :
    FV_inv k rho rho' Scope Funs GFuns1 c Γ FVs ->
    GFuns1 \subset GFuns2 ->
    FV_inv k rho rho' Scope Funs GFuns2 c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
  Qed.
  
  Lemma FV_inv_antimonotonic_add_global_funs k rho rho' Scope GFuns GFuns' names {Hd : Decidable names} Funs c Γ FVs FVs' :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    add_global_funs GFuns names (FromList FVs') GFuns' ->
    names \subset Scope ->
    FV_inv k rho rho' Scope Funs GFuns' c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]] Hadd Hsub. inv Hadd; eauto.
    - do 2 eexists; split; eauto.
      split; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    - do 2 eexists; split; eauto.
      split; eauto.
      eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
      intros. eapply H2; eauto.    
      destruct Hd. destruct (Dec x1); eauto. intros Hc1.
      eapply H5. constructor; eauto. 
  Qed.

  Lemma FV_inv_Forall2 k rho rho' Scope GFuns Funs c Γ FVs vs1 vs2 :
    get_list FVs rho = Some vs1 ->
    M.get Γ rho' = Some (Vconstr c vs2) ->
    Forall2 (cc_approx_val pr cenv clo_tag k boundG) vs1 vs2 ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hget1 Hget2 Hall. do 2 eexists; split; eauto. 
    split; eauto. clear Hget2.
    revert vs1 vs2 Hget1 Hall; induction FVs; intros vs1 vs2 Hget1 Hall;
      destruct vs2; try (now inv Hget1).
    + inv Hall; eauto.
      eapply get_list_length_eq in Hget1. simpl in Hget1. congruence.
    + inv Hall.
      constructor; eauto.
      * intros. simpl in Hget1.
        rewrite H4 in Hget1.
        destruct (get_list FVs rho) eqn:Hfv; try congruence.
      * simpl in Hget1.
        destruct (get_list FVs rho) eqn:Hfv; try congruence; destruct (M.get a rho); try congruence. 
        inv Hget1. eapply IHFVs; eauto.
  Qed.

  (** Extend the [Scope]. TODO : replace with monotonicity property? *)
  Lemma FV_inv_extend_Scope k rho rho' Scope GFuns Funs c Γ FVs x :
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k rho rho' (Union _ (Singleton _ x) Scope) Funs GFuns c Γ FVs.
  Proof.
    intros [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
  Qed.
  
  (** Define a block of functions in both environments and put the in the
    current scope *)
  Lemma FV_inv_def_funs k rho rho' B1 B1' B2 B2' Scope Funs GFuns c Γ FVs:
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    FV_inv k  (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho')
           (Union _ (name_in_fundefs B1') Scope) Funs GFuns c Γ FVs.
  Proof.
    intros Hnin1 Hnin2 [c' [g [Hget [Hc HInv]]]]. do 2 eexists; split; eauto.
    now rewrite def_funs_neq; eauto.    
    split; eauto.
    eapply Forall2_monotonic_strong; [| eassumption ]; eauto.
    intros z w Hin1 Hin2 He v1 Hnin3 Hnin4 Hnin5 Hget'.
    eapply He; eauto. now rewrite def_funs_neq in Hget'; eauto.
  Qed.

  (** * Lemmas about [GFun_inv]  *)

  (** Extend the two environments with a variable that is not the current environment
    argument (i.e. [Γ]) *)
  Lemma GFun_inv_set k rho rho' Scope GFuns σ f rho1 B1 f1 rho2 B2 f2:
    GFun_inv k rho rho' Scope (GFuns \\ [set f]) σ ->
    ~ In _ Scope (σ f) ->
    ~ In _ (image σ (GFuns \\ [set f])) (σ f) ->
    (forall c, f \in GFuns ->
          cc_approx_val pr cenv clo_tag k boundG (Vfun rho1 B1 f1) (Vconstr clo_tag [(Vfun rho2 B2 f2) ; Vconstr c []])) ->
    GFun_inv k (M.set f (Vfun rho1 B1 f1) rho) (M.set (σ f) (Vfun rho2 B2 f2) rho') Scope GFuns σ.
  Proof.
    intros Hinv Hnin Hnin' Hv f'' v Hnin'' Hin Hget'.
    destruct (peq f'' f); subst; eauto.
    - rewrite M.gss in Hget'. inv Hget'. repeat eexists; eauto.
      now rewrite M.gss.
    - rewrite M.gso in Hget'; eauto.
      edestruct Hinv with (f0 := f'') as
          [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq [Ηnin2 [Hget2 Happrox]]]]]]]]]; subst; eauto.
      constructor; eauto. intros Hc. inv Hc. congruence. repeat eexists; eauto.
      rewrite M.gso. now eauto. 
      intros Hc. eapply Hnin'. rewrite <- Hc. eapply In_image. constructor; eauto.
      intros Hc'. inv Hc'. contradiction.
  Qed.
  
  (** Extend the first environment with a variable not in [GFuns] *)
  Lemma GFun_inv_set_not_In_GFuns_l k rho1 rho2 Scope GFuns σ x v :
    ~ x \in GFuns ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    GFun_inv k (M.set x v rho1) rho2 Scope GFuns σ.
  Proof.
    intros Hnin Hinv f v' c Hin Hget.
    eapply Hinv; eauto. rewrite M.gso in Hget.
    now eauto. intros Hc; subst. now eauto.
  Qed.

  (** Extend the second environment with a variable in [GFuns] *)
  Lemma GFun_inv_set_not_In_GFuns_r k rho1 rho2 Scope GFuns σ x v :
    ~ x \in (image σ GFuns) ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    GFun_inv k rho1 (M.set x v rho2) Scope GFuns σ.
  Proof.
    intros Hnin Hinv f v' c Hin Hget.
    edestruct Hinv as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite M.gso. eassumption.
    intros Hc. eapply Hnin. subst. eapply In_image. eassumption. 
  Qed.

  (** Extend the first environment with a variable not in [GFuns] *)
  Lemma GFun_inv_setlist_not_In_GFuns_l k rho1 rho1' rho2 Scope GFuns σ xs vs :
    Disjoint _ (FromList xs) GFuns ->
    set_lists xs vs rho1 = Some rho1' ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    GFun_inv k rho1' rho2 Scope GFuns σ.
  Proof.
    revert rho1 rho1' vs. induction xs; intros rho1 rho1' vs.
    - intros Hinc Hset Hfun. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hset Hfun.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho1) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply GFun_inv_set_not_In_GFuns_l.
      + intros Hc; eapply Hinc. constructor; eauto.
        now left.
      + eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        rewrite FromList_cons; sets.
  Qed.

  (** Extend the second environment with a list not in [GFuns] *)
  Lemma GFun_inv_setlist_not_In_GFuns_r k rho1 rho2' rho2 Scope GFuns σ xs vs :
    Disjoint _ (FromList xs) (image σ GFuns) ->
    set_lists xs vs rho2 = Some rho2' ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    GFun_inv k rho1 rho2' Scope GFuns σ.
  Proof.
    revert rho2 rho2' vs. induction xs; intros rho2 rho2' vs.
    - intros Hinc Hset Hfun. inv Hset.
      destruct vs; [ | discriminate ]. now inv H0.
    - intros Hinc Hset Hfun.
      simpl in Hset.
      destruct vs; [ discriminate | ].
      destruct (set_lists xs vs rho2) eqn:Heq; [ | discriminate ]. inv Hset.
      eapply GFun_inv_set_not_In_GFuns_r.
      + intros Hc; eapply Hinc. constructor; eauto.
        now left.
      + eapply IHxs; eauto.
        eapply Disjoint_Included_l; [| eassumption ].
        rewrite FromList_cons; sets.
  Qed.

  (** Extend the first environment with funs not in [GFuns] *)
  Lemma GFun_inv_def_funs_not_In_GFuns_l k rho1 rho2 Scope GFuns σ B1 B1' :
    Disjoint _ (name_in_fundefs B1') GFuns ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    GFun_inv k (def_funs B1 B1' rho1 rho1) rho2 Scope GFuns σ.
  Proof.
    intros HD Hinv f v1 c Hinf Hget. rewrite def_funs_neq in Hget; eauto.
    intros Hc. eapply HD. constructor; eauto.
  Qed.

  Lemma GFun_inv_def_funs_not_In_GFuns_r k rho rho' B1 B1' Scope GFuns σ :
    Disjoint _ (image σ GFuns) (name_in_fundefs B1') ->
    GFun_inv k rho rho' Scope GFuns σ ->
    GFun_inv k rho (def_funs B1 B1' rho' rho') Scope GFuns σ.
  Proof.
    intros HD Hinv f v1 c Hinf Hget. setoid_rewrite def_funs_neq; eauto.
    intros Hc. eapply HD. constructor; sets.
  Qed.

  Lemma GFun_inv_antimon k rho rho' Scope GFuns GFuns' σ :
     GFun_inv k rho rho' Scope GFuns σ ->
     GFuns' \subset GFuns ->
     GFun_inv k rho rho' Scope GFuns' σ .
  Proof.
    intros Hg Hsub f v1 Hinf Hget; eauto.
  Qed.

  Lemma GFun_inv_Scope k rho rho' Scope Scope' GFuns σ :
    Disjoint _ Scope' (image σ GFuns) -> 
    GFun_inv k rho rho' Scope GFuns σ ->
    GFun_inv k rho rho' Scope' GFuns σ.
  Proof.
    intros Hd Hg f v1 c Hinf Hget; eauto.
    edestruct Hg as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq1 & Hnin & Hget1 & Hcc); eauto.
    repeat eexists; eauto.
    intros Hc. eapply Hd. constructor; eauto.
    eapply In_image. eassumption.
  Qed. 

  Lemma GFun_inv_monotonic k j rho rho' Scope GFuns σ :
    GFun_inv k rho rho' Scope GFuns σ ->
    j <= k ->
    GFun_inv j rho rho' Scope GFuns σ.
  Proof.
    intros Hg Hleq c f v1 Hinf Hget; eauto.
    edestruct Hg as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq1 & Hnin & Hget1 & Hcc); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
  
  Lemma GFun_inv_Scope_extend k rho rho' Scope Scope' GFuns σ :
    Disjoint _ (image σ GFuns) Scope' ->
    GFun_inv k rho rho' Scope GFuns σ ->
    GFun_inv k rho rho' (Scope' :|: Scope) GFuns σ.
  Proof.
    intros Hdis Hg f v1 c1 Hinf Hget; eauto.
    edestruct Hg as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq & Hnin & Hget' & Hcc); eauto.
    subst. repeat eexists; eauto.
    intros Hc. inv Hc; eauto.
    eapply Hdis. constructor; eauto.
    now eapply In_image. 
  Qed.

  Lemma GFun_inv_fuse k rho rho' Scope1 Scope2 GFuns1 GFuns2 σ names FVs { Hd : Decidable names} :
    add_global_funs GFuns1 names FVs GFuns2 ->
    GFun_inv k rho rho' Scope1 (GFuns1 \\ names) σ ->
    GFun_inv k rho rho' Scope2 GFuns2 σ ->
    Scope2 \subset Scope1 ->
    Disjoint _ Scope1 (image σ names) ->
    GFun_inv k rho rho' Scope1 GFuns2 σ.
  Proof.
    intros Ha Hg1 Hg2 Hsub Hd' x v c Hin1 Hget. inv Ha.
    - destruct Hd. destruct (Dec x); eauto.
      * edestruct Hg2 as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq1 & Hnin & Hget1 & Hcc); eauto.
        repeat eexists; eauto.
        intros Hc. eapply Hd'. constructor; eauto.
        eapply In_image. eassumption.
      * inv Hin1; try contradiction.  
        edestruct Hg1 as (rho1 & B1 & f1 & rho2 & B2 & f2 & Heq1 & Hnin & Hget1 & Hcc); eauto.
        constructor; eauto.
        repeat eexists; eauto.
    - eauto.
  Qed.

  Lemma Fun_inv_from_GFun_inv k rho1 rho2 Scope GFuns Funs σ Γ c :
    Funs \subset GFuns -> 
    GFun_inv k rho1 rho2 Scope (GFuns \\ Scope) σ ->
    M.get Γ rho2 = Some (Vconstr c []) ->  
    Fun_inv k rho1 rho2 Scope Funs σ Γ.
  Proof.
    intros Hsub Hinv Hget f v' Hnin Hin Hget'.
    edestruct Hinv as
        [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]; eauto.
    now constructor; eauto. 
    repeat eexists; eauto.
  Qed.
  
  (** * Lemmas about the existance of the interpretation of an evaluation context *)
  
  Lemma project_var_ctx_to_rho Scope Funs GFuns σ c Γ FVs x x' C S S' v1 k rho1 rho2 :
    Disjoint _ S (image σ (GFuns \\ Scope)) ->
    project_var clo_tag Scope Funs GFuns σ c Γ FVs S x x' C S' ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    M.get x rho1 = Some v1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof.
    intros Hg Hproj HFV HFun HGfun Hget. inv Hproj.
    - eexists; econstructor; eauto.
    - edestruct HFun as
          [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
      eexists; econstructor; eauto.
      simpl. rewrite Hget2. rewrite Hget1. reflexivity.
      constructor.
    - edestruct HGfun with (c := c) as
          [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]; eauto.
      eexists; econstructor; eauto. reflexivity. 
      subst. econstructor.
      simpl. rewrite M.gso, Hget2.
      rewrite M.gss. reflexivity.
      intros Hc; subst. eapply Hg. constructor.
      now eapply H3. eapply In_image. now constructor; eauto.
      constructor.
    - edestruct HFV as [c' [g [Hgetg [Hleq Hin]]]].
      eapply Forall2_nthN in Hin; eauto.
      destruct Hin as [v2 [Hnth' Hyp]]. destruct FVs; try now inv H2.
      rewrite Hleq in *; try congruence. 
      eexists. econstructor; eauto. constructor. 
  Qed.

  Lemma make_closures_ctx_to_rho B S Γ C σ S' k rho1 rho2 :
    make_closures clo_tag B S Γ C σ S' ->
    unique_functions B ->
    Disjoint _ S (name_in_fundefs B) ->
    ~ In _ (name_in_fundefs B) Γ ->
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ Γ ->
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
      + intros. eapply Hyp. right; eauto.
      + eexists. econstructor; eauto.
        simpl. rewrite Hget1, Hget2. reflexivity.
  Qed.
  
  Lemma project_vars_ctx_to_rho Scope Funs GFuns σ c Γ FVs xs xs' C S S' vs1 k rho1 rho2 :
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
    project_vars clo_tag Scope Funs GFuns σ c Γ FVs S xs xs' C S' ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ -> 
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    get_list xs rho1 = Some vs1 ->
    exists rho2', ctx_to_rho C rho2 rho2'.
  Proof. 
    revert Scope Funs Γ FVs xs' C S S' vs1 k
           rho1 rho2.
    induction xs;
      intros Scope Funs Γ FVs xs' C S S' vs1 k
             rho1 rho2 HD Hvars HFun HGfun HFV Hget_list.
    - inv Hvars. eexists; econstructor; eauto.
    - inv Hvars. simpl in Hget_list.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate. 
      destruct (get_list xs rho1) eqn:Hget_list1; try discriminate. 
      edestruct project_var_ctx_to_rho with (rho1 := rho1) as [rho2' Hctx1]; eauto.
      eapply Disjoint_Included_r; [| eassumption ].
      now eauto 10 with Ensembles_DB functions_BD. 
      edestruct IHxs with (rho2 := rho2') as [rho2'' Hctx2].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + eassumption.
      + inv Hget_list. intros f v' Hnin Hin Hget.
        edestruct HFun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        repeat eexists; eauto.
        erewrite <- project_var_get; eauto.  intros Hc. eapply HD. now eauto.
        erewrite <- project_var_get; eauto. 
        intros Hin'. eapply HD. constructor. now eauto.
        right. left. eapply In_image. do 2 constructor; eauto.
      + intros x v1 c' Hin Hget. inv Hget_list.
        edestruct HGfun as [rho0 [B1 [f1 [rho3 [B2 [f2 [Heq1 [Hnin [Hget' Hcc]]]]]]]]]; eauto.
        subst.
        repeat eexists; eauto. 
        erewrite <- project_var_get; eauto.
        intros Hin'. eapply HD. constructor; eauto.
        right. left. eapply In_image. right. eauto.
      + edestruct HFV as [c' [g [Hgetg [Hleq Hinv]]]].
        exists c'.  eexists; split; eauto.
        erewrite <- project_var_get; eauto.
        intros Hin. eapply HD. now eauto.
      + eassumption.
      + exists rho2''. eapply ctx_to_rho_comp_ctx_f_r; eassumption.
  Qed.

  Lemma add_global_funs_included G F {_ : Decidable F} V G' :
    add_global_funs G F V G' ->
    G \subset G' :|: F.
  Proof. 
    intros Hin. inv Hin; sets.
  Qed.
  
  Lemma add_global_funs_included_r G F V G' :
    add_global_funs G F V G' ->
    G' \subset G :|: F.
  Proof. 
    intros Hin. inv Hin; sets.
  Qed.

  Definition is_gfuns (GFuns : Ensemble var) names (FVs : list var) GFuns' :=
    (FVs = [] /\ GFuns' \subset GFuns :|: names) \/
    (FVs <> [] /\ GFuns' \subset GFuns \\ names).

  Lemma add_global_funs_is_gfuns (GFuns : Ensemble var) names (FVs : list var) GFuns':
    add_global_funs GFuns names (FromList FVs) GFuns' ->
    is_gfuns GFuns names FVs GFuns'.
  Proof.
    intros Hin; destruct FVs; inv Hin; unfold is_gfuns; sets.
    - exfalso. eapply not_In_Empty_set. eapply H.
      now left.
    - right. split; sets. congruence.
  Qed.

  Lemma is_gfuns_setminus (GFuns : Ensemble var) names (FVs : list var) GFuns' x:
   is_gfuns GFuns (x |: names) FVs GFuns' ->
   is_gfuns GFuns names FVs (GFuns' \\ [set x]).
  Proof.
    intros [[H1 H2] | [H1 H2]]; subst; unfold is_gfuns in *.
    left; split; eauto.
    eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. sets.
    right; split; eauto.
    eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption. sets.
  Qed.

  Lemma is_gfuns_included_r G F {_ : Decidable F} V G' :
    is_gfuns G F V G' ->
    G' \subset G :|: F.
  Proof. 
    intros Hin. destruct Hin as [[? ?] | [? ?]]; subst; sets.
    eapply Included_trans. eassumption. sets.
  Qed.

  Lemma add_global_funs_is_gfuns_included (GFuns : Ensemble var) names (FVs : list var) GFuns' GFuns'' :
    add_global_funs GFuns names (FromList FVs) GFuns' ->
    is_gfuns GFuns names FVs GFuns'' ->
    GFuns'' \subset GFuns'.
  Proof.
    intros Hadd Hin; destruct Hin as [[? ?] | [? ?]]; inv Hadd; unfold is_gfuns; sets.
    - eapply Included_trans. eassumption. sets.
    - rewrite FromList_nil in H1. exfalso; eapply H1; reflexivity.
    - eapply Included_trans. eassumption. sets.
  Qed.

  (** * Correctness lemmas *)

  (** Correctness of [closure_conversion_fundefs]. Basically un-nesting the nested
      induction that is required by the correctness of [Closure_conversion] *) 
  Lemma Closure_conversion_fundefs_correct k rho rho' B1 B2 B1' B2'
        Scope c Γ FVs Funs' GFuns GFuns' GFuns'' σ FVs' :
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e : exp) (rho rho' : env) (e' : exp)
         (Scope Funs GFuns : Ensemble var) σ c (Γ : var) (FVs : list var)
         (C : exp_ctx),
         cc_approx_env_P pr cenv clo_tag Scope m boundG rho rho' ->
         ~ In var (bound_var e) Γ ->
         binding_in_map (occurs_free e) rho ->
         fundefs_names_unique e ->
         injective_subdomain (Funs \\ Scope :|: GFuns) σ ->
         Disjoint var (image σ (Funs \\ Scope :|: GFuns)) (bound_var e) ->
         Fun_inv m rho rho' Scope Funs σ Γ ->
         GFun_inv m rho rho' Scope GFuns σ ->
         FV_inv m rho rho' Scope Funs GFuns c Γ FVs ->
         Closure_conversion clo_tag Scope Funs GFuns σ c Γ FVs e e' C ->
         cc_approx_exp pr cenv clo_tag m (boundL m e rho) boundG (e, rho) (C |[ e' ]|, rho')) ->
    (* FVs *)
    (occurs_free_fundefs B1 \\ GFuns) <--> (FromList FVs) ->
    (* unique functions *)
    fundefs_names_unique_fundefs B1 ->
    fundefs_names_unique_fundefs B1' ->
    binding_in_map (occurs_free_fundefs B1) rho ->
    GFun_inv k rho rho' Scope GFuns σ ->
    is_gfuns GFuns (name_in_fundefs B1') FVs GFuns'' ->
    add_global_funs GFuns (name_in_fundefs B1) (FromList FVs) GFuns' ->
    (* Closure Conversion *)
    Closure_conversion_fundefs clo_tag (name_in_fundefs B1) GFuns' σ c FVs B1 B2 ->
    Closure_conversion_fundefs clo_tag Funs' GFuns' σ c FVs' B1' B2' ->
    Disjoint _ (image σ (name_in_fundefs B1 :|: GFuns')) (bound_var_fundefs B1) ->
    Disjoint _ (image σ (name_in_fundefs B1')) Scope ->
    Same_set _ (image σ (name_in_fundefs B1)) (name_in_fundefs B2) ->
    injective_subdomain (name_in_fundefs B1 :|: GFuns) σ ->
    injective_subdomain (name_in_fundefs B1' :|: GFuns) σ ->
    ~ In _ (image σ GFuns :|: name_in_fundefs B1) Γ ->
    ~ In _ (name_in_fundefs B1') Γ ->
    ~ In _ (name_in_fundefs B2) Γ ->
    ~ In _ (name_in_fundefs B2') Γ ->
    FV_inv k rho rho' (Empty_set _) (Empty_set _) GFuns c Γ FVs ->
    Fun_inv k (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho') Scope (name_in_fundefs B1') σ Γ /\
    GFun_inv k (def_funs B1 B1' rho rho) (def_funs B2 B2' rho' rho') Scope GFuns'' σ.
  Proof.
    revert B1' rho rho' B2 B1 B2' Scope Γ FVs Funs' GFuns GFuns' GFuns'' FVs' c. 
    induction k as [k IHk] using lt_wf_rec1.
    induction B1'; 
      intros rho rho' B2 B1 B2' Scope Γ FVs Funs' GFuns GFuns' GFuns'' FVs' c
             IHe Hs Hun Hun' Hfv Hgfun Hadd1 Hadd2 Hcc Hcc' Hd Hd'' Hseq Hinj Hinj' Hnin1 Hnin1' Hnin2 Hnin2' Henv.
    - inv Hcc'. 
      (* show the IH for B first *)
      assert (HB1 : Fun_inv k (def_funs B1 B1' rho rho) (def_funs B2 defs' rho' rho') Scope (name_in_fundefs B1') σ Γ /\
                    GFun_inv k (def_funs B1 B1' rho rho) (def_funs B2 defs' rho' rho') Scope (GFuns'' \\ [set v]) σ).
      { eapply IHB1'; eauto. 
        * intros B H. inv H; eauto. specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
          inv Hun'; eauto.
        * eapply is_gfuns_setminus. eassumption. 
        * eapply Disjoint_Included_l; [| eassumption ].
          eapply image_monotonic.  now apply Included_Union_r.
        * eapply injective_subdomain_antimon. eassumption. now sets.
        * intros Hc. apply Hnin1'. simpl; eauto.
        * intros Hc. apply Hnin2'. simpl; eauto. }
      destruct HB1 as [IHF IHG].
      (* Now show each goal separately *)
      split.
      + edestruct Henv as [c' [vs [Hgetg [Hleq Hallg]]]].
        simpl. eapply Fun_inv_set. 
        * eassumption.
        * intros Hc. eapply Hnin2'. subst. left. eauto.          
        * intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
          left. eauto.
        * simpl in Hinj'.
          assert (Hinj'' : injective_subdomain (v |: name_in_fundefs B1') σ). 
          { eapply injective_subdomain_antimon. eauto. sets. }
          eapply injective_subdomain_Union_not_In_image in Hinj''.
          intros Hc. eapply Hinj''. constructor; eauto. eexists; eauto.
          eapply image_monotonic; [| eassumption ]. now sets.
          eapply Disjoint_sym. eapply Disjoint_Singleton_r.
          specialize (Hun' (Fcons v f l e B1') (or_intror eq_refl)).
          inv Hun'; eauto.
        * rewrite def_funs_neq. eassumption.
          intros Hc. eapply Hnin2'. right. eauto.
        * (* Finally show that the added funs ares related *)     
          simpl. rewrite cc_approx_val_eq. 
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.  
          edestruct (@set_lists_length val)
            with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset'].
          eassumption. now eauto.
          edestruct closure_conversion_fundefs_find_def
            as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]; [  |  | eassumption |].
          eapply injective_subdomain_antimon. now eapply Hinj. now sets. eassumption. 
          exists Γ'', xs1. do 2 eexists.
          split. reflexivity. split. eassumption. split.
          simpl. rewrite Hset'. reflexivity.        
          intros Hlt Hall.
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) σ Γ /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) GFuns' σ).
          { eapply IHk with (Funs' := name_in_fundefs B1); try eassumption. 
            - intros. eapply IHe; eauto. omega.
            - eapply GFun_inv_Scope.
              eapply Disjoint_sym.
              eapply Disjoint_Included; [ | | now eapply Hd ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.  
              eapply image_monotonic. eapply Included_trans.
              eapply add_global_funs_included; [| eassumption ]; tci. now sets.
              eapply GFun_inv_monotonic; eauto. omega. 
            - eapply add_global_funs_is_gfuns. eassumption.
            - eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [ | now eapply Hd ] ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]...
              now sets. now sets.
            - sets.
            - eapply FV_inv_monotonic. eassumption. omega. }
          destruct HK as [Hkf Hkg].
          (* Apply IHe *)
          eapply IHe with (Scope := FromList xs1) (GFuns := GFuns' \\ FromList xs1). 
          -- eassumption.
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin''. right; left. eassumption.
          -- intros Hc. apply Hnin''. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- intros B Hin. eapply Hun. left. 
             eapply fun_in_fundefs_funs_in_fundef; eauto.
             eapply find_def_correct. eassumption.
          -- eapply injective_subdomain_antimon. now eapply Hinj.
             eapply Union_Included. eapply Included_Union_preserv_l. now eapply Setminus_Included.
             eapply Included_trans. eapply Setminus_Included.             
             rewrite Union_commut. eapply add_global_funs_included_r. eassumption.
          -- eapply Disjoint_Included;[ | | eapply Hd ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             rewrite !Union_assoc. now apply Included_Union_r.
          -- (* Fun_inv *)
             eapply Fun_inv_rename with (Γ := Γ). intros Hin. 
             eapply Hnin2. rewrite <- Hseq. eapply image_monotonic; [| eassumption ].
             now apply Setminus_Included.
             intros Hin. eapply Hnin''. left. rewrite image_Union. left; eassumption. 
             eapply Fun_inv_set_lists_In_Scope_l; [ now apply Included_refl | | now eauto ].
             eapply Fun_inv_set_lists_In_Scope_r; [ now apply Included_refl | | | eassumption ].
             eapply Disjoint_Included_r; 
               [| eapply Disjoint_Included_l;
                  [ apply image_monotonic; now apply Setminus_Included | eapply Disjoint_Included_l; [| now apply Hd ]]].
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             right; eauto. now sets. eapply Fun_inv_reset; eauto.
          -- eapply GFun_inv_set_not_In_GFuns_r.
             intros Hc. eapply Hnin''.
             left. eapply image_monotonic; [| eassumption ]. sets.
             eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ].
             now sets.
             eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ].
             eapply Disjoint_sym.
             eapply Disjoint_Included; [ | | now eapply Hd ].
             eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.
              eapply image_monotonic. sets.
              eapply GFun_inv_antimon. eassumption. sets.
          -- do 2 eexists. split. rewrite M.gss. reflexivity.
             split. intros. reflexivity.
             eapply Forall2_monotonic; [| eassumption ].
             intros x v1 Hyp v2 Hnin3 Hnin4 Hnin5 Hget'.  
             erewrite <- set_lists_not_In in Hget'; [| now eauto | eassumption ].
             erewrite def_funs_neq in Hget'.
             eapply cc_approx_val_monotonic. eapply Hyp; eauto.
             now eapply not_In_Empty_set. now eapply not_In_Empty_set.
             intros Hnin. eapply Hnin5. constructor; eauto.
             eapply add_global_funs_included in Hnin; [| | eassumption ]; tci. inv Hnin; eauto.
             contradiction. omega. eassumption.
          -- destruct FVs.
             eapply Closure_conversion_tag_inv. eassumption.
             rewrite Hleq. eassumption. congruence.
      + edestruct Henv as [c' [vs [Hgetg [Hleq Hallg]]]].
        simpl. eapply GFun_inv_set. 
        * eassumption.
        * intros Hc. eapply Hd''. constructor; eauto. eexists. split; eauto.
          left. eauto.
        * assert (Hda: Disjoint _ (image σ (GFuns'' \\ [set v])) [set (σ v)]).
          { rewrite <- image_Singleton. eapply injective_subdomain_Union_not_In_image; sets.
            eapply injective_subdomain_antimon; [ eassumption |  ].
            rewrite <- Union_Setminus; tci. eapply Union_Included; sets.
            eapply Included_trans. eapply is_gfuns_included_r; eauto; tci.
            sets. }
          intros Hc. eapply Hda. constructor; eauto.
        * (* Finally show that the added funs ares related *)     
          simpl. intros c'' Hin. rewrite cc_approx_val_eq.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hfind Hset.  
          edestruct (@set_lists_length val)
            with (rho' := def_funs B2 B2 rho' rho') as [rho2' Hset'].
          eassumption. now eauto.
          edestruct closure_conversion_fundefs_find_def
            as [Γ'' [C2 [e2 [Hnin'' [Hfind' Hcc']]]]]; [  |  | eassumption |]. 
          eapply injective_subdomain_antimon. now eapply Hinj. now sets. eassumption. 
          exists Γ'', xs1. do 2 eexists.
          split. reflexivity. split. eassumption. split.
          simpl. rewrite Hset'. reflexivity.        
          intros Hlt Hall.
          assert (HK : Fun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) (name_in_fundefs B1) σ Γ /\
                       GFun_inv j (def_funs B1 B1 rho rho) (def_funs B2 B2 rho' rho') (FromList xs1) GFuns' σ).
          { eapply IHk with (Funs' := name_in_fundefs B1); try eassumption. 
            - intros. eapply IHe; eauto. omega.
            - eapply GFun_inv_Scope.
              eapply Disjoint_sym.
              eapply Disjoint_Included; [ | | now eapply Hd ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
              now sets.  
              eapply image_monotonic. eapply Included_trans.
              eapply add_global_funs_included; [| eassumption ]; tci. now sets.
              eapply GFun_inv_monotonic; eauto. omega. 
            - eapply add_global_funs_is_gfuns. eassumption.
            - eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [ | now eapply Hd ] ].
              eapply Included_trans;
                [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ]...
              now sets. now sets.
            - sets.
            - eapply FV_inv_monotonic. eassumption. omega. }
          destruct HK as [Hkf Hkg].
          assert (Hgfun' : GFun_inv j rho1' (M.set Γ'' (Vconstr c'' []) rho2') (FromList xs1) 
                                    (GFuns' \\ FromList xs1) σ). 
          { eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply Hnin''.
            left. eapply image_monotonic; [| eassumption ]. sets.
            eapply GFun_inv_setlist_not_In_GFuns_l; [| now eauto | ].
            now sets.
            eapply GFun_inv_setlist_not_In_GFuns_r; [| now eauto | ].
            eapply Disjoint_sym.
            eapply Disjoint_Included; [ | | now eapply Hd ].
            eapply Included_trans;
              [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
            now sets.
            eapply image_monotonic. sets.
            eapply GFun_inv_antimon. eassumption. sets. }
          
          (* Apply IHe *) 
          eapply IHe with (Scope := FromList xs1) (GFuns := GFuns' \\ FromList xs1). 
          -- eassumption.
          -- eapply cc_approx_env_P_set_not_in_P_r.
             eapply cc_approx_env_P_set_lists_l with (P1 := Empty_set _); eauto.
             eapply cc_approx_env_Empty_set. now intros Hc; eauto.
             intros Hc. eapply Hnin''. right; left. eassumption.
          -- intros Hc. apply Hnin''. eauto.
          -- eapply binding_in_map_antimon.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
             eapply binding_in_map_set_lists; [| now eauto ].
             eapply binding_in_map_def_funs. eassumption.
          -- intros B Hin'. eapply Hun. left. 
             eapply fun_in_fundefs_funs_in_fundef; eauto.
             eapply find_def_correct. eassumption.
          -- eapply injective_subdomain_antimon. now eapply Hinj.
             eapply Union_Included. eapply Included_trans. eapply Setminus_Included.
             eapply Included_Union_l. 
             eapply Included_trans. eapply Setminus_Included.
             rewrite Union_commut. eapply add_global_funs_included_r. eassumption.
          -- eapply Disjoint_Included;[ | | eapply Hd ]; sets.
             eapply Included_trans;
               [| eapply fun_in_fundefs_bound_var_fundefs; now eapply find_def_correct; eauto ].
             rewrite !Union_assoc. now apply Included_Union_r.
          -- (* Fun_inv *)              
            eapply Fun_inv_from_GFun_inv; [ | eassumption | rewrite M.gss; reflexivity ].
            destruct Hadd1 as [[Ha1 Ha2] | [Ha1 Ha2]]; subst.
            ** inv Hadd2. sets. exfalso. eapply H. normalize_sets. reflexivity.
            ** exfalso. eapply Ha2. eassumption. now left.
          -- eassumption.
          -- do 2 eexists. split; [| split; [| constructor ]]. rewrite M.gss. reflexivity.
             eauto.
          -- destruct Hadd1 as [ [Heq He2] | [Heq1 He2] ]; subst.
             eapply Closure_conversion_tag_inv. eassumption.
             exfalso. eapply He2. eassumption. now left.
    - split. intros f v Hnin Hin Hget. now inv Hin.
      inv Hcc'. simpl. eapply GFun_inv_antimon.
      eassumption. 
      eapply Included_trans. eapply is_gfuns_included_r; eauto; tci.
      sets.
  Qed.

  
  (** Correctness of [project_var] *)
  Lemma project_var_correct k rho1 rho2 rho2' Scope GFuns Funs σ c Γ FVs x x' C S S'  :
    project_var clo_tag Scope Funs GFuns σ c Γ FVs S x x' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ])))  ->
    ~ In _ S' x' /\
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x'.
  Proof.
    intros Hproj Hcc Hfun Hgfun Henv Hctx Hd.
    inv Hproj.
    - inv Hctx. repeat split; eauto. intros Hc. eapply Hd; eauto.
    - inv Hctx. inv H9.
      repeat split; eauto.
      + intros Hc. inv Hc. eauto.
      + eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. eauto.
      + (* TODO : make lemma *) 
        intros f v Hnin Hin Hget.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        subst. repeat eexists; eauto.
        rewrite M.gso; [ eassumption | now intros Heq; subst; eapply Hd; eauto ].
        rewrite M.gso. eassumption. 
        intros Hc. subst; eapply Hd; constructor; eauto. right; left.
        eexists. split; eauto. left. constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto. right; left.
        eapply image_monotonic; eauto. sets. 
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]]; eauto.
        simpl in H8. rewrite Hget2 in H8; inv H8.
        rewrite Hget1 in H3; inv H3. eassumption.
    - inv Hctx. inv H11. inv H10. inv H13. repeat split. 
      + intros Hc. inv Hc. eapply H4; eauto.
      + eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_set_not_in_P_r. eassumption.
        intros Hc. eapply Hd. constructor. eapply H3. now sets. 
        intros Hc. eapply Hd. constructor. eapply H2. now sets.
      + eapply Fun_inv_set_not_In_Funs_r_not_Γ.
        intros Hc. eapply Hd. constructor; eauto. right. left. eapply image_monotonic; eauto. now sets.
        intros Hc. subst. eapply Hd; eauto.
        eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | eassumption ].
        intros Hc. subst. eapply Hd; eauto. constructor.
        now eapply H3. right. left. eapply image_monotonic; eauto.  sets.
        intros Hc1. subst. eapply Hd; eauto. constructor. eapply H3. sets.
      + intros f v c1 Hin Hget.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Heq2 [Hget2 Happrox]]]]]]]]]; eauto.
        simpl in H12.
        subst. repeat eexists; eauto.
        rewrite M.gso. 2:{ intros Heq; subst. eapply Hd. constructor; eauto. right. left. 
                           eapply In_image. sets. }
        rewrite M.gso. eassumption.  
        intros Hc. subst; eapply Hd; constructor. eapply H3. right; left.
        eexists. split; [| now eauto ]. now sets. 
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eapply FV_inv_set_r. intros Heq; subst; eapply Hd; eauto. constructor. 
        eapply H3. now sets. eassumption. 
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Hgfun as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [Hget1 [Heq2 [Hget2 Happrox]]]]]]]]]; eauto.
        subst. simpl in H12.
        rewrite !M.gss, !M.gso in H12. rewrite Hget2 in H12. inv H12.
        eassumption. intros Hc. subst. eapply Hd. constructor.
        eapply H3; eauto. right. left. eapply In_image. now sets.
    - inv Hctx. inv H13.
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
        eexists. split; [| now eauto ]. left; constructor; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eassumption ].
        intros Hc. eapply Hd; constructor; eauto. right; left.
        eapply image_monotonic; eauto. sets.
      + eapply FV_inv_set_r. now intros Heq; subst; eapply Hd; eauto.
        eassumption.
      + intros v' Hget. eexists. rewrite M.gss. split; eauto.
        edestruct Henv as [g [ce [Hgetg [Hc Hinv]]]].
        repeat subst_exp. eapply Forall2_nthN' in Hinv; eauto. 
  Qed.
  
  (** Correctness of [project_vars] *)
  Lemma project_vars_correct k rho1 rho2 rho2'
        Scope Funs GFuns σ c Γ FVs xs xs' C S S' :
    project_vars clo_tag Scope Funs GFuns σ c Γ FVs S xs xs' C S' ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2 ->
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->        
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->   
    ctx_to_rho C rho2 rho2' ->
    Disjoint _ S (Scope :|: (image σ ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs /\
    (forall vs,
       get_list xs rho1 = Some vs ->
       exists vs', get_list xs' rho2' = Some vs' /\
              Forall2 (cc_approx_val pr cenv clo_tag k boundG) vs vs').
  Proof.
    revert k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S.
    induction xs;
      intros k rho1 rho2 rho2' Scope Funs Γ FVs xs' C S Hproj Hcc Hfun Hgfuns Henv Hctx Hd.
    - inv Hproj. inv Hctx. repeat split; eauto. 
      eexists. split. reflexivity. 
      inv H. now constructor. 
    - inv Hproj.
      edestruct ctx_to_rho_comp_ctx_l as [rho'' [Hctx1 Hctx2]]; eauto.
      rewrite <- comp_ctx_f_correct. reflexivity.
      eapply project_var_correct in Hctx1; eauto.
      destruct Hctx1 as [Hnin [Hcc1 [Hfun1 [Hgfun1 [Henv1 Hcc_var]]]]].
      edestruct IHxs as [Hcc2 [Hfun2 [Hgfun2 [Henv2 Hyp]]]]; eauto. 
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included; eassumption.
      repeat split; eauto. intros vs Hget. 
      simpl in Hget. destruct (M.get a rho1) eqn:Hget'; try discriminate. 
      destruct (get_list xs rho1) eqn:Hget_list; try discriminate.
      inv Hget. edestruct Hyp as [vs' [Hget_list' Hall]]; [ reflexivity |].
      edestruct Hcc_var as [v' [Hget''' Hcc''']]; eauto.
      eexists. split; eauto. simpl. rewrite Hget_list'. 
      erewrite <- project_vars_get; eauto. rewrite Hget'''. reflexivity.
  Qed.
  

  (** Correctness of [make_closures] *)
  Lemma make_closures_correct k rho1 rho2 rho2' B S Γ' C σ S' Scope Funs GFuns FVs c Γ :
    make_closures clo_tag B S Γ' C σ S' ->

    unique_functions B ->   
    ~ In _ (name_in_fundefs B) Γ ->
    ~ In _ (name_in_fundefs B) Γ' ->
    Included _ (name_in_fundefs B) Scope ->
    Disjoint _ S (name_in_fundefs B) ->
    Disjoint _ (image σ GFuns) (name_in_fundefs B) ->

    cc_approx_env_P pr cenv clo_tag (Setminus _ Scope (name_in_fundefs B)) k boundG rho1 rho2 ->
    
    Fun_inv k rho1 rho2 Scope Funs σ Γ ->
    GFun_inv k rho1 rho2 Scope GFuns σ ->  
    Fun_inv k rho1 rho2 (Empty_set _) (name_in_fundefs B) σ Γ' ->
    GFun_inv k rho1 rho2 (Empty_set _) GFuns σ ->
    FV_inv k rho1 rho2 Scope Funs GFuns c Γ FVs ->
    
    ctx_to_rho C rho2 rho2' ->
    
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho1 rho2' /\
    Fun_inv k rho1 rho2' Scope Funs σ Γ /\
    GFun_inv k rho1 rho2' Scope GFuns σ /\
    FV_inv k rho1 rho2' Scope Funs GFuns c Γ FVs.
  Proof.
    intros Hmake. revert k rho1 rho2 rho2' Scope Funs GFuns FVs Γ.
    induction Hmake;
      intros k rho1 rho2 rho2' Scope Funs GFuns FVs Γ1 Hun Hnin1 Hnin2
             Hsub Hd Hd' Hcc Hfun HGfun Hfun' HGfun' Henv Hctx.
    - inv Hctx. repeat split; eauto. simpl in Hcc.
      eapply cc_approx_env_P_antimon; eauto. sets.
    - eapply ctx_to_rho_comp_ctx_l in Hctx; [| apply Constr_cc; constructor ].
      destruct Hctx as [rho2'' [Hctx1 Hctx2]].
      inv Hctx1. inv H7. inv Hun.
      edestruct IHHmake with (Scope := Scope) (GFuns := GFuns)
        as [Hcc1 [Hfun1 [Hgfun1 Henv1]]];
        [ eassumption | | | | | | | | | | | | eassumption | ]. 
      + intros Hc. eapply Hnin1. right. now apply Hc. 
      + intros Hc. eapply Hnin2. right. now apply Hc.
      + eapply Included_trans; [| eassumption ]. sets.
      + sets. 
      + eapply Disjoint_Included; [| | eapply Hd' ]. sets. sets.
      + eapply cc_approx_env_P_antimon;
          [| now apply (@Included_Union_Setminus _ _ (Singleton var f) _) ]. 
        eapply cc_approx_env_P_union.
        eapply cc_approx_env_P_set_not_in_P_r.
        eapply cc_approx_env_P_antimon. eassumption.
        simpl. now sets. intros Hc. inv Hc; eauto.
        intros x Hin v Hget. inv Hin.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
          [| | eassumption |]. now apply not_In_Empty_set. now left.
        eexists. split. now rewrite M.gss. subst.
        simpl in H6. rewrite Hget1, Hget2 in H6. inv H6.
        eassumption.
      + eapply Fun_inv_set_In_Scope_r_not_Γ ; [| | eassumption ].
        * eapply Hsub. now left.
        * intros Hc; subst. eapply Hnin1. left; eauto.
      + eapply GFun_inv_set_not_In_GFuns_r; [| eapply GFun_inv_antimon; try eassumption ]; simpl; sets.
        intros Hc; subst. eapply Hd'. constructor; eauto.
        now left.
      + intros f'' v Hnin Hin Hget.
        edestruct Hfun' as
            [vs' [rho3 [B3 [f3 [rho4 [B4 [f4 [Hget1 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]]]];
          [| | eassumption |]. now apply not_In_Empty_set. now right.
        subst. repeat eexists; eauto. 
        rewrite M.gso. eassumption. 
        intros Hc; subst. eapply Hnin2. now left; eauto.
        rewrite M.gso. eassumption.
        intros Hc; subst.
        eapply make_closures_image_Included in Hmake.
        eapply Hd. constructor; [| now left; eauto ].
        eapply Hmake. eexists; eauto.
      + intros f'' v Hnin Hin Hget. 
        edestruct HGfun' as
            [rho3 [B3 [f3 [rho4 [B4 [f4 [Heq2 [Ηnin2 [Hget2 Happrox]]]]]]]]];
          [| eassumption |]; eauto.
        repeat eexists; eauto.
        rewrite M.gso. eassumption. 
        intros Hc; subst. eapply Hd'. constructor.
        eapply In_image. eassumption. now left.
      + eapply FV_inv_set_r.
        intros Hc; subst. eapply Hnin1. left; eauto. eassumption.
      + repeat split; eauto.
  Qed. 
  

  (* TODO move *)

  Lemma mult_le_n n m :
    1 <= m ->
    n <= n * m.
  Proof.
    rewrite Nat.mul_comm.
    edestruct mult_O_le; eauto. omega.
  Qed.

  Lemma plus_le_mult  (a1 a2 b1 b2 b3 : nat) :
    b3 <= a1 ->
    1 <= b2 ->
    a2 <= b1 * b3 ->
    a1 + a2 <= (1 + b1) * a1 * b2.
  Proof.
    intros.
    rewrite <- mult_assoc, NPeano.Nat.mul_add_distr_r.
    eapply plus_le_compat.
    - simpl. rewrite <- plus_n_O.
      now eapply mult_le_n.
    - eapply le_trans. eapply le_trans. eassumption.
      eapply mult_le_compat. eauto. eassumption.
      rewrite mult_assoc. eapply mult_le_n. eassumption.
  Qed.
  
  Lemma Ecase_correct_upper_bound k rho1 rho2 rho2' C x x' c e e' l l' :
    ctx_to_rho C rho2 rho2' ->
    sizeOf_exp_ctx C <= 4 ->
    Forall2 (fun p1 p2 : ctor_tag * exp => fst p1 = fst p2) l l' ->
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x' ->
    cc_approx_exp pr cenv clo_tag k (upper_boundL k e rho1)
                  boundG (e, rho1) (e', rho2') ->
    cc_approx_exp pr cenv clo_tag k (upper_boundL k (Ecase x l) rho1)
                  boundG (Ecase x l, rho1) (C |[ Ecase x' l' ]|, rho2) ->
    cc_approx_exp pr cenv clo_tag k (upper_boundL k (Ecase x ((c, e) :: l)) rho1)
                  boundG (Ecase x ((c, e) :: l), rho1)
                  (C |[ Ecase x' ((c, e') :: l') ]|, rho2).
  Proof.
    intros Hctx Hleq Hall Henv Hcc1 Hcc2.
    eapply cc_approx_exp_rel_mon.
    pose (rhs := fun (n : nat) c1 =>
                   (8 * c1 * max_exp_env k (Ecase x ((c, e) :: l)) rho1 + n) + 8 * sizeOf_exp (Ecase x ((c, e) :: l))).
    { eapply ctx_to_rho_cc_approx_exp with
      (P := fun n c1 c2 => c2 + sizeOf_exp_ctx C <= rhs n c1)
        (P' := fun c1 c2 => c2 + sizeOf_exp_ctx C <= rhs 0 c1); try eassumption.
      - intros n1 n2. unfold rhs.  omega.
      - unfold rhs. intros c1 c2 n' c' H. omega.
      - eapply cc_approx_exp_case_cons_compat 
        with (S' := fun c1 c2 => c2 + sizeOf_exp_ctx C <=
                              8 * c1 * max_exp_env k (Ecase x l) rho1
                              + 8 * sizeOf_exp (Ecase x l)); try eassumption.
        + intros c1 c2 c' Hle. unfold upper_boundL, rhs. intros H.
          eapply le_trans with (m := 8  * c1 * max_exp_env k e rho1 + c' + 4
                                     + 8 * sizeOf_exp e).
          * omega.
          * rewrite <- plus_n_O. eapply plus_le_compat; [| simpl; omega ]. 
            ring_simplify. rewrite <- plus_assoc.
            eapply plus_le_compat. eapply mult_le_compat. eauto.
            now apply max_exp_env_Ecase_cons_hd.
            replace 8 with (1 + 7) by omega.
            eapply plus_le_mult; eauto.
            now eapply max_exp_env_grt_1. omega.
        + intros c1 c2 c' Hle. unfold rhs. intros H. ring_simplify.
          rewrite <- (plus_assoc _ _ (8 * _)).
          rewrite (plus_comm _ c'), <- plus_assoc. eapply plus_le_compat.
          * rewrite (mult_comm _ c'), <- mult_assoc.
            eapply mult_le_n. rewrite <- (Nat.mul_1_r 1).
            eapply NPeano.Nat.mul_le_mono. omega.
            now eapply max_exp_env_grt_1.
          * eapply le_trans; eauto.
            eapply plus_le_compat; [| simpl; omega ].
            eapply mult_le_compat; eauto. now apply max_exp_env_Ecase_cons_tl.
        + eapply cc_approx_exp_ctx_to_rho with
          (P' := fun n c1 c2 => c2 + sizeOf_exp_ctx C <=
                             8 * c1 * max_exp_env k (Ecase x l) rho1 +
                             8 * sizeOf_exp (Ecase x l)+ n); try eassumption.
          * intros n1 n2 H. omega.
          * intros c1 c2 c3 n Hlt. omega.
          * eapply cc_approx_exp_rel_mon. eassumption.
            intros n1 n2. unfold upper_boundL. omega. }
    intros c1 c2 H. unfold upper_boundL. omega.
  Qed.

  Lemma Ecase_correct_lower_bound k rho1 rho2 rho2' C x x' c e e' l l' :
    ctx_to_rho C rho2 rho2' ->
    sizeOf_exp_ctx C <= 4 ->
    Forall2 (fun p1 p2 : ctor_tag * exp => fst p1 = fst p2) l l' ->
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x' ->
    cc_approx_exp pr cenv clo_tag k lower_boundL
                  boundG (e, rho1) (e', rho2') ->
    cc_approx_exp pr cenv clo_tag k lower_boundL
                  boundG (Ecase x l, rho1) (C |[ Ecase x' l' ]|, rho2) ->
    cc_approx_exp pr cenv clo_tag k lower_boundL
                  boundG (Ecase x ((c, e) :: l), rho1)
                  (C |[ Ecase x' ((c, e') :: l') ]|, rho2).
  Proof.
    intros Hctx Hleq Hall Henv Hcc1 Hcc2.
    eapply cc_approx_exp_rel_mon.
    eapply ctx_to_rho_cc_approx_exp
    with (P := fun n c1 c2 => c1 + n <= c2 + sizeOf_exp_ctx C)
      (P' := fun c1 c2 => c1 <= c2 + sizeOf_exp_ctx C); try eassumption.
    - intros n c1 c2. simpl. omega.
    - intros c1 c2 n' c'. simpl. omega.
    - eapply cc_approx_exp_case_cons_compat
      with (S' := fun c1 c2 : nat => c1 <= c2 + sizeOf_exp_ctx C); try eassumption.
      + intros c1 c2 c'. unfold lower_boundL. simpl. omega.
        + intros c1 c2 c'. simpl. omega.
        + eapply cc_approx_exp_ctx_to_rho with
          (P' := fun n c1 c2 => c1 + n <= c2 + sizeOf_exp_ctx C); try eassumption.
          * intros c1 c2. simpl. omega.
          * intros c1 c2 c3 n Hlt. omega.
          * eapply cc_approx_exp_rel_mon. eassumption. intros c1 c2. unfold lower_boundL. omega.
    - intros c1 c2 c'. unfold lower_boundL. simpl. omega.
  Qed.

  Opaque mult.

  Corollary Ecase_correct k rho1 rho2 rho2' C x x' c e e' l l' :
    ctx_to_rho C rho2 rho2' ->
    sizeOf_exp_ctx C <= 4 ->
    Forall2 (fun p1 p2 : ctor_tag * exp => fst p1 = fst p2) l l' ->
    cc_approx_var_env pr cenv clo_tag k boundG rho1 rho2' x x' ->
    cc_approx_exp pr cenv clo_tag k (boundL k e rho1)
                  boundG (e, rho1) (e', rho2') ->
    cc_approx_exp pr cenv clo_tag k (boundL k (Ecase x l) rho1)
                  boundG (Ecase x l, rho1) (C |[ Ecase x' l' ]|, rho2) ->
    cc_approx_exp pr cenv clo_tag k (boundL k (Ecase x ((c, e) :: l)) rho1)
                  boundG (Ecase x ((c, e) :: l), rho1)
                  (C |[ Ecase x' ((c, e') :: l') ]|, rho2).
  Proof.
    intros. eapply cc_approx_exp_rel_conj.
    eapply Ecase_correct_lower_bound; eauto.
    eapply cc_approx_exp_rel_mon; eauto. now firstorder.
    eapply cc_approx_exp_rel_mon; eauto. now firstorder.
    eapply Ecase_correct_upper_bound; eauto.
    eapply cc_approx_exp_rel_mon; eauto. now firstorder.
    eapply cc_approx_exp_rel_mon; eauto. now firstorder.
  Qed.

  (* Axiom about prims. Currently assuming that they do not return functions *)
  Parameter primAxiom :
    forall f f' vs v k,
      M.get f pr = Some f' ->
      f' vs = Some v ->
      sizeOf_val k v = 0.
  

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct k rho rho' e e' Scope Funs GFuns σ c Γ FVs C :
    (* [Scope] invariant *)
    cc_approx_env_P pr cenv clo_tag Scope k boundG rho rho' ->
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e) rho ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain (Funs \\ Scope :|: GFuns) σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Funs \\ Scope :|: GFuns)) (bound_var e) ->
    (* [Fun] invariant *)
    Fun_inv k rho rho' Scope Funs σ Γ ->
    (* Free variables invariant *)
    FV_inv k rho rho' Scope Funs GFuns c Γ FVs ->
    (* Global functions invariant *)
    GFun_inv k rho rho' Scope GFuns σ ->
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs GFuns σ c Γ FVs e e' C ->
    cc_approx_exp pr cenv clo_tag k (boundL k e rho) boundG (e, rho) (C |[ e' ]|, rho').
  Proof with now eauto with Ensembles_DB.
    revert k e rho rho' e' Scope Funs GFuns σ c Γ FVs C.
    induction k as [k IHk] using lt_wf_rec1.
    induction e using exp_ind';
      intros rho1 rho2 e' Scope Funs GFuns σ c' Γ FVs C Happrox Hnin HFVs Hun Hinj Hd Hfun Hgfun Henv Hcc.
    - (* Case Econstr *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4*length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).
      pose (P :=
              fun n c1 c2 : nat =>
                c1 + n <= c2 + sizeOf_exp_ctx C <= 8 * c1 * max_exp_env k e rho1
                                                 + 8 * sizeOf_exp e + n).
      eapply cc_approx_exp_rel_mon with (P1 := P (sizeOf_exp_ctx C)).
      { intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
        edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
        edestruct project_vars_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
        edestruct Hvar as [v' [Hget' Happ']]; eauto.
        eapply ctx_to_rho_cc_approx_exp with (P' := P 0); eauto.
        - now firstorder.
        - clear. now firstorder.
        - eapply cc_approx_exp_constr_compat with (S0 := boundL k e rho1).
          + eapply Forall2_cc_approx_var_env; eauto.
          + unfold boundL, upper_boundL, lower_boundL, P. intros c1 c2 n Hle.
            rewrite <- !plus_n_O. intros [Hle1 Hle2]; split; try omega.
            ring_simplify. rewrite <- !plus_assoc, (plus_comm c2).
            eapply plus_le_compat; eauto. eapply plus_le_mult; eauto.
            now apply max_exp_env_grt_1. eapply le_trans. eassumption.
            omega.
          + intros vs1 vs2 Hget Hall.
            unfold boundL, upper_boundL, lower_boundL, max_exp_env.
            erewrite <- sizeOf_env_set_constr; eauto.
            eapply IHe; [ | | | | | | | | | eassumption ].
            * eapply cc_approx_env_P_extend with (v2 := Vconstr t vs2).
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              rewrite cc_approx_val_eq. constructor; eauto.
              now eapply Forall2_Forall2_asym_included.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Econstr_Included. 
            * intros f Hfin. eauto.
            * eapply injective_subdomain_antimon; eauto. sets. 
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              intros Heq; subst. now eauto.
              eapply Fun_inv_mon; [ | now eauto ]. 
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              now intros Hc; inv Hc; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor.
              rewrite image_Union. right. eapply image_monotonic; eauto...
              normalize_bound_var... sets.
              eapply GFun_inv_Scope_extend; sets.
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
              eapply GFun_inv_antimon; sets. } 
      { intros c1 c2. unfold P, boundL, lower_boundL, upper_boundL.
        intros [Hle1 Hle2]; split; try omega.
        eapply le_trans;
          [| eapply plus_le_compat_r; eapply mult_le_compat_l; now apply max_exp_env_Econstr ].
        simpl. omega. }
    - (* Case [Ecase x []] *)
      inv Hcc. inv H12.
      intros v1 c1 Hleq Hstep. inv Hstep. inv H5. 
    - (* Case [Ecase x ((c, p) :: pats] *)
      inv Hcc.
      inversion H12 as [ | [c1 p1] [c2 p2] l1 l2 [Heq [C' [e' [Heq' Hcc]]]] Hall ];
        simpl in Heq, Heq'; subst.
      repeat normalize_bound_var_in_ctx.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
      edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
      eapply Disjoint_Included_r; [| eassumption ]. sets.
      now eauto 10 with Ensembles_DB functions_BD.   
      edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
      edestruct Hvar as [Hget' Happ']; eauto. 
      eapply Ecase_correct; try eassumption.
      + inv H12. eapply Forall2_monotonic; try eassumption.
        firstorder.
      + eapply IHe; try eassumption.
        * now intros Hc; eapply Hnin; eauto.
        * eapply binding_in_map_antimon; [|  eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * intros f Hfin. eapply Hun.
          econstructor. eassumption. now constructor.
        * eauto with Ensembles_DB.
      + eapply IHe0; try eassumption.
        * now eauto.
        * eapply binding_in_map_antimon; [| eassumption ].
          intros x Hin. inv Hin; eauto.
        * intros f Hfin. eapply Hun. inv Hfin. 
          econstructor; eauto. constructor 2. eassumption.
        * eauto with Ensembles_DB.
        * econstructor; eauto.
    - (* Case Eproj *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 4) by (eapply project_var_sizeOf_ctx_exp; eauto).
      pose (P :=
              fun n c1 c2 : nat =>
                c1 + n <= c2 + sizeOf_exp_ctx C <= 8 * c1 * max_exp_env k e rho1
                                                 + 8 * sizeOf_exp e + n).
      eapply cc_approx_exp_rel_mon with (P1 := P (sizeOf_exp_ctx C)).
      { intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
        edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
        now eauto 10 with Ensembles_DB functions_BD.   
        edestruct project_var_correct as [Happ [Hfun' [Hgfun' [Henv' Hvar]]]]; eauto.
        edestruct Hvar as [Hget' Happ']; eauto.
        eapply ctx_to_rho_cc_approx_exp with (P' := P 0); eauto.
        - now firstorder.
        - clear; now firstorder.
        - eapply cc_approx_exp_proj_compat with (S0 := boundL k e rho1).
          + eassumption.
          + unfold boundL, upper_boundL, lower_boundL, P. intros c1 c2.
            rewrite <- !plus_n_O. intros [Hle1 Hle2]; split; try omega.
            ring_simplify.  rewrite <- !plus_assoc.
            rewrite (plus_comm _ (8 * _)), (plus_assoc _ (8 * _)).
            eapply plus_le_compat; eauto.
            eapply le_trans with (m := 5). omega.
            specialize (max_exp_env_grt_1 k e rho1). omega.
          + intros v1' v2' c1 vs1 Hget Hin Hv.
            unfold boundL, lower_boundL, upper_boundL, max_exp_env.
            erewrite <- sizeOf_env_set_proj; eauto.
            eapply IHe; [ | | | | | | | | | eassumption ].
            * eapply cc_approx_env_P_extend.
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              eassumption.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Eproj_Included. 
            * intros f Hfin. eauto.
            * eapply injective_subdomain_antimon; eauto; sets.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              intros Heq; subst. now eauto.
              eapply Fun_inv_mon; [ | now eauto ].
              eapply Disjoint_Included; [ | | now apply Hd ].
              normalize_bound_var... sets.
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope_GFuns.
            * eapply GFun_inv_set_not_In_GFuns_l.
              now intros Hc; inv Hc; eauto.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply Hd. constructor.
              rewrite image_Union. right. eapply image_monotonic; eauto...
              normalize_bound_var... sets.
              eapply GFun_inv_Scope_extend; sets.
              eapply Disjoint_Included; [| | now eapply Hd ].
              normalize_bound_var... sets. 
              eapply GFun_inv_antimon; sets. } 
      { intros c1 c2. unfold P, boundL, lower_boundL, upper_boundL.
        intros [Hle1 Hle2]; split; try omega.
        eapply le_trans; [| eapply plus_le_compat_r; eapply mult_le_compat_l; now apply max_exp_env_Eproj ].
        simpl. omega. }
    - (* Case letapp *)
      admit. 
    - (* Case Efun -- the hardest one! *)
      inv Hcc.
      assert (Hsub : FromList FVs' \subset occurs_free_fundefs f2).
      { rewrite <- H1... } 
      specialize (occurs_free_fundefs_cardinality _ _ Hsub H2); intros Hlen.
      assert (Ha : exists vs, get_list FVs' rho1 = Some vs).
      { eapply In_get_list. intros x Hin. eapply HFVs.
        rewrite occurs_free_Efun. left. eauto. }
      destruct Ha as [vs Hget_list].
      (* sizes of evaluation contexts *)
      assert(HC1 : sizeOf_exp_ctx C' <= 4 * sizeOf_fundefs f2)
        by (eapply le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | omega ]).
      assert (HC2 : sizeOf_exp_ctx C0 <= 3 * numOf_fundefs f2)
        by (eapply make_closures_sizeOf_ctx_exp; eauto).
      pose (P1 :=
              fun m n c1 c2 : nat => 
                c1 + n <= c2 + sizeOf_exp_ctx C' <= 8 * c1 * max_exp_env k (Efun f2 e) rho1
                                                  + m * sizeOf_fundefs f2 + 8 * sizeOf_exp e + 8
                                                  + n).
      pose (P2 :=
              fun m n c1 c2 : nat => 
                c1 + n <= c2 + sizeOf_exp_ctx C0 <= 8 * c1 * max_exp_env k (Efun f2 e) rho1
                                                  + m * sizeOf_fundefs f2 + 8 * sizeOf_exp e + 7
                                                  + n).
      eapply cc_approx_exp_rel_mon with (P1 := P1 8 (sizeOf_exp_ctx C'));
        [| intros c1 c2; unfold P1, boundL, lower_boundL, upper_boundL;
           intros [Hle1 Hle2]; split; simpl; omega ].
      intros v1 c1 Hleq Hstep.
      edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; [ | eassumption | | | | | ]; eauto.
      edestruct project_vars_correct as [Happ [Hfun' [Henv' [Hgfun' Hvar]]]]; eauto.
      edestruct Hvar as [v' [Hget' Happ']]; eauto. rewrite <- app_ctx_f_fuse. simpl.
      eapply ctx_to_rho_cc_approx_exp with (P' := P1 8 0);
        try eassumption;
        try now (intros n1 n2; unfold P1; intros; simpl; omega).
      assert (Hfuns : Fun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
                              (Empty_set var) (name_in_fundefs f2) σ Γ' /\
                      GFun_inv k (def_funs f2 f2 rho1 rho1) (def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2')) (Empty_set _) GFuns' σ
             ).
      { eapply Closure_conversion_fundefs_correct with (c := c'0) ; eauto.
        * intros f Hfin. inv Hfin; eauto.
        * intros f Hfin. inv Hfin; eauto.
        * eapply binding_in_map_antimon; [| eassumption ].
          intros x H. eapply Free_Efun2. eassumption.
        * eapply GFun_inv_set_not_In_GFuns_r.
          intros Hc. eapply H5. constructor; eauto. rewrite image_Union. sets.
          eapply GFun_inv_Scope. sets. eassumption.
        * eapply add_global_funs_is_gfuns. eassumption.
        * eapply Disjoint_Included_l.
          eapply image_monotonic. eapply Included_Union_compat. reflexivity.
          eapply add_global_funs_included_r. eassumption.
          rewrite Union_Same_set; sets. rewrite image_Union.
          eapply Union_Disjoint_l. repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included; [ | | eapply Hd ]; sets.
          eapply Disjoint_Included; [ | | eapply H7 ]; sets. normalize_bound_var...
          eapply Included_trans;  [ eapply make_closures_image_Included; eassumption |]...                
        * now apply Disjoint_Empty_set_r.
        * eapply closure_conversion_fundefs_Same_set_image. eassumption.
        * eapply make_closures_injective; [| | |  eassumption].
          eapply Disjoint_Included_r; [| eassumption ]. normalize_bound_var.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
          eapply Disjoint_Included_r; [| eassumption ]. rewrite image_Union. sets.
          eapply injective_subdomain_antimon. eassumption. sets. 
        * eapply make_closures_injective; [| | |  eassumption].
          eapply Disjoint_Included_r; [| eassumption ]. normalize_bound_var.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
          eapply Disjoint_Included_r; [| eassumption ]. rewrite image_Union. sets.
          eapply injective_subdomain_antimon. eassumption. sets. 
        * intros Hc. eapply H5. constructor; eauto. rewrite image_Union.
          inv Hc; now eauto.
        * intros Hc. eapply H5. now eauto.
        * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
          eapply H7. constructor.
          eapply make_closures_image_Included. eassumption.
          eassumption. now eauto.
        * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
          eapply H7. constructor.
          eapply make_closures_image_Included. eassumption.
          eassumption. now eauto.
        * edestruct Hvar as [vs' [Hget_list' Hall]]; eauto.
          eapply FV_inv_Forall2. eassumption. rewrite M.gss. reflexivity.
          eassumption. }
      assert (Hsuf :
                cc_approx_exp pr cenv clo_tag k (P2 3 (sizeOf_exp_ctx C0))  boundG (e, def_funs f2 f2 rho1 rho1)
                              (C0 |[ Ce |[ e'0 ]| ]|, def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2')
                                                   (M.set Γ' (Vconstr c'0 v') rho2'))).
      { edestruct make_closures_ctx_to_rho
          with (rho2 := def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2') (M.set Γ' (Vconstr c'0 v') rho2'))
          as [rho2'' Htp_rho']; eauto.
        - eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_preserv_l. normalize_bound_var.
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs. sets.
        - intros Hc. eapply H5. now eauto. 
        - eapply Closure_conversion_fundefs_correct; try eassumption; eauto.
          + intros f Hfin. inv Hfin; eauto.
          + intros f Hfin. inv Hfin; eauto.
          + eapply binding_in_map_antimon; [| eassumption ].
            intros x H. eapply Free_Efun2. eassumption.
          + eapply GFun_inv_set_not_In_GFuns_r.
            intros Hc. eapply H5. constructor; eauto.
            do 2 right. left; eauto. rewrite image_Union...
            eapply GFun_inv_Scope; eauto. sets.
          + eapply add_global_funs_is_gfuns. eassumption.
          + eapply Disjoint_Included_l. 
            eapply make_closures_image_set; try eassumption.
            eapply Union_Disjoint_l.
            * eapply Disjoint_Included; [ | | eapply Hd ].
              normalize_bound_var... 
              rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
              eapply image_monotonic. eapply Setminus_Included_Included_Union.
              eapply Included_trans. eapply add_global_funs_included_r; eauto; tci. sets.
            * eapply Disjoint_Included; [ | | eapply H7 ]. normalize_bound_var...
              sets. 
          + now apply Disjoint_Empty_set_r. 
          + eapply closure_conversion_fundefs_Same_set_image. eassumption.
          + eapply make_closures_injective; try eassumption.
            eapply Disjoint_Included_r; [| eassumption ].
            eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
            normalize_bound_var...
            eapply Disjoint_Included_r; [| eassumption ].
            now eauto 20 with Ensembles_DB functions_BD.
            eapply injective_subdomain_antimon. eassumption. sets.
          + eapply make_closures_injective; try eassumption.
            eapply Disjoint_Included_r; [| eassumption ].
            eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
            normalize_bound_var...
            eapply Disjoint_Included_r; [| eassumption ].
            now eauto 20 with Ensembles_DB functions_BD.
            eapply injective_subdomain_antimon. eassumption. sets.
          + intros Hc. eapply H5. constructor; eauto. rewrite image_Union. sets.
            inv Hc; eauto.
          + intros Hc; eauto. eapply H5. constructor; eauto. 
          + intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H7. constructor; [| now eauto ].
            eapply make_closures_image_Included. eassumption. eassumption.
          + intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
            eapply H7. constructor; [| now eauto ].
            eapply make_closures_image_Included. eassumption. eassumption.
          + edestruct Hvar as [vs' [Hget_list' Hall]]; eauto.
            eapply FV_inv_Forall2. eassumption. rewrite M.gss. reflexivity.
            eassumption.
        - intros f Hin. eapply binding_in_map_def_funs. eapply HFVs. eauto.
        - edestruct make_closures_correct with
          (Scope := Union var (name_in_fundefs f2) Scope)
            (Γ := Γ)
            (rho1 := def_funs f2 f2 rho1 rho1)
            (rho2 := def_funs B' B' (M.set Γ' (Vconstr c'0 v') rho2')
                              (M.set Γ' (Vconstr c'0 v') rho2'))
            (GFuns := GFuns') (Funs := Funs)
            as [Hcc'' [Hfun'' [Hgfun''  Henv'']]]. 
          + eauto.
          + eauto.
          + intros Hc. eapply Hnin. constructor.
            now eapply name_in_fundefs_bound_var_fundefs.
          + intros Hc. eapply H5. now eauto.
          + eapply Included_Union_l.
          + eapply Disjoint_Included_r; [| eassumption ].
            eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
            normalize_bound_var...
          + eapply Disjoint_Included_l. eapply image_monotonic. eapply add_global_funs_included_r. eassumption.
            rewrite image_Union. rewrite make_closures_image_eq; eauto.
            eapply Union_Disjoint_l. 
            eapply Disjoint_Included; [| | eapply Hd ].
            eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
            normalize_bound_var... sets.
            eapply Disjoint_Included; [| | eapply H7 ].
            eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
            normalize_bound_var... sets. 
          + eapply cc_approx_env_P_def_funs_not_In_P_l.
            now eauto with Ensembles_DB.
            eapply cc_approx_env_P_def_funs_not_In_P_r.
            erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); [| eassumption ].
            eapply Disjoint_Included_r.
            now eapply make_closures_image_Included; eauto.
            rewrite Setminus_Union_distr. now eauto 7 with Ensembles_DB.
            eapply cc_approx_env_P_set_not_in_P_r.
            eapply cc_approx_env_P_antimon; [ eassumption |].
            now sets.
            intros Hin. inv Hin. inv H. eauto. eapply H5. eauto.
          + repeat normalize_bound_var_in_ctx. eapply Fun_inv_def_funs.
            * intros Hc. erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
              eapply H7. constructor.
              eapply make_closures_image_Included. eassumption. eassumption.
              rewrite !Union_assoc...
            * intros Hc. eapply Hnin. eapply Included_Union_l.
              now apply name_in_fundefs_bound_var_fundefs.
            * eapply Disjoint_Included; [| | now eapply Hd ]; sets.              
              apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
            * erewrite <- closure_conversion_fundefs_Same_set_image; [| eassumption ].
              eapply Disjoint_Included_r;
                [ eapply make_closures_image_Included; eassumption |].
              eapply Disjoint_sym. eapply Disjoint_Included; [| | now eapply H7 ]; sets.
              rewrite image_Union...
            * eapply Fun_inv_set_not_In_Funs_r_not_Γ; [| | ].
              intros Hc. eapply H5. constructor; eauto.
              right. right. left. rewrite image_Union. left. eassumption.
              intros Hc. subst. eapply H5. constructor. now eauto.
              now eauto. now eauto.
          + eapply GFun_inv_fuse with (names := name_in_fundefs f2); tci. 
            * eapply GFun_inv_Scope_extend.
              eapply Disjoint_Included; [| | now eapply Hd ]; sets.              
              normalize_bound_var. apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
              eapply GFun_inv_def_funs_not_In_GFuns_r.
              erewrite <- closure_conversion_fundefs_Same_set_image with (B2 := B'); eauto.
              rewrite make_closures_image_eq; eauto.
              eapply Disjoint_sym. eapply Disjoint_Included; [| | now eapply H7 ]; sets.
              rewrite image_Union. now eauto 20 with Ensembles_DB.
              eapply GFun_inv_def_funs_not_In_GFuns_l. sets.
              eapply GFun_inv_set_not_In_GFuns_r.
              intros Hc. eapply H5. constructor; eauto. rewrite image_Union.
              do 2 right. left. right. eapply image_monotonic; [| eassumption ]; sets.
              eapply GFun_inv_antimon. eassumption. sets.
            * destruct Hfuns as [Hf Hg]. eassumption.
            * sets.
            * rewrite make_closures_image_eq; eauto.
              eapply Disjoint_sym.
              eapply Disjoint_Included; [| | now eapply H7 ]; sets.
              normalize_bound_var. eapply Union_Included; sets.
              do 2 apply Included_Union_preserv_l. now apply name_in_fundefs_bound_var_fundefs.
          + destruct Hfuns as [Hf Hg]. eassumption.
          + destruct Hfuns as [Hf Hg]. eassumption.
          + eapply FV_inv_antimonotonic_add_global_funs; [ | | eassumption | ]; tci.
            eapply FV_inv_def_funs.
            * intros Hc. eapply Hnin. constructor. 
              now eapply name_in_fundefs_bound_var_fundefs.
            * intros Hc.
              erewrite <- closure_conversion_fundefs_Same_set_image in Hc; [| eassumption ].
              eapply H7. constructor.
              eapply make_closures_image_Included. eassumption. eassumption.
              rewrite !Union_assoc. now apply Included_Union_r.
            * eapply FV_inv_set_r.
              intros Hc. subst. eapply H5. constructor; eauto.
              eassumption.
            * sets.
          + eauto.
          + eapply ctx_to_rho_cc_approx_exp with (P' := P2 3 0);
            try eassumption;
            try now (intros n1 n2; unfold P2; intros; simpl; omega). 
            eapply cc_approx_exp_rel_mon; [ eapply IHe with (GFuns := GFuns'); eauto |]. 
            * eapply binding_in_map_antimon.
              eapply Included_trans. now eapply occurs_free_Efun_Included.
              rewrite Union_commut. now apply Included_refl.
              apply binding_in_map_def_funs. eassumption.
            * intros f Hfin; eauto.
            * eapply injective_subdomain_antimon.
              eapply make_closures_injective; try eassumption. 
              eapply Disjoint_Included_r; [| eassumption ]. 
              eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
              normalize_bound_var...
              eapply Disjoint_Included_r; [| eassumption ].
              now eauto 20 with Ensembles_DB functions_BD.
              eapply Union_Included; sets. eapply Included_trans.
              eapply add_global_funs_included_r. eassumption. sets.
            * rewrite image_Union. eapply Union_Disjoint_l.
              eapply Disjoint_Included; [| | eapply Hd ]. normalize_bound_var...
              sets.  
              eapply Disjoint_Included_l. eapply image_monotonic. eapply add_global_funs_included_r.
              eassumption. rewrite image_Union. rewrite make_closures_image_eq; eauto.
              eapply Union_Disjoint_l.
              eapply Disjoint_Included; [| | eapply Hd ]; sets. normalize_bound_var...
              eapply Disjoint_Included; [| | eapply H7 ]; sets. normalize_bound_var...
            * intros n1 n2; unfold boundL, lower_boundL, upper_boundL, P2.
              rewrite <- !plus_n_O. intros [Hle1 Hle2]; split; try omega.
              eapply le_trans. eapply plus_le_compat. eassumption.
              eapply le_trans. eassumption. eapply mult_le_compat_l.
              now apply numOf_fundefs_le_sizeOf_fundefs.
              eapply le_trans. do 2 eapply plus_le_compat_r.
              eapply mult_le_compat_l. now eapply max_exp_env_Efun.
              omega. }
      intros v1' c1' Hleq' Hstep'. inv Hstep'.
      edestruct Hsuf as [v2' [c2' [Hstep2' [[Hle1 Hle2] Hcc2']]]]; [| eassumption |]; eauto.
      assert (Hadm : length FVs' = length FVs'').
      {  do 2 (erewrite get_list_length_eq; [| eassumption ]).
         eapply Forall2_length. eassumption. }
      assert (Hadm' : numOf_fundefs f2 = numOf_fundefs B')
        by (eapply Closure_conversion_fundefs_numOf_fundefs; eauto).
      do 2 eexists. split; [| split ].
      econstructor; eauto. econstructor; eauto.
      unfold P1 in Hle1, Hle2. split; omega. 
      eapply cc_approx_val_monotonic; try eassumption. omega.
    - (* Case Eapp *)
      inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 3 * length l + 3)
        by (eapply le_trans; [ now eapply project_vars_sizeOf_ctx_exp; eauto | simpl; omega ]).
      pose (P :=
              fun n c1 c2 : nat =>
                c1 + n <= c2 + sizeOf_exp_ctx C <= 7 * c1 * max_exp_env k (Eapp v t l) rho1
                                                 + 7 * sizeOf_exp (Eapp v t l) 
                                                 + n).
      eapply cc_approx_exp_rel_mon with (P1 := P (sizeOf_exp_ctx C));
        [| intros n1 n2; unfold P, boundL, upper_boundL, lower_boundL; simpl; omega ].
      { intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep); inv Hstep'.
        edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
        simpl. rewrite H4, H5. reflexivity.
        edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
        edestruct Hvar as [v' [Hget' Happ']]; eauto.
        simpl. rewrite H4, H5. reflexivity.
        simpl in Hget'. destruct (M.get f' rho2') eqn:Hgetf'; try discriminate.
        destruct (get_list ys' rho2') eqn:Hget_list'; try discriminate. inv Hget'.
        inv Happ'. rewrite cc_approx_val_eq in H6. destruct v0; try contradiction.
        eapply ctx_to_rho_cc_approx_exp with (P' := P 0);
          [ now firstorder
          | now (intros n1 n2; simpl; unfold P; intros; omega) | | | | ]; try eassumption.
        intros v1' c1' Hleq' Hstep'. inv Hstep'.
        rewrite H4 in H8. inv H8. rewrite H5 in H15; inv H15.
        destruct l1; try contradiction. destruct v0, l1; try contradiction.
        destruct v2; try contradiction. 
        rewrite H17 in H7. inv H7. 
        rewrite H11 in H20. inv H20. eapply bstep_cost_deterministic in H21.
        2:eapply H12. inv H21.
        assert (Hlen := List_util.Forall2_length _ _ _ H9).
        edestruct H6 with (vs2 := l0) (j := k - 1)
          as [Γ' [xs2 [e2 [rho2'' [Heq [Hfind [Hset Hyp]]]]]]]; eauto.
        edestruct Hyp with (c1:=c1) as [v2' [c'2 [Hstep2 [[Hle1 Hle2] Hcc']]]]; try eassumption.
        - omega.
        - eapply List_util.Forall2_monotonic; [| eassumption ].
          intros. eapply cc_approx_val_monotonic. eassumption. omega.
        - omega.          
        - subst.
          assert (Heq: length ys' = length l).
          { symmetry. do 2 (erewrite get_list_length_eq; [| eassumption ]).
            eapply Forall2_length. eassumption. }
          repeat eexists.
          + econstructor. eassumption. reflexivity.
            econstructor. rewrite M.gso. eassumption.
            intros Hc; subst. eapply project_vars_not_In_free_set; [ now eauto | now eauto | ].
            constructor. now eapply H10. rewrite FromList_cons. now eauto.
            reflexivity.
            eapply BStepc_app. rewrite M.gso. rewrite M.gss. reflexivity.
            now eauto.
            simpl. rewrite M.gss. rewrite get_list_set_neq. rewrite get_list_set_neq.
            rewrite Hget_list'. reflexivity. 
            intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption. 
            constructor. eapply H10. rewrite FromList_cons. now eauto.
            intros Hin. eapply project_vars_not_In_free_set. eassumption. eassumption.
            constructor. now eauto. rewrite FromList_cons. now eauto.
            eassumption. simpl in Hset. eauto. eassumption. 
          + simpl. unfold boundG, boundL, upper_boundL, lower_boundL in Hle1.
            omega.
          + unfold boundG, boundL, upper_boundL, lower_boundL in Hle2.
            assert (Hles : sizeOf_exp e <= sizeOf_env k rho1).
            { eapply le_trans; [| now eapply sizeOf_env_get; eauto ].
              destruct k; try omega. simpl. eapply le_trans. 
              eapply fun_in_fundefs_sizeOf_exp; eauto. now eapply find_def_correct; eauto.
              now apply Max.le_max_l. }
            rewrite <- ! plus_assoc. rewrite <- plus_n_O.
            eapply plus_le_compat; [| simpl; omega ].
            rewrite <- mult_assoc, NPeano.Nat.mul_add_distr_r, NPeano.Nat.mul_add_distr_l.
            eapply le_trans. eassumption. eapply plus_le_compat.
            { destruct (Nat.eq_0_gt_0_cases k); subst.
              * unfold max_exp_env. rewrite sizeOf_env_O, Max.max_0_r.
                rewrite mult_assoc. eapply mult_le_compat_l.
                eapply le_trans. eassumption. now apply Max.le_max_r.
              * eapply le_trans. eapply mult_le_compat_l.
                eapply sizeOf_env_set_app; eauto.
                eapply fun_in_fundefs_sizeOf_exp; eauto. now eapply find_def_correct; eauto.
                rewrite mult_assoc. eapply mult_le_compat_l. now apply Max.le_max_r. }
            { rewrite mult_assoc. eapply mult_le_compat. omega.
              eapply le_trans; [eassumption |  now apply Max.le_max_r ]. }
          + eapply cc_approx_val_monotonic. eassumption. omega. }
    (* Case Eprim *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 3*length l) by (eapply project_vars_sizeOf_ctx_exp; eauto).
      pose (P :=
              fun n c1 c2 : nat =>
                c1 + n <= c2 + sizeOf_exp_ctx C <= 7 * c1 * max_exp_env k e rho1
                                                 + 7 * sizeOf_exp e + n).
      eapply cc_approx_exp_rel_mon with (P1 := P (sizeOf_exp_ctx C)).
      { intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
        edestruct project_vars_ctx_to_rho as [rho2' Hto_rho]; eauto.
        edestruct project_vars_correct as [Happ [Hfun' [Henv' Hvar]]]; eauto.
        edestruct Hvar as [v' [Hget' Happ']]; eauto.
        eapply ctx_to_rho_cc_approx_exp with (P' := P 0); eauto.
        - now firstorder.
        - now firstorder.
        - eapply cc_approx_exp_prim_compat with (S0 := boundL k e rho1).
          + unfold boundL, upper_boundL, lower_boundL, P. intros c1 c2 n Hle.
            rewrite <- !plus_n_O. intros [Hle1 Hle2]; split; try omega.
            ring_simplify. rewrite <- !plus_assoc, (plus_comm c2).
            eapply plus_le_compat; eauto. eapply plus_le_mult; eauto.
            now apply max_exp_env_grt_1. eapply le_trans. eassumption.
            omega.
          + eapply Forall2_cc_approx_var_env; eauto.
          + intros vs1 vs2 l1 f Hgetl Hgetf Happf Hall.
            unfold boundL, upper_boundL, lower_boundL, max_exp_env.
            assert (HadmX : sizeOf_env k rho1 = sizeOf_env k (M.set  v vs1 rho1)).
            { erewrite sizeOf_env_set, primAxiom; eauto. }
            erewrite HadmX; eauto.
            eapply IHe; [ | | | | eassumption | | | | eassumption ].
            * eapply cc_approx_env_P_extend with (v2 := vs2).
              eapply cc_approx_env_P_antimon; [ eassumption |]...
              eassumption.
            * now eauto.
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply occurs_free_Eprim_Included. 
            * intros f1 Hfin. eauto.
            * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
              normalize_bound_var... now eauto with Ensembles_DB.
            * eapply Fun_inv_set_In_Scope_l. now eauto.
              eapply Fun_inv_set_In_Scope_r_not_Γ. now eauto.
              intros Heq; subst. now eauto.
              eapply Fun_inv_mon; [ | now eauto ]...
            * eapply FV_inv_set_In_Scope_l. now constructor.
              eapply FV_inv_set_r. intros Hc. eapply Hnin.
              subst. now eauto. now eapply FV_inv_extend_Scope. }
      { intros c1 c2. unfold P, boundL, lower_boundL, upper_boundL.
        intros [Hle1 Hle2]; split; try omega.
        eapply le_trans;
          [| eapply plus_le_compat_r; eapply mult_le_compat_l; now apply max_exp_env_Eprim ].
        simpl. omega. }
   (* Case Ehalt *)
    - inv Hcc.
      assert(Hadm : sizeOf_exp_ctx C <= 3) by (eapply project_var_sizeOf_ctx_exp; eauto).
      pose (P :=
              fun n c1 c2 : nat =>
                c1 + n <= c2 + sizeOf_exp_ctx C <= 7 * c1 * max_exp_env k (Ehalt v) rho1
                                                 + 7 + n).
      eapply cc_approx_exp_rel_mon with (P1 := P (sizeOf_exp_ctx C)).
      { intros v1 c1 Hleq Hstep. assert (Hstep' := Hstep). inv Hstep'.
        edestruct project_var_ctx_to_rho as [rho2' Hto_rho]; eauto.
        edestruct project_var_correct as [Hnin' [Happ [Hfun' [Henv' Hvar]]]]; eauto.
        edestruct Hvar as [v' [Hget' Happ']]; eauto.
        eapply ctx_to_rho_cc_approx_exp with (P' := P 0); eauto.
        - now firstorder.
        - now firstorder.
        - eapply cc_approx_exp_halt_compat.
          unfold P. omega.
          eassumption. }
      { intros c1 c2. unfold P, boundL, lower_boundL, upper_boundL.
        intros [Hle1 Hle2]; split; try simpl; omega. }
  Qed.

  
  
End Closure_conversion_correct. 
