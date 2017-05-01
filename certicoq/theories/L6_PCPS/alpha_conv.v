(* Definition and semantics preservation proof for alpha conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)


Require Import L6.cps L6.ctx L6.cps_util L6.set_util L6.identifiers L6.Ensembles_util L6.List_util
        L6.eval L6.logical_relations L6.functions.
Require Import compcert.lib.Coqlib.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Fixpoint extend_fundefs (f: var -> var) (B B' : fundefs) : (var -> var) :=
  match B with
    | Fnil => f
    | Fcons g _ _ _ B =>
      match B' with
        | Fnil => f
        | Fcons g' _ _ _ B' =>
          (extend_fundefs f B B'){g ~> g'}
      end
  end.

Inductive construct_lst_injection : (var -> var) -> list var -> list var -> (var -> var) -> Prop :=
| Inj_nil :
    forall f, construct_lst_injection f [] [] f
| Inf_cons :
    forall f f' x xs y ys,
      construct_lst_injection f xs ys f' ->
      injective (f' {x ~> y}) ->
      construct_lst_injection f (x :: xs) (y :: ys) (f' {x ~> y}).

Inductive construct_fundefs_injection : (var -> var) -> fundefs -> fundefs -> (var -> var) -> Prop :=
| Inj_Fnil :
    forall f, construct_fundefs_injection f Fnil Fnil f
| Inf_Fcons :
    forall f f' g1 t1 xs1 e1 B1 g2 t2 xs2 e2 B2,
      construct_fundefs_injection f B1 B2 f' ->
      injective (f' {g1 ~> g2}) ->
      construct_fundefs_injection f (Fcons g1 t1 xs1 e1 B1) (Fcons g2 t2 xs2 e2 B2) (f' {g1 ~> g2}).

(** α-equivalent terms *)
Inductive Alpha_conv : exp -> exp -> (var -> var) -> Prop :=
| Alpha_Econstr :
    forall x x' t ys ys' e e' f,
      Forall2 (fun y y' => f y = y') ys ys' ->
      injective (f {x ~> x'}) -> 
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Econstr x t ys e) (Econstr x' t ys' e') f
| Alpha_Eproj :
    forall x x' tau N y y' e e' f, 
      f y = y' ->
      injective (f {x ~> x'}) ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eproj x tau N y e) (Eproj x' tau N y' e') f
| Alpha_Ecase :
    forall x x' pats pats' f,
      Forall2 (fun p p' => fst p = fst p' /\ Alpha_conv (snd p) (snd p') f) pats pats' ->
      f x = x' ->
      Alpha_conv (Ecase x pats) (Ecase x' pats') f
| Alpha_Eapp :
    forall g g' xs xs' f ft,
      Forall2 (fun y y' => f y = y') xs xs' ->
      f g = g' ->
      Alpha_conv (Eapp g ft xs) (Eapp g' ft xs') f
| Alpha_Eprim :
    forall x x' p ys ys' e e' f, 
      Forall2 (fun y y' => f y = y') ys ys' ->      
      injective (f {x ~> x'}) ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eprim x p ys e) (Eprim x' p ys' e') f
| Alpha_Efun :
    forall B B' e e' f f',
      construct_fundefs_injection f B B' f' ->
      Alpha_conv_fundefs B B' f' ->
      Alpha_conv e e' f' ->
      Alpha_conv (Efun B e) (Efun B' e') f
| Alpha_Ehalt :
    forall f x x',
      f x = x' ->
      Alpha_conv (Ehalt x) (Ehalt x') f
with Alpha_conv_fundefs : fundefs -> fundefs -> (var -> var) -> Prop :=
| Alpha_Fnil :
    forall f, Alpha_conv_fundefs Fnil Fnil f
| Alpha_Fcons :
    forall g g' t xs xs' e e' B B' f f',
      f g = g' ->
      length xs = length xs' ->
      Alpha_conv_fundefs B B' f ->
      construct_lst_injection f xs xs' f' ->
      Alpha_conv e e' f' ->
      Alpha_conv_fundefs (Fcons g t xs e B) (Fcons g' t xs' e' B') f.

Lemma construct_fundefs_injection_f_eq f f' B B' g :
  construct_fundefs_injection f B B' f' ->
  f_eq f g ->
  exists g',
    f_eq f' g' /\ construct_fundefs_injection g B B' g'.
Proof. 
  intros H Heq. induction H.
  - eexists; split. eassumption. constructor.
  - edestruct IHconstruct_fundefs_injection as [g' [Heq' Hc]] .
    eassumption. eexists. split.
    apply f_eq_extend. eassumption. 
    constructor. eauto. rewrite f_eq_extend. eassumption.
    now symmetry.
Qed.

Lemma construct_lst_injection_f_eq f f' l l' g :
  construct_lst_injection f l l' f' ->
  f_eq f g ->
  exists g',
    f_eq f' g' /\ construct_lst_injection g l l' g'.
Proof. 
  intros H Heq. induction H.
  - eexists; split. eassumption. constructor.
  - edestruct IHconstruct_lst_injection as [g' [Heq' Hc]] .
    eassumption. eexists. split.
    apply f_eq_extend. eassumption. 
    constructor. eauto. rewrite f_eq_extend. eassumption.
    now symmetry.
Qed.

Lemma Alpha_conv_proper_mut :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv /\
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv_fundefs.
Proof.
  eapply exp_def_mutual_ind; intros; split; intros H'; subst.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite <- H2. eassumption.
    + rewrite f_eq_extend. eassumption. symmetry. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption. 
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite H2. eassumption.
    + rewrite f_eq_extend. eassumption. eassumption.
    + eapply H; eauto.
      eapply f_eq_extend. eassumption. 
  - inv H'. inv H2. constructor. constructor.
    rewrite H1. reflexivity.
  - inv H'. inv H2. constructor;  eauto.
  - inv H'; constructor; eauto. inv H4. destruct y as [c' e'].
    inv H5. simpl in H1; subst. constructor.
    split; eauto. eapply H; eauto. symmetry; eassumption.      
    assert (Hsuf : Alpha_conv (Ecase v l) (Ecase (x0 v) l') y1).
    { eapply H0; eauto. symmetry; eassumption. 
      constructor; eauto. }
      now inv Hsuf.
  - inv H'; constructor; eauto. inv H4. destruct y as [c' e'].
    inv H5. simpl in H1; subst. constructor.
    split; eauto. eapply H; eauto.
    assert (Hsuf : Alpha_conv (Ecase v l) (Ecase (y1 v) l') x0).
    { eapply H0; eauto. constructor; eauto. }
    now inv Hsuf.
  - inv H'; constructor; eauto.
    + rewrite f_eq_extend. eassumption. symmetry. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption. 
  - inv H'; constructor; eauto.
    + rewrite f_eq_extend; eassumption.
    + eapply H; eauto. 
      eapply f_eq_extend. eassumption. 
  - inv H'. edestruct construct_fundefs_injection_f_eq as [g' [Heq Hinj]].
    eassumption. eassumption. econstructor. eassumption.
    eapply H; eauto. now symmetry.
    eapply H0; eauto. now symmetry.
  - inv H'. edestruct construct_fundefs_injection_f_eq as [g' [Heq Hinj]].
    eassumption. now symmetry; eassumption. econstructor. eassumption.
    eapply H; eauto. now symmetry.
    eapply H0; eauto. now symmetry. 
  - inv H'. constructor; eauto. 
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 Heq. rewrite <- H1. eassumption.
  - inv H'. constructor; eauto. 
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 Heq. rewrite H1. eassumption.
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite <- H2. eassumption. 
    + rewrite f_eq_extend. eassumption. symmetry. eassumption.
    + eapply H; eauto. symmetry.
      eapply f_eq_extend. eassumption. 
  - inv H'; constructor; eauto.
    + eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 Heq. rewrite H2. eassumption. 
    + rewrite f_eq_extend. eassumption. eassumption.
    + eapply H; eauto. eapply f_eq_extend. eassumption. 
  - inv H'; constructor; eauto.
  - inv H'; constructor; eauto.
  - inv H'. edestruct construct_lst_injection_f_eq as [g' [Heq Hinj]].
    eassumption. eassumption. econstructor; eauto.
    eapply H0; eauto. now symmetry.
    eapply H; eauto. now symmetry. 
  - inv H'. edestruct construct_lst_injection_f_eq as [g' [Heq Hinj]].
    eassumption. symmetry. eassumption. econstructor; eauto.
    now eapply H0; eauto. now eapply H; eauto.
  - inv H'. constructor.
  - inv H'. constructor.
Qed.

Instance Alpha_conv_proper :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv.
Proof.
  now apply Alpha_conv_proper_mut.
Qed.

Instance Alpha_conv_fundfes_proper :
  Proper (Logic.eq ==> Logic.eq ==> f_eq ==> iff) Alpha_conv_fundefs.
Proof.
  now apply Alpha_conv_proper_mut.
Qed.

(** Pair of contexts that preserves α-equivalence *)
Definition Alpha_conv_ctx C C' f :=
  forall e e',
    Alpha_conv e e' f ->
    Alpha_conv (C |[ e ]|) (C' |[ e']|) f.

Instance alpha_conv_ctx_Proper : Proper (eq ==> eq ==> f_eq ==> iff) Alpha_conv_ctx.
Proof. 
  intros c1 c2 Heq1 c3 c4 Heq2 f1 f2 Hfeq; subst; split; intros H1 e1 e2 H2.
  rewrite <- Hfeq. rewrite <- Hfeq in H2. now eauto.
  rewrite Hfeq. rewrite Hfeq in H2. now eauto. 
Qed.

Section Alpha_conv_correct.

  Variable pr : prims.
  Variable cenv : cEnv.

  Definition preord_env_P_inj (P : Ensemble var) k f rho1 rho2 :=
    forall x : var,
      P x -> preord_var_env pr cenv k rho1 rho2 x (f x).

  Lemma Forall2_app {A B} (P : A -> B -> Prop) xs ys f :
    Forall2 (fun x y => f x = y) xs ys ->
    (forall x y, List.In x xs -> f x = y -> P x y) ->
    Forall2 P xs ys. 
  Proof. 
    intros Hall Hyp. induction Hall.
    - constructor.
    - constructor.
      + eapply Hyp. now constructor. eassumption.
      + eapply IHHall.
        intros. eapply Hyp. now constructor 2.
        eassumption. 
  Qed.

  Lemma construct_fundefs_injection_injective f B1 B2 f' :
    construct_fundefs_injection f B1 B2 f' ->
    injective f ->
    injective f'. 
  Proof.
    intros H1 H2. induction H1; eauto. 
  Qed.

  Lemma construct_lst_injection_injective f xs ys f' :
    construct_lst_injection f xs ys f' ->
    injective f ->
    injective f'. 
  Proof.
    intros H1 H2. induction H1; eauto. 
  Qed.
  
  Lemma preord_env_P_inj_set (P : Ensemble var) (rho1 rho2 : env) 
        (k : nat)  f(x y : var) (v1 v2 : val) : 
    preord_env_P_inj (Setminus var P (Singleton var x)) k f rho1 rho2 ->
    preord_val pr cenv k v1 v2 ->
    injective_subdomain (Union _ P (Singleton _ x)) (f {x ~> y}) ->
    preord_env_P_inj P k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
  Proof.
    intros Henv Hv Hinj z HP. unfold extend. 
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      destruct (peq (f z) y).
      + exfalso. eapply Hneq. eapply Hinj. left. eassumption.
        now eauto.
        rewrite extend_gso; eauto.
        rewrite extend_gss. eassumption.
      + edestruct (Henv z); eauto.
        constructor; eauto. intros Hc. inv Hc. congruence. 
        eexists. rewrite M.gso; eauto. 
  Qed.
  
  Lemma preord_env_P_inj_set_alt (P : Ensemble var) (rho1 rho2 : env) 
        (k : nat)  f(x y : var) (v1 v2 : val) : 
    preord_env_P_inj (Setminus var P (Singleton var x)) k f rho1 rho2 ->
    preord_val pr cenv k v1 v2 ->
    ~ In _ (image f (Setminus _ P (Singleton _ x))) y ->
    preord_env_P_inj P k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
  Proof.
    intros Henv Hv Hnin z HP. unfold extend. 
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      destruct (peq (f z) y).
      + exfalso. eapply Hnin. eexists; eauto.
        split; eauto. constructor; eauto.
        intros Hc; inv Hc; congruence.
      + edestruct (Henv z); eauto.
        constructor; eauto. intros Hc. inv Hc. congruence. 
        eexists. rewrite M.gso; eauto. 
  Qed.

  Lemma preord_env_P_inj_antimon (P1 P2 : var -> Prop) (k : nat) (rho1 rho2 : env) f :
    preord_env_P_inj P2 k f rho1 rho2 ->
    Included var P1 P2 -> preord_env_P_inj P1 k f rho1 rho2.
  Proof.
    intros Henv Hi x HP. eapply Henv. now apply Hi.
  Qed.

  Lemma preord_env_P_inj_monotonic :
    forall P (k j : nat) (rho1 rho2 : env) f,
      j <= k -> preord_env_P_inj P k f rho1 rho2 -> preord_env_P_inj P j f rho1 rho2.
  Proof.
    intros P k j rho1 rho2 f Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2] ]; eauto.
    eexists; split; eauto. eapply preord_val_monotonic; eauto.
  Qed.

  Global Instance preord_env_P_inj_proper  :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           preord_env_P_inj.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    eapply preord_env_P_inj_antimon; subst; eauto.
  Qed.

  Lemma Alpha_conv_fundefs_find_def B1 B2 f g t xs1 e1 :
    Alpha_conv_fundefs B1 B2 f ->
    find_def g B1 = Some (t, xs1, e1) ->
    injective f ->
    exists xs2 e2 f', 
      find_def (f g) B2 = Some (t, xs2, e2) /\
      length xs1 = length xs2 /\
      construct_lst_injection f xs1 xs2 f' /\
      Alpha_conv e1 e2 f'.
  Proof. 
    intros Ha Hdef Hinj. induction Ha. 
    - inv Hdef. 
    - simpl in Hdef. subst. destruct (M.elt_eq g g0).
      + subst. inv Hdef. exists xs', e'.
        simpl. rewrite peq_true. eauto.
      + edestruct IHHa as [xs2 [ e2 Ha' ] ]; eauto.
        edestruct (peq (f g) (f g0)). 
        * eapply Hinj in e0. subst. congruence. now constructor.
          now constructor.
        * do 2 eexists. simpl. rewrite peq_false; eauto.
  Qed.

  Lemma setlist_length2 (rho rho' rho1 : env) (xs1 xs2 : list var) (vs1 vs2 : list val) :
    length xs1 = length xs2 ->
    length vs1 = length vs2 ->
    setlist xs1 vs1 rho = Some rho1 ->
    exists rho2 : M.t val, setlist xs2 vs2 rho' = Some rho2.
  Proof. 
    revert xs2 vs1 vs2 rho1.
    induction xs1 as [| x xs1 IHxs ]; intros xs2 vs1 vs2 rho1 Hlen1 Hlen2 Hset.
    - inv Hset. destruct vs1; try discriminate. inv H0.
      destruct vs2; try discriminate. destruct xs2; try discriminate.
      eexists; simpl; eauto.
    - destruct xs2; try discriminate.
      destruct vs1; try discriminate. destruct vs2; try discriminate.
      inv Hlen1. inv Hlen2. simpl in Hset. 
      destruct (setlist xs1 vs1 rho) eqn:Heq2; try discriminate. inv Hset.
      edestruct IHxs as [vs2' Hset2]; try eassumption.
      eexists. simpl; rewrite Hset2; eauto.
  Qed.

  Lemma preord_env_P_inj_setlist (P1 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list val) f f':
    preord_env_P_inj (Setminus _ P1 (FromList xs1)) k f rho1 rho2 ->
    Forall2 (preord_val pr cenv k) vs1 vs2 ->
    construct_lst_injection f xs1 xs2 f' ->
    setlist xs1 vs1 rho1 = Some rho1' ->
    setlist xs2 vs2 rho2 = Some rho2' ->
    preord_env_P_inj P1 k f' rho1' rho2'.
  Proof.
    revert P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f f'. induction xs1;
      intros P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2  f f' Hpre Hall Hinj Hset1 Hset2 x HP v Hget.
    - inv Hinj. destruct vs1; try discriminate.
      inv Hall. inv Hset1; inv Hset2. eapply Hpre; eauto.
      constructor; eauto.
    - destruct vs1; try discriminate. inv Hall. inv Hinj.
      simpl in Hset1, Hset2. 
      destruct (setlist xs1 vs1 rho1) eqn:Heq1;
        destruct (setlist ys l' rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. rewrite M.gsspec in Hget.
      destruct (peq x a); subst.
      + inv Hget. eexists. 
        simpl. unfold extend. rewrite peq_true.
        rewrite M.gss. eauto.
      + edestruct IHxs1 with (P1 := Setminus var P1 (Singleton _ a)) as [v2 [Het' Hpre']]; eauto.
        * rewrite Setminus_Union.
          rewrite FromList_cons in Hpre. eassumption.
        * constructor; eauto. intros Hc.  inv Hc; eauto.
        * eexists. rewrite extend_gso; eauto.
          rewrite M.gso; [ now eauto |].
          intros Heq. eapply n. 
          eapply H7; try now constructor.
          rewrite extend_gss. rewrite extend_gso; eassumption. 
  Qed.
  
  Lemma preord_env_P_inj_setlist_alt (P1 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 xs2 : list var) (vs1 vs2 : list val) f :
    preord_env_P_inj (Setminus _ P1 (FromList xs1)) k f rho1 rho2 ->
    Forall2 (preord_val pr cenv k) vs1 vs2 ->
    NoDup xs1 -> NoDup xs2 ->
    length xs1 = length xs2 ->
    Disjoint _ (image f (Setminus _ P1 (FromList xs1))) (FromList xs2) ->
    setlist xs1 vs1 rho1 = Some rho1' ->
    setlist xs2 vs2 rho2 = Some rho2' ->
    preord_env_P_inj P1 k (f <{ xs1 ~> xs2 }>)  rho1' rho2'.
  Proof with now eauto with Ensembles_DB.
    revert P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f.
    induction xs1;
      intros P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f Hpre Hall
             Hnd1 Hnd2 Hlen HD Hset1 Hset2 x HP v Hget;
      destruct xs2; try discriminate;
      destruct vs1; try discriminate;
      destruct vs2; try discriminate.
    - rewrite FromList_nil in Hpre.
      inv Hset1. inv Hset2. eapply Hpre; eauto.
      constructor; eauto. eapply not_In_Empty_set.
    - inv Hall. inv Hlen. inv Hnd1. inv Hnd2. simpl in *.
      destruct (setlist xs1 vs1 rho1) eqn:Heq1;
        destruct (setlist xs2 vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. rewrite M.gsspec in Hget.
      destruct (peq x a); subst.
      + inv Hget. eexists. 
        simpl. rewrite extend_gss.
        rewrite M.gss. eauto.
      + edestruct IHxs1 with (P1 := Setminus var P1 (Singleton _ a))
          as [v2' [Hget' Hpre']]; eauto.
        * rewrite Setminus_Union.
          rewrite FromList_cons in Hpre. eassumption.
        * eapply Disjoint_Included; [| | eassumption ].
          rewrite FromList_cons...
          rewrite FromList_cons, Setminus_Union. reflexivity.
        * constructor; eauto. intros Hc; inv Hc.
          congruence.
        * eexists. rewrite extend_gso; eauto.
          rewrite M.gso; [ now eauto |].
          rewrite !FromList_cons in HD. intros Heq.
          eapply HD.
          assert (Hnin : ~ List.In x xs1).
          { destruct (in_dec peq x xs1); eauto.
            edestruct (@extend_lst_gss var) as [y' [Heq' Hin]]; eauto.
            rewrite Heq' in Heq. subst v0. exfalso; eauto. }
          rewrite extend_lst_gso in Heq, Hget'; eauto.
          constructor; eauto.
          eexists. split; eauto. constructor; eauto.
          intros Hc; inv Hc. inv H; congruence.
          eauto.
  Qed.

  Lemma Forall2_preord_var_env_map k P σ rho rho' l :
    preord_env_P_inj P k σ rho rho' ->
    Included _ (FromList l) P ->
    Forall2 (preord_var_env pr cenv k rho rho') l (map σ l).
  Proof with now eauto with Ensembles_DB.
    induction l; intros Henv Hin; simpl; constructor.
    - eapply Henv. eapply Hin. rewrite FromList_cons...
    - eapply IHl; eauto.
      eapply Included_trans; [| eassumption ].
      rewrite FromList_cons...
  Qed.

  Lemma preord_env_P_inj_getlist_l (P : var -> Prop) k f rho1 rho2 xs vs1 :
    preord_env_P_inj P k f rho1 rho2 ->
    Included var (FromList xs) P ->
    getlist xs rho1 = Some vs1 ->
    exists vs2 : list val,
      getlist (map f xs) rho2 = Some vs2 /\ Forall2 (preord_val pr cenv k) vs1 vs2.
  Proof with now eauto with Ensembles_DB.
    revert vs1. induction xs; intros vs1 Henv Hinc Hget.
    - eexists; split; eauto. inv Hget. constructor.
    - simpl in *.
      destruct (M.get a rho1) eqn:Hgeta; try discriminate.
      destruct (getlist xs rho1) eqn:Hgetl; try discriminate.
      inv Hget.
      edestruct Henv with (x := a) as [x' [Hgetx' Hprex']]. eapply Hinc. rewrite FromList_cons...
      eassumption.
      edestruct IHxs as [l' [Hgetl' Hprel']]. eassumption.
      eapply Included_trans; [| eassumption ]. rewrite FromList_cons...
      reflexivity.
      eexists. rewrite Hgetx', Hgetl'. split.
      reflexivity.
      now constructor; eauto.
  Qed.

  Global Instance preord_env_P_inj_f_proper : Proper (eq ==> eq ==> f_eq ==> eq ==> eq ==> iff)
                                                preord_env_P_inj.
  Proof.
    constructor; subst; intros Hp.
    intros z Hz. rewrite <- H1. eauto.
    intros z Hz. rewrite H1. eauto.
  Qed.

  Lemma preord_env_P_inj_set_not_In_P_l P k f rho1 rho2 x v :
    preord_env_P_inj P k f rho1 rho2 ->
    ~ In _ P x ->
    preord_env_P_inj P k f (M.set x v rho1) rho2.
  Proof.
    intros Henv Hnin y Hy v' Hget. eapply Henv. eassumption.
    rewrite M.gso in Hget. eassumption. intros Hc; subst.
    eauto.
  Qed.

  Lemma preord_env_P_inj_set_not_In_P_r P k f rho1 rho2 x v :
    preord_env_P_inj P k f rho1 rho2 ->
    ~ In _ (image f P) x ->    
    preord_env_P_inj P k f rho1 (M.set x v rho2).
  Proof.
    intros Henv Hnin y Hy v' Hget.
    edestruct Henv as [v'' [Hget' Hv]]; eauto.
    eexists; split; eauto.
    rewrite M.gso. eassumption. intros Hc; subst.
    eapply Hnin. eexists; eauto.
  Qed.
  
  Lemma preord_env_P_inj_reset P k f rho rho' x y v :
    M.get (f x) rho' = Some v ->
    ~ In _ (image f P) y ->
    preord_env_P_inj P k f rho rho' ->
    preord_env_P_inj P k (f {x ~> y}) rho (M.set y v rho').
  Proof.
    intros Hget Hnin Hpre z Hz v' Hget'.
    destruct (peq z x); subst.
    - rewrite extend_gss, M.gss.
      edestruct Hpre as [v2 [Hget'' Hpre2]]; eauto.
      rewrite Hget'' in Hget; inv Hget.
      eexists; eauto.
    - rewrite extend_gso, M.gso; eauto.
      eapply Hpre; eauto.
      intros Hc; subst. eapply Hnin; eexists; eauto.
  Qed.


  Lemma preord_env_P_inj_resetlist P k f rho rho' rho'' xs ys vs :
    getlist (map f xs) rho' = Some vs ->
    Disjoint _ (image f P) (FromList ys) ->
    setlist ys vs rho' = Some rho'' ->
    NoDup ys ->
    length xs = length ys ->
    preord_env_P_inj P k f rho rho' ->
    preord_env_P_inj P k (f <{xs ~> ys}>) rho rho''.
  Proof.
    revert rho'' ys vs; induction xs; intros rho'' ys vs Hget HD Hset Hdup Hlen Hpre.
    - simpl. destruct vs; try discriminate.
      destruct ys; try discriminate. inv Hset. eassumption.
    - simpl in *.
      destruct (M.get (f a) rho') eqn:Heqa; try discriminate.
      destruct (getlist (map f xs) rho') eqn:Hgetl; try discriminate.
      inv Hget.
      destruct ys; try discriminate. simpl in Hset.
      destruct (setlist ys l rho') eqn:Hsetl; try discriminate.
      rewrite FromList_cons in HD. inv Hset.
      assert (Hpre' : preord_env_P_inj P k (f <{ xs ~> ys }>) rho t).
      { eapply IHxs. reflexivity.
        now eauto with Ensembles_DB.
        eassumption. now inv Hdup. now inv Hlen. eassumption. }
      intros z Hz v' Hget'.
      destruct (peq z a); subst.
      + rewrite extend_gss, M.gss.
        edestruct Hpre as [v2 [Hget'' Hpre2]]; eauto.
        rewrite Hget'' in Heqa; inv Heqa.
        eexists; eauto.
      + rewrite extend_gso, M.gso; eauto.
        eapply Hpre'; eauto.
        inv Hdup. intros Hc; subst.
        edestruct in_dec with (a := z) (l := xs) as [Hin | Hnin ].
        now apply peq.
        edestruct (@extend_lst_gss var f xs ys z) as [x' [Heq Hin']].
        eassumption. now inv Hlen. eapply H1.
        rewrite <- Heq in Hin'. eassumption.
        rewrite extend_lst_gso in H1; [| eassumption ].
        eapply HD. constructor; eauto.
        eexists; split; eauto. rewrite extend_lst_gso; [| eassumption ].
        reflexivity.
  Qed.

  Lemma preord_env_P_inj_def_funs_pre k rho1 rho2 B1 B1' B2 B2' f h h' e :
    (* The IH *)
    (forall m : nat,
       m < k ->
       forall (e1 e2 : exp) (rho1 rho2 : env) (f : var -> var),
         injective f ->
         Alpha_conv e1 e2 f ->
         preord_env_P_inj (occurs_free e1) m f rho1 rho2 ->
         preord_exp pr cenv m (e1, rho1) (e2, rho2)) ->
    construct_fundefs_injection f B1 B2 h ->
    construct_fundefs_injection f B1' B2' h' ->
    injective f ->
    Alpha_conv_fundefs B1 B2 h'  ->
    Alpha_conv_fundefs B1' B2' h' ->
    preord_env_P_inj (occurs_free (Efun B1' e)) k f rho1 rho2 ->
    preord_env_P_inj (Union _ (occurs_free (Efun B1' e)) (name_in_fundefs B1)) k h
                     (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2).
  Proof with now eauto with Ensembles_DB.
    revert B1 rho1 rho2 B1' B2 B2' f h h' e.
    induction k as [ k IH' ] using lt_wf_rec1.
    induction B1; intros rho1 rho2 B1' B2 B2' g h h' e' IHe Hinj Hinj' Hinj'' Ha Ha' Hpre.
    - inv Ha. simpl. subst. inv Hinj. eapply preord_env_P_inj_set. 
      + eapply preord_env_P_inj_antimon. now eapply IHB1; eauto.
        eauto 6 with Ensembles_DB.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct Alpha_conv_fundefs_find_def
          as [xs2 [e2 [f'' [Hf' [Hlen' [Hinj''' Ha'' ] ] ] ] ] ]; [ apply Ha' | | | ]; eauto.
        now eapply construct_fundefs_injection_injective; eauto.
        edestruct setlist_length2 as [rho2' Hs']; eauto.
        exists xs2. exists e2. exists rho2'. split; eauto.
        split; [ now eauto |]. intros Hleq Hpre'.
        eapply IHe; [| | eassumption |]. omega.
        eapply construct_lst_injection_injective; eauto.
        now eapply construct_fundefs_injection_injective; eauto.
        apply find_def_correct in Hf; eauto.
        eapply preord_env_P_inj_antimon; [| eapply occurs_free_in_fun; eassumption ]. 
        * eapply preord_env_P_inj_setlist;
          [ | eassumption | eassumption | now eauto | now eauto  ].
          eapply preord_env_P_inj_antimon.
          eapply IH'; eauto. intros. eapply IHe. omega. now eauto. now eauto.
          eassumption.
          eapply (preord_env_P_inj_monotonic _ k). omega.
          now eauto. rewrite Setminus_Union_distr.
          rewrite Setminus_Same_set_Empty_set.
          normalize_occurs_free...
      + eapply injective_subdomain_antimon. eassumption.
        constructor.
    - inv Ha. simpl. inv Hinj. eapply preord_env_P_inj_antimon. eassumption.
      eauto with Ensembles_DB.
  Qed.

  (** α-equivalence preserves semantics *)
  Lemma Alpha_conv_correct k rho1 rho2 e1 e2 f :
    injective f ->
    Alpha_conv e1 e2 f ->
    preord_env_P_inj (occurs_free e1) k f rho1 rho2 ->
    preord_exp pr cenv k (e1, rho1) (e2, rho2).
  Proof with now eauto with Ensembles_DB. 
    revert e1 e2 rho1 rho2 f.
    induction k as [ k IH ] using lt_wf_rec1.
    induction e1 using exp_ind'; intros e2 rho1 rho2 f Hinj Ha Henv; inv Ha.
    - eapply preord_exp_const_compat; eauto; intros.
      + eapply Forall2_app; [ eassumption |].
        intros x y Hin Heq. specialize (Henv x).
        rewrite Heq in Henv. eapply Henv.
        now constructor.
      + eapply IHe1. eassumption. eassumption.
        eapply preord_env_P_inj_set. 
        eapply preord_env_P_inj_antimon; eauto.
        normalize_occurs_free...
        rewrite preord_val_eq. constructor; eauto using Forall2_Forall2_asym_included.
        eapply injective_subdomain_antimon. eassumption. now constructor.
    - inv H1. eapply preord_exp_case_nil_compat.
    - inv H1. destruct H2 as [Heq Ha]. destruct y as [c' e2]. simpl in Heq; subst.
      eapply preord_exp_case_cons_compat; eauto.
      eapply Forall2_monotonic; [| eassumption ]. intros x1 x2 H; now inv H. 
      eapply IHe1. eassumption. eassumption.
      eapply preord_env_P_inj_antimon.
      eassumption. normalize_occurs_free...
      eapply IHe0. eassumption. now constructor; eauto.
      eapply preord_env_P_inj_antimon.
      eassumption. normalize_occurs_free...
    - eapply preord_exp_proj_compat; eauto; intros.
      eapply IHe1. eassumption. eassumption.
      eapply preord_env_P_inj_set. 
      eapply preord_env_P_inj_antimon; eauto.
      normalize_occurs_free... eassumption.
      eapply injective_subdomain_antimon. eassumption. now constructor.
    - eapply preord_exp_fun_compat; eauto.
      eapply IHe1; [| eassumption |].
      eapply construct_fundefs_injection_injective. eassumption. eassumption.
      eapply preord_env_P_inj_antimon.
      + eapply preord_env_P_inj_def_funs_pre; eauto.
      + eapply occurs_free_Efun_Included.
    - eapply preord_exp_app_compat.
      + now eauto.
      + eapply Forall2_app; [ eassumption |].
        intros x y Hin Heq. specialize (Henv x).
        rewrite Heq in Henv. eapply Henv.
        now constructor.
    - eapply preord_exp_prim_compat; eauto; intros.
      + eapply Forall2_app; [ eassumption |].
        intros x y Hin Heq. specialize (Henv x).
        rewrite Heq in Henv. eapply Henv.
        now constructor.
      + eapply IHe1. eassumption. eassumption.
        eapply preord_env_P_inj_set. 
        eapply preord_env_P_inj_antimon; eauto.
        normalize_occurs_free...
        eassumption.
        eapply injective_subdomain_antimon. eassumption. now constructor.
    - eapply preord_exp_halt_compat.
      eapply Henv. now constructor.
  Qed.
  
End Alpha_conv_correct.

Close Scope fun_scope.
Close Scope ctx_scope.