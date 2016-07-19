Require Import cps ctx cps_util set_util identifiers Ensembles_util List_util
        eval logical_relations functions.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.


Fixpoint extend_lst (f: var -> var) (xs xs' : list var) : (var -> var) :=
  match xs with
    | [] => f
    | x :: xs =>
      match xs' with
        | [] => f
        | x' :: xs' =>
          extend_lst (f{x ~> x'}) xs xs'
      end
  end.

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

(* Notation " f '{[' xs '~>' ys ']}' " := (extend_lst f xs ys) (at level 10, no associativity) *)
(*                                        : alpha_scope. *)

(* Notation " f '<{' B '~>' B' '}>' " := (extend_fundefs f B B') (at level 10, no associativity) *)
(*                                        : alpha_scope. *)

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
    forall x x' tau t ys ys' e e' f,
      Forall2 (fun y y' => f y = y') ys ys' ->
      injective (f {x ~> x'}) -> 
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Econstr x tau t ys e) (Econstr x' tau t ys' e') f
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
    forall g g' xs xs' f,
      Forall2 (fun y y' => f y = y') xs xs' ->
      f g = g' ->
      Alpha_conv (Eapp g xs) (Eapp g' xs') f
| Alpha_Eprim :
    forall x x' tau p ys ys' e e' f, 
      Forall2 (fun y y' => f y = y') ys ys' ->      
      injective (f {x ~> x'}) ->
      Alpha_conv e e' (f {x ~> x'}) ->
      Alpha_conv (Eprim x tau p ys e) (Eprim x' tau p ys' e') f
| Alpha_Efun :
    forall B B' e e' f f',
      construct_fundefs_injection f B B' f' ->
      Alpha_conv_fundefs B B' f' ->
      Alpha_conv e e' f' ->
      Alpha_conv (Efun B e) (Efun B' e') f
with Alpha_conv_fundefs : fundefs -> fundefs -> (var -> var) -> Prop :=
| Alpha_Fnil :
    forall f, Alpha_conv_fundefs Fnil Fnil f
| Alpha_Fcons :
    forall g g' tau xs xs' e e' B B' f f',
      f g = g' ->
      length xs = length xs' ->
      Alpha_conv_fundefs B B' f ->
      construct_lst_injection f xs xs' f' ->
      Alpha_conv e e' f' ->
      Alpha_conv_fundefs (Fcons g tau xs e B) (Fcons g' tau xs' e' B') f.

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
  
Definition preord_env_P_inj P k f rho1 rho2 :=
  forall x : var,
    P x -> preord_var_env k rho1 rho2 x (f x).

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
  preord_val k v1 v2 ->
  injective (f {x ~> y}) ->
  preord_env_P_inj P k (f {x ~> y}) (M.set x v1 rho1) (M.set y v2 rho2).
Proof. 
  intros Henv Hv Hinj z HP. unfold extend. 
  destruct (Coqlib.peq z x) as [| Hneq] eqn:Heq'.
  - subst. intros z Hget.
    rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss; eauto.
  - intros z' Hget. rewrite M.gso in Hget; eauto.
    destruct (Coqlib.peq (f z) y).
    + exfalso. eapply Hneq. eapply Hinj. now constructor.
      now constructor. rewrite extend_gso; eauto.
      rewrite extend_gss. eassumption.
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

Instance preord_env_P_inj_proper  :
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
      simpl. rewrite Coqlib.peq_true. eauto.
    + edestruct IHHa as [xs2 [ e2 Ha' ] ]; eauto.
      edestruct (Coqlib.peq (f g) (f g0)). 
      * eapply Hinj in e0. subst. congruence. now constructor.
        now constructor.
      * do 2 eexists. simpl. rewrite Coqlib.peq_false; eauto.
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
  preord_env_P_inj P1 k f rho1 rho2 ->
  Forall2 (preord_val k) vs1 vs2 ->
  construct_lst_injection f xs1 xs2 f' ->
  setlist xs1 vs1 rho1 = Some rho1' ->
  setlist xs2 vs2 rho2 = Some rho2' ->
  preord_env_P_inj (Union _ P1 (FromList xs1)) k f' rho1' rho2'.
Proof.
  revert P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2 f f'. induction xs1;
  intros P1 rho1 rho2 rho1' rho2' xs2 vs1 vs2  f f' Hpre Hall Hinj Hset1 Hset2 x HP v Hget.
  - inv Hinj. destruct vs1; try discriminate.
    inv Hall. 
    inv Hset1; inv Hset2. eapply Hpre; eauto.
    inv HP; [ now eauto | now inv H ]. 
  - destruct vs1; try discriminate. inv Hall. inv Hinj.
    simpl in Hset1, Hset2. 
    destruct (setlist xs1 vs1 rho1) eqn:Heq1;
      destruct (setlist ys l' rho2) eqn:Heq2; try discriminate.
    inv Hset1; inv Hset2. rewrite M.gsspec in Hget.
    destruct (Coqlib.peq x a); subst.
    + inv Hget. eexists. 
      simpl. unfold extend. rewrite Coqlib.peq_true.
      rewrite M.gss. eauto.
    + edestruct IHxs1 as [v2 [Het' Hpre'] ]; eauto.
      * inv HP; [ now left; eauto |].
        rewrite FromList_cons in H. inv H.
        inv H0. congruence. right; eauto.
      * eexists. unfold extend. rewrite Coqlib.peq_false; [| now eauto ].
        rewrite M.gso; [ now eauto |].
        intros Heq. eapply n. 
        eapply H7; try now constructor.
        rewrite extend_gss. rewrite extend_gso; eassumption. 
Qed.
 
Lemma preord_env_P_inj_def_funs_pre k rho1 rho2 B1 B1' B2 B2' f h h' e :
  (* The IH *)
  (forall m : nat,
     m < k ->
     forall (e1 e2 : exp) (rho1 rho2 : env) (f : var -> var),
       injective f ->
       Alpha_conv e1 e2 f ->
       preord_env_P_inj (occurs_free e1) m f rho1 rho2 ->
       preord_exp m (e1, rho1) (e2, rho2)) ->
  construct_fundefs_injection f B1 B2 h ->
  construct_fundefs_injection f B1' B2' h' ->
  injective f ->
  Alpha_conv_fundefs B1 B2 h'  ->
  Alpha_conv_fundefs B1' B2' h' ->
  preord_env_P_inj (occurs_free (Efun B1' e)) k f rho1 rho2 ->
  preord_env_P_inj (Union _ (occurs_free (Efun B1' e)) (name_in_fundefs B1)) k h
                   (def_funs B1' B1 rho1 rho1) (def_funs B2' B2 rho2 rho2).
Proof.
  revert B1 rho1 rho2 B1' B2 B2' f h h' e.
  induction k as [ k IH' ] using lt_wf_rec1.
  induction B1; intros rho1 rho2 B1' B2 B2' f h h' e' IHe Hinj Hinj' Hinj'' Ha Ha' Hpre.
  - inv Ha. simpl. subst. inv Hinj. eapply preord_env_P_inj_set. 
    + eapply preord_env_P_inj_antimon. now eapply IHB1; eauto.
      rewrite !Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r.
      eapply Included_Union_compat.
      * eapply Setminus_Included. now apply Included_refl.
      * eapply Subset_Setminus.
    + rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
      edestruct Alpha_conv_fundefs_find_def
        as [xs2 [e2 [f'' [Hf' [Hlen' [Hinj''' Ha'' ] ] ] ] ] ]; [ apply Ha' | | | ]; eauto.
      now eapply construct_fundefs_injection_injective; eauto.
      edestruct setlist_length2 as [rho2' Hs']; eauto.
      exists t1. exists xs2. exists e2. exists rho2'. split; eauto.
      split; [ now eauto |]. intros Hleq Hpre'.
      eapply IHe; [| | eassumption |]. omega.
      eapply construct_lst_injection_injective; eauto.
      now eapply construct_fundefs_injection_injective; eauto.
      eapply preord_env_P_inj_antimon.
      * eapply preord_env_P_inj_setlist;
        [ | eassumption | eassumption | now eauto | now eauto  ].
        eapply IH'; eauto. intros. eapply IHe. omega. now eauto. now eauto.
        eassumption.
        eapply (preord_env_P_inj_monotonic _ k). omega.
        now eauto.
      * apply find_def_correct in Hf; eauto.
        rewrite occurs_free_Efun.
        eapply Included_trans.
        eapply occurs_free_in_fun. eassumption. 
        rewrite Union_sym. eapply Included_Union_compat; [| now apply Included_refl ].
        rewrite Union_sym. eapply Included_Union_compat; [| now apply Included_refl ].
        now apply Included_Union_l.
    + eassumption.
  - inv Ha. simpl. inv Hinj. eapply preord_env_P_inj_antimon. eassumption.
    rewrite Union_Empty_set_l. now apply Included_refl.
Qed.

(** α-equivalence preserves semantics *)
Lemma Alpha_conv_correct k rho1 rho2 e1 e2 f :
  injective f ->
  Alpha_conv e1 e2 f ->
  preord_env_P_inj (occurs_free e1) k f rho1 rho2 ->
  preord_exp k (e1, rho1) (e2, rho2).
Proof. 
  revert e1 e2 rho1 rho2 f.
  induction k as [ k IH ] using lt_wf_rec1.
  induction e1 using exp_ind'; intros e2 rho1 rho2 f Hinj Ha Henv; inv Ha.
  - eapply preord_exp_const_compat; eauto; intros.
    + eapply Forall2_app; [ eassumption |].
      intros x y Hin Heq. specialize (Henv x).
      rewrite Heq in Henv. eapply Henv.
      now constructor.
    + eapply IHe1. eassumption. eassumption.
      eapply preord_env_P_inj_set; [| | eassumption ]. 
      eapply preord_env_P_inj_antimon; eauto.
      rewrite occurs_free_Econstr. now apply Included_Union_r.
      rewrite preord_val_eq. constructor; eauto using Forall2_Forall2_asym_included.
  - inv H1. eapply preord_exp_case_nil_compat.
  - inv H1. destruct H2 as [Heq Ha]. destruct y as [c' e2]. simpl in Heq; subst.
    eapply preord_exp_case_cons_compat; eauto.
    eapply IHe1. eassumption. eassumption.
    eapply preord_env_P_inj_antimon.
    eassumption. rewrite occurs_free_Ecase_cons. now apply Included_Union_l.
    eapply IHe0. eassumption. now constructor; eauto.
    eapply preord_env_P_inj_antimon.
    eassumption. rewrite occurs_free_Ecase_cons.
    rewrite Union_assoc. now apply Included_Union_r.
  - eapply preord_exp_proj_compat; eauto; intros.
    eapply IHe1. eassumption. eassumption.
    eapply preord_env_P_inj_set; [| | eassumption ]. 
    eapply preord_env_P_inj_antimon; eauto.
    rewrite occurs_free_Eproj. now apply Included_Union_r. eassumption.
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
      eapply preord_env_P_inj_set; [| | eassumption ]. 
      eapply preord_env_P_inj_antimon; eauto.
      rewrite occurs_free_Eprim. now apply Included_Union_r.
      eauto. 
Qed.

Close Scope fun_scope.
Close Scope ctx_scope.