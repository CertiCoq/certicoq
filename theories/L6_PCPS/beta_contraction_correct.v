Require Import L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
Require Import identifiers.
Require Import L6.cps L6.size_cps L6.cps_util L6.eval L6.logical_relations L6.set_util
        L6.identifiers L6.alpha_conv L6.alpha_fresh L6.ctx L6.Ensembles_util L6.List_util
        L6.functions L6.beta_contraction L6.state.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Coq.Program.Wf.
Require Import Program.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.

Import ListNotations MonadNotation.
Open Scope monad_scope.

(** Used variables in an expression *)

Definition used_vars (e : exp) : Ensemble var := bound_var e :|: occurs_free e.
Definition used_vars_fundefs (fds : fundefs) : Ensemble var
  := bound_var_fundefs fds :|: occurs_free_fundefs fds.
Definition used_vars_ctx (c : exp_ctx) : Ensemble var
  := bound_var_ctx c :|: occurs_free_ctx c.
Definition used_vars_fundefs_ctx (f : fundefs_ctx) : Ensemble var
  := bound_var_fundefs_ctx f :|: occurs_free_fundefs_ctx f.

Lemma used_vars_dec: forall e, Decidable (used_vars e).
Proof.
  intros e.
  apply Decidable_Union.
  apply bound_var_dec.
  apply Decidable_occurs_free.
Qed.

Lemma used_vars_fundefs_dec: forall fds, Decidable (used_vars_fundefs fds).
Proof.
  intros fds.
  apply Decidable_Union.
  apply bound_var_fundefs_dec.
  apply Decidable_occurs_free_fundefs.
Qed.

Lemma used_vars_ctx_dec: forall e, Decidable (used_vars_ctx e).
Proof.
  intros e.
  apply Decidable_Union.
  apply bound_var_ctx_dec.
  apply Decidable_occurs_free_ctx.
Qed.

Lemma used_vars_fundefs_ctx_dec: forall fds, Decidable (used_vars_fundefs_ctx fds).
Proof.
  intros fds.
  apply Decidable_Union.
  apply bound_var_fundefs_ctx_dec.
  apply Decidable_occurs_free_fundefs_ctx.
Qed.

(** Useful tactics for terms involving Ensembles *)

Lemma Decidable_not_not : forall {A} (S : Ensemble A),
  Decidable S -> forall a,
  ~ ~ In _ S a <-> In _ S a.
Proof.
  intros A S HS a;
  destruct HS as [HS];
  specialize HS with (x := a);
  destruct HS as [HS|HS];
  split; easy.
Qed.

Lemma Union_demorgan : forall {A} (l r : Ensemble A) a,
  ~ In _ (l :|: r) a <-> ~ In _ l a /\ ~ In _ r a.
Proof.
  split; intros.
  - split; intros contra; contradiction H.
    now left. now right.
  - destruct H. intros contra. inv contra; congruence.
Qed.

Lemma Disjoint_Singleton_In : forall {A} S a,
  Decidable S -> Disjoint A S [set a] <-> ~ In _ S a.
Proof.
  split; intros H.
  - inv H; specialize H0 with (x := a).
    destruct X; destruct (Dec a); [|easy].
    contradiction H0; constructor; easy.
  - constructor.
    intros x contra; inv contra.
    now inv H1.
Qed.

Lemma not_Disjoint_Singleton_In : forall {A} S a,
  Decidable S -> ~ Disjoint A S [set a] <-> In _ S a.
Proof.
  split; [intros H|inversion 2; eapply H0; eauto].
  destruct X; destruct (Dec a); [easy|].
  contradiction H; constructor; intros.
  intros contra; destruct contra.
  inv H1.
  contradiction.
Qed.

Lemma Ensemble_iff_In_iff : forall {A} (S1 S2 : _ A),
  (S1 <--> S2) <-> (forall a, In _ S1 a <-> In _ S2 a).
Proof.
  split; intros.
  now rewrite H.
  unfold Same_set, Included.
  firstorder.
Qed.

Lemma In_or_Iff_Union : forall {A} (a : A) S1 S2,
  In _ (S1 :|: S2) a <-> In _ S1 a \/ In _ S2 a.
Proof. split; intros; destruct H; auto. Qed.

Ltac normalize_Ensemble' :=
  (* Right associative rewrites on _ :|: _ *)
  repeat rewrite <- Union_assoc; 
  repeat lazymatch goal with
  | |- context [ Empty_set _ :|: ?S ] => rewrite Union_Empty_set_neut_l
  end;
  (* Left associative rewrites on _ :|: _ *)
  repeat rewrite Union_assoc;
  repeat lazymatch goal with
  | |- context [ ?S :|: Empty_set _ ] => rewrite Union_Empty_set_neut_r
  end;
  (* Right associative rewrites on _ :&: _ *)
  repeat rewrite <- Intersection_assoc; 
  repeat lazymatch goal with
  | |- context [ Empty_set _ :&: ?S ] => rewrite Intersection_Empty_set_abs_l
  end;
  (* Left associative rewrites on _ :&: _ *)
  repeat rewrite Intersection_assoc;
  repeat lazymatch goal with
  | |- context [ ?S :&: Empty_set _ ] => rewrite Intersection_Empty_set_abs_r
  end.

Lemma Empty_set_In_false : forall A x, In A (Empty_set A) x <-> False.
Proof. split; intros; destruct H; auto. Qed.

Lemma In_and_Iff_Intersection : forall {A} (a : A) S1 S2,
  In _ (S1 :&: S2) a <-> In _ S1 a /\ In _ S2 a.
Proof. split; intros; destruct H; auto. Qed.

Lemma Intersection_demorgan : forall {A} (l r : Ensemble A) a,
  Decidable l -> Decidable r ->
  ~ In _ (l :&: r) a <-> ~ In _ l a \/ ~ In _ r a.
Proof.
  intros ? ? ? ? Hdec1 Hdec2; split; intros; destruct Hdec1 as [Hdec1]; destruct Hdec2 as [Hdec2].
  - destruct (Hdec1 a); destruct (Hdec2 a); try solve [now left | now right].
    contradiction H; now split.
  - destruct H; intros H1; destruct H1; auto.
Qed.

Lemma Setminus_andnot : forall {A} (l r : Ensemble A) a,
  In _ (l \\ r) a <-> In _ l a /\ ~ In _ r a.
Proof. unfold Setminus; split; intros; destruct H; auto. Qed.

Lemma Singleton_In : forall {A} (x a : A), In _ [set x] a <-> x = a.
Proof. split; intros; destruct H; auto. Qed.

Lemma Singleton_not_In : forall {A} (x a : A), ~ In _ [set x] a <-> x <> a.
Proof. split; intros; intros contra; inv contra; contradiction H; auto. Qed.

Lemma Union_Disjoint_split : forall {A} (S1 S2 S3 : Ensemble A),
  Disjoint _ (S1 :|: S2) S3 <-> Disjoint _ S1 S3 /\ Disjoint _ S2 S3.
Proof.
  split; intros; eauto with Ensembles_DB.
  apply Union_Disjoint_l; intuition.
Qed.

Check Disjoint_Singleton_In.

Ltac decidable_predicate p :=
  lazymatch p with
  | used_vars => idtac
  | bound_var => idtac
  | occurs_free => idtac
  | _ => fail
  end.

Ltac it_is_decidable :=
  apply used_vars_dec || apply bound_var_dec || apply Decidable_occurs_free.

(** Convert a Prop involving Ensembles into a logical formula involving In *)
Ltac Ensembles_to_logic' :=
  (* Unfold \subset *)
  lazymatch goal with
  | |- _ \subset _ =>
    unfold Included;
    let elt := fresh "elt" in
    intros elt
  | _ => idtac
  end;
  unfold Included;
  (* Easy cases that might show up while performing other simplifications *)
  let easy_cases := (
    repeat rewrite Empty_set_In_false; (* x ∈ ∅ ~~> ⊥ *)
    repeat rewrite Singleton_not_In; (* x ∉ {y} ~~> x <> y *)
    repeat rewrite Singleton_In (* x ∈ {y} ~~> x = y *)
  ) in
  (* Simplify ∉s first to avoid double negation *)
  repeat (
    easy_cases;
    repeat rewrite Setminus_andnot; (* x ∈ S \ T ~~> x ∈ S /\ S ∉ T *)
    repeat rewrite Union_demorgan; (* x ∉ S ∪ T ~~> x ∉ S /\ S ∉ T *)
    repeat match goal with 
    (* x ∉ S ∩ T ~~> S ∉ S \/ S ∉ T if S and T are Decidable *)
    | |- context [ ~ In _ (?f ?S :&: ?g ?T) _ ] =>
      decidable_predicate f;
      decidable_predicate g;
      rewrite (Intersection_demorgan (f S) (g T)) by it_is_decidable
    (* Disjoint (S ∪ T) V ~~> Disjoint S V /\ Disjoint T V *)
    | |- context [ Disjoint _ (?S1 :|: ?S2) ?S3 ] => rewrite (Union_Disjoint_split S1 S2 S3)
    (* Disjoint S {x} ~~> x ∉ S if S is decidable *)
    | |- context [ Disjoint (?f ?S) [set ?x] ] =>
      decidable_predicate f;
      rewrite (Disjoint_Singleton_In (f S)) by it_is_decidable
    (* ~ Disjoint S {x} ~~> x ∈ S if S is decidable *)
    | |- context [ ~ Disjoint (?f ?S) [set ?x] ] =>
      decidable_predicate f;
      rewrite (not_Disjoint_Singleton_In (f S)) by it_is_decidable
    end);
  (* Simplify ∈s *)
  repeat (
    easy_cases;
    repeat rewrite Setminus_andnot; (* x ∈ S \ T ~~> x ∈ S /\ S ∉ T *)
    repeat rewrite In_or_Iff_Union; (* x ∈ S ∪ T ~~> x ∈ S \/ S ∈ T *)
    repeat rewrite In_and_Iff_Intersection); (* x ∈ S ∩ T ~~> x ∈ S /\ S ∈ T *)
  idtac.

(** Simplifying expressions involving used variables
    TODO: put this in a new file vars_util.v *)

(* All variables in a list are distinct and disjoint from some set of used vars *)
Definition fresh_copies (s : Ensemble var) (l : list var) : Prop
  := Disjoint _ s (FromList l) /\ NoDup l.

Ltac split_var_eq a b :=
  destruct (PS.Raw.MX.eq_dec a b).

Ltac split_var_in_list a l :=
  destruct (in_dec PS.Raw.MX.eq_dec a l).

Ltac split_var_in_fundefs a fds Hfds :=
  destruct (Decidable_name_in_fundefs fds) as [Hfds]; destruct (Hfds a).

Local Ltac solve_bound_cases a v l := 
  split_var_eq a v; split_var_in_list a l;
  [ right; now constructor
  | left; subst a; constructor
  | right; now constructor
  | right].

Lemma used_vars_subset_mut :
  (forall c, (fun c => forall e, used_vars e \subset used_vars (c |[ e ]|)) c) /\
  (forall f, (fun f => forall e, used_vars e \subset used_vars_fundefs (f <[ e ]>)) f).
Proof with eauto with Ensembles_DB.
  exp_fundefs_ctx_induction IHe IHf; simpl; try rename e into c.
  - (* Hole_c *) easy...
  - (* Econstr_c *)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
    destruct Ha; [left; now constructor|].
    solve_bound_cases x v l.
    apply Free_Econstr2; auto.
  - (* Eproj_c *)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
    destruct Ha; [left; now constructor|].
    split_var_eq x v; [left|right].
    subst x; constructor.
    constructor; auto.
  - (* Eletapp_c *)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
    destruct Ha; [left; now constructor|].
    split_var_eq x v; [left|right].
    subst x; constructor.
    apply Free_Eletapp2; auto.
  - (* Eprim_c *)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
    destruct Ha; [left; now constructor|].
    solve_bound_cases x v l.
    apply Free_Eprim2; auto.
  - (* Efun1_c *)
    intros l0 e; eapply Included_trans; [apply IHe|]; intros a Ha.
    unfold used_vars.
    rewrite bound_var_Ecase_app.
    rewrite occurs_free_Ecase_app.
    destruct Ha; [|auto..].
    repeat rewrite <- Union_assoc.
    rewrite Union_commut.
    repeat rewrite <- Union_assoc.
    apply Union_introl.
    econstructor; [eassumption|now constructor].
  - (* Efun2_c *)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
    destruct Ha; [left; now apply Bound_Efun2|].
    split_var_in_fundefs x f4 Hf4; [left|right].
    constructor; now apply name_in_fundefs_bound_var_fundefs.
    now constructor.
  - (* Fcons1_c *)
    intros e; eapply Included_trans; [apply IHf|]; intros a Ha. 
    destruct Ha; [left; now constructor|].
    split_var_in_fundefs x (f5 <[ e ]>) Hf5; [left|right].
    constructor; now apply name_in_fundefs_bound_var_fundefs.
    now constructor.
  - (* Fcons2_c*)
    intros e; eapply Included_trans; [apply IHe|]; intros a Ha. 
    destruct Ha; [left; now constructor|].
    split_var_eq x v; split_var_in_list x l.
    left... left; subst x... left...
    split_var_in_fundefs x f6 Hf6.
    left; apply Bound_Fcons2; now apply name_in_fundefs_bound_var_fundefs.
    right; constructor; assumption.
  - (* Fcons3_c *)
    intros e; eapply Included_trans; [apply IHf|]; intros a Ha. 
    destruct Ha; [left; now constructor|].
    split_var_eq x v; split_var_in_list x l.
    left... left; subst x... left...
    split_var_in_fundefs x (f7 <[ e ]>) Hf7.
    left; apply Bound_Fcons2; now apply name_in_fundefs_bound_var_fundefs.
    right; constructor; assumption.
Qed.

Corollary used_vars_subset : forall c e, 
  used_vars e \subset used_vars (c |[ e ]|).
Proof. apply used_vars_subset_mut. Qed.

Corollary used_vars_subset_fundefs_ctx : forall f e, 
  used_vars e \subset used_vars_fundefs (f <[ e ]>).
Proof. apply used_vars_subset_mut. Qed.

Definition eq_var := Pos.eqb.

(* Returns true iff [k] is in [xs]. *)
Fixpoint occurs_in_vars (k:var) (xs:list var) : bool :=
  match xs with
  | nil => false
  | x::xs1 => eq_var k x || occurs_in_vars k xs1
  end.

(* Returns true iff [k] occurs (at all) within the expression [e] *)
Fixpoint occurs_in_exp (k:var) (e:exp) : bool :=
  match e with
  | Econstr z _ xs e1 =>
    eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
  | Ecase x arms =>
    eq_var k x ||
            (fix occurs_in_arms (arms: list (ctor_tag * exp)) : bool :=
               match arms with
               | nil => false
               | p::arms1 => match p with
                             | (_,e) => occurs_in_exp k e || occurs_in_arms arms1
                             end
               end) arms
  | Eproj z _ _ x e1 =>
    eq_var z k || eq_var k x || occurs_in_exp k e1
  | Eletapp z f _ xs e1 =>
    eq_var z k || eq_var f k || occurs_in_vars k xs || occurs_in_exp k e1
  | Efun fds e =>
    occurs_in_fundefs k fds || occurs_in_exp k e
  | Eapp x _ xs => eq_var k x || occurs_in_vars k xs
  | Eprim z _ xs e1 =>
    eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
  | Ehalt x => eq_var x k
  end
(* Returns true iff [k] occurs within the function definitions [fds] *)
with occurs_in_fundefs (k:var) (fds:fundefs) : bool :=
       match fds with
       | Fnil => false
       | Fcons z _ zs e fds1 =>
         eq_var z k || occurs_in_vars k zs || occurs_in_exp k e ||
                 occurs_in_fundefs k fds1
       end.

Lemma occurs_in_vars_correct : forall a l, occurs_in_vars a l = true <-> List.In a l.
Proof.
  induction l; [firstorder|].
  destruct (Pos.eqb_spec a a0); subst.
  simpl; rewrite Pos.eqb_refl; simpl; split; intros; [now left|easy].
  simpl; rewrite <- Pos.eqb_neq in n; unfold eq_var; rewrite n; simpl.
  rewrite IHl.
  split; [intros H; now right|intros [contra|H]]; [|assumption].
  rewrite Pos.eqb_neq in n; congruence.
Qed.

Corollary occurs_in_vars_correct_neq : forall a l, occurs_in_vars a l = false <-> ~ List.In a l.
Proof.
  assert (forall a, a = false <-> ~ (a = true)). {
    split; intros Ha.
    - intros Hcontra; congruence.
    - destruct a; [congruence|reflexivity].
  } 
  intros; rewrite H.
  apply not_iff_compat.
  apply occurs_in_vars_correct.
Qed.

Lemma negb_not : forall a b, a = negb b <-> a <> b.
Proof. destruct a; destruct b; firstorder. Qed.

Lemma find_def_is_Some_occurs_free_fundefs : forall f fds t xs e a,
  find_def f fds = Some (t, xs, e) ->
  occurs_free e a ->
  ~ List.In a xs ->
  ~ name_in_fundefs fds a ->
  occurs_free_fundefs fds a.
Proof.
  induction fds; simpl; intros; [|now contradiction H2].
  destruct (M.elt_eq f v); [subst; inv H|].
  - constructor; auto; intros contra; subst; contradiction H2; [now left|now right].
  - apply Free_Fcons2; [|intros contra; subst; contradiction H2; now left].
    eapply IHfds; eauto.
    intros contra; subst; contradiction H2; now right.
Qed.

Hint Resolve Union_demorgan.
Hint Resolve negb_not.
Hint Resolve Disjoint_Singleton_In.
Hint Resolve not_Disjoint_Singleton_In.
Hint Resolve used_vars_dec.
Hint Resolve used_vars_fundefs_dec.
Hint Resolve bound_var_dec.
Hint Resolve bound_var_fundefs_dec.
Hint Resolve Decidable_occurs_free.
Hint Resolve Decidable_occurs_free_fundefs.
Hint Resolve Decidable_Union.
Hint Resolve Decidable_Intersection.
Hint Resolve Decidable_Setminus.
Hint Resolve Decidable_singleton_var.
Hint Resolve Decidable_FromList.
Hint Resolve Decidable_occurs_free.
Hint Resolve name_in_fundefs_bound_var_fundefs.
Hint Constructors Union.
Hint Constructors or.

Local Ltac simplify_boolean_exprs := 
  simpl in *;
  repeat rewrite orb_false_r in *;
  repeat rewrite orb_true_r in *;
  simpl in *.

Local Ltac rewrite_trivial_iffs :=
  repeat match goal with
  | [ Heq : ?a <-> ?b, Ha : ?a |- _ ] => (assert b by now rewrite <- Heq); clear Heq
  | [ Heq : ?a <-> ?b |- ?a ] => rewrite Heq
  | [ Heq : true = false <-> ~ In var ?S ?a |- _ ] =>
      apply not_iff_compat in Heq;
      rewrite <- negb_not in Heq;
      (rewrite Decidable_not_not in Heq; [|auto]);
      (assert (In var S a) by now rewrite <- Heq); clear Heq
  | [ Heq : false = false <-> In var ?S ?a |- _ ] =>
      (assert (In var S a) by now rewrite <- Heq); clear Heq
  | [ Heq : false = false <-> ~ In var ?S ?a |- _ ] => 
      (assert (~ In var S a) by now rewrite <- Heq); clear Heq
  end.

Local Ltac eliminate_singleton_disjoints :=
  repeat match goal with
  | [ Hin : _ = _ <-> Disjoint _ _ [set _] |- _ ] =>
      rewrite Disjoint_Singleton_In in Hin; [|auto]
  | [ Hin : _ = _ <-> ~ Disjoint _ _ [set _] |- _ ] =>
      rewrite not_Disjoint_Singleton_In in Hin; [|auto]
  | [ Hin : Disjoint _ _ [set _] |- _ ] =>
      rewrite Disjoint_Singleton_In in Hin; [|auto]
  | [ Hin : ~ Disjoint _ _ [set _] |- _ ] =>
      rewrite not_Disjoint_Singleton_In in Hin; [|auto]
  end;
  try (rewrite Disjoint_Singleton_In; [|auto]);
  try (rewrite not_Disjoint_Singleton_In; [|auto]).

Local Ltac demorgan_not_used_vars :=
  repeat match goal with
  | [ Hin : ~ In var (used_vars _) _ |- _ ] =>
      unfold used_vars in Hin;
      rewrite Union_demorgan in Hin;
      destruct Hin
  | [ Hin : ~ In var (used_vars_fundefs _) _ |- _ ] =>
      unfold used_vars_fundefs in Hin;
      rewrite Union_demorgan in Hin;
      destruct Hin
  end.

Local Ltac cleanup :=
  try (rewrite occurs_in_vars_correct in *);
  try (rewrite occurs_in_vars_correct_neq in *);
  simplify_boolean_exprs;
  eliminate_singleton_disjoints;
  rewrite_trivial_iffs;
  demorgan_not_used_vars.

Local Ltac super_destruct e Hvar :=
  destruct e eqn:Hvar;
  simpl in *;
  try rewrite Hvar in *;
  try (rewrite Pos.eqb_eq in Hvar; subst);
  try (rewrite Pos.eqb_neq in Hvar);
  cleanup;
  try congruence.

Local Ltac inv_all :=
  repeat match goal with
  | [ H : In var _ _ |- _ ] => inv H
  | [ H : List.In _ _ |- _ ] => inv H
  | [ H : (_, _) = (_, _) |- _ ] => inv H
  end;
  eauto with Ensembles_DB.

Ltac crush_occurs_in_exp_mut :=
  repeat normalize_bound_var; repeat normalize_occurs_free; Ensembles_to_logic'; firstorder.

Lemma occurs_in_exp_correct_mut : forall x,
  (forall e, (fun e => occurs_in_exp x e = false <-> Disjoint _ (used_vars e) [set x]) e) /\
  (forall f, (fun f => occurs_in_fundefs x f = false <-> Disjoint _ (used_vars_fundefs f) [set x]) f).
Proof.
  intros x.
  apply exp_def_mutual_ind.
  - (* Econstr *)
    simpl; intros v t l e He1; split; intros H.
    + super_destruct (eq_var v x) Hvar.
      super_destruct (occurs_in_vars x l) Hvars.
      intros contra; inv_all.
    + super_destruct (eq_var v x) Hvar.
      contradiction H; constructor.
      super_destruct (occurs_in_vars x l) Hvars.
      contradiction H0; now constructor.
      unfold used_vars; revert H H0; crush_occurs_in_exp_mut.
  - (* Ecase [] *)
    simpl; intros v; split; intros H; super_destruct (eq_var x v) Hvar.
    + intros contra; inv_all.
    + contradiction H0; constructor.
  - (* Ecase :: *)
    simpl; intros v l c e He IHl; split; intros H.
    + super_destruct (eq_var x v) Hvar.
      super_destruct (occurs_in_exp x e) Hexp.
      intros contra; inv_all.
    + super_destruct (eq_var x v) Hvar.
      contradiction H1; constructor.
      super_destruct (occurs_in_exp x e) Hexp.
      inv H1.
      contradiction H; econstructor; [eassumption|now constructor].
      contradiction H0; now constructor.
      intros contra; inv_all.
      contradiction H; econstructor; [|right]; eassumption.
  - (* Eproj *)
    simpl; intros v t n v0 e He; split; intros H.
    + super_destruct (eq_var v x) Hvar.
      super_destruct (eq_var x v0) Hvar'.
      intros contra; inv_all.
    + super_destruct (eq_var v x) Hvar.
      super_destruct (occurs_in_exp x e) Hexp; try (contradiction H; constructor).
      super_destruct (eq_var x v0) Hvar'.
      contradiction H0; constructor.
      unfold used_vars; revert H H0; crush_occurs_in_exp_mut.
  - (* Eletapp *)
    simpl; intros x0 f ft ys e; split; intros H'.
    + super_destruct (eq_var x0 x) Hvar.
      super_destruct (eq_var f x) Hvar'.
      super_destruct (occurs_in_exp x e) He.
      super_destruct (occurs_in_vars x ys) Hys.
      unfold used_vars; revert H H0; crush_occurs_in_exp_mut.
    + super_destruct (eq_var x0 x) Hvar; auto; [revert H0 H1; crush_occurs_in_exp_mut|].
      super_destruct (eq_var f x) Hvar'; auto; [revert H0 H1; crush_occurs_in_exp_mut|].
      super_destruct (occurs_in_vars x ys) Hys; auto; [revert H0 H1; crush_occurs_in_exp_mut|].
      unfold used_vars; revert H0 H1; crush_occurs_in_exp_mut.
  - (* Efun *)
    simpl; intros fds Hfds e He; split; intros H. 
    + super_destruct (occurs_in_exp x e) Hexp.
      super_destruct (occurs_in_fundefs x fds) Hfds'.
      intros contra; inv_all.
    + super_destruct (occurs_in_exp x e) Hexp.
      inv H0.
      contradiction H; now apply Bound_Efun2.
      super_destruct (occurs_in_fundefs x fds) Hfds'.
      inv H0.
      contradiction H; now constructor.
      contradiction H1; eauto.
      contradiction H1; apply Free_Efun1; [|assumption].
      intros contra; now apply name_in_fundefs_bound_var_fundefs in contra.
      intros contra; inv contra.
      contradiction H; now constructor.
      contradiction H2; now apply Free_Efun2.
  - (* Eapp *)
    simpl; intros v t l; split; intros H.
    + super_destruct (eq_var x v) Hvar.
      intros contra; inv contra; inv_all.
    + super_destruct (eq_var x v) Hvar.
      contradiction H0; constructor.
      eauto.
  - (* Eprim *)
    simpl; intros v p l e He; split; intros H.
    + super_destruct (eq_var v x) Hvar.
      super_destruct (occurs_in_vars x l) Hvars.
      intros contra; inv_all.
    + super_destruct (eq_var v x) Hvar.
      contradiction H; constructor.
      super_destruct (occurs_in_vars x l) Hvars.
      contradiction H0; now constructor.
      unfold used_vars; revert H H0; crush_occurs_in_exp_mut.
  - (* Ehalt *)
    simpl; intros v; split; intros H; super_destruct (eq_var v x) Hvar.
    intros contra; inv_all.
    contradiction H0; constructor.
  - (* Fcons *)
    simpl; intros v t l e He1 fd Hfd1; split; intros H.
    + super_destruct (eq_var v x) Hvar.
      super_destruct (occurs_in_vars x l) Hvars.
      super_destruct (occurs_in_exp x e) Hexp.
      intros contra; inv_all.
    + super_destruct (eq_var v x) Hvar.
      contradiction H; constructor; now left.
      super_destruct (occurs_in_vars x l) Hvars.
      contradiction H; constructor; now right.
      super_destruct (occurs_in_exp x e) Hexp.
      inv H1.
      contradiction H; now apply Bound_Fcons3.
      contradiction H0; constructor; eauto.
      intros contra; apply name_in_fundefs_bound_var_fundefs in contra.
      contradiction H; now apply Bound_Fcons2.
      intros contra; inv contra.
      contradiction H. now apply Bound_Fcons2.
      contradiction H0; apply Free_Fcons2; auto.
  - (* Fnil *)
    cleanup; split; [intros _ contra; inv_all|easy].
Qed.

Corollary occurs_in_exp_correct : forall x e,
  occurs_in_exp x e = false <-> Disjoint _ (used_vars e) [set x].
Proof. apply occurs_in_exp_correct_mut. Qed.

Corollary occurs_in_fundefs_correct : forall x f,
  occurs_in_fundefs x f = false <-> Disjoint _ (used_vars_fundefs f) [set x].
Proof. apply occurs_in_exp_correct_mut. Qed.

Corollary occurs_in_exp_iff_used_vars : forall e a,
  occurs_in_exp a e = true <-> In _ (used_vars e) a.
Proof.
  intros.
  rewrite <- Decidable_not_not; auto.
  replace true with (negb false); auto.
  rewrite negb_not.
  apply not_iff_compat.
  rewrite <- Disjoint_Singleton_In; auto.
  apply occurs_in_exp_correct.
Qed.

Corollary not_occurs_in_exp_iff_used_vars : forall e a,
  occurs_in_exp a e = false <-> ~ In _ (used_vars e) a.
Proof. intros. rewrite <- Disjoint_Singleton_In; auto. apply occurs_in_exp_correct. Qed.

Corollary occurs_in_fundefs_iff_used_vars_fundefs : forall e a,
  occurs_in_fundefs a e = true <-> In _ (used_vars_fundefs e) a.
Proof.
  intros.
  rewrite <- Decidable_not_not; auto.
  replace true with (negb false); auto.
  rewrite negb_not.
  apply not_iff_compat.
  rewrite <- Disjoint_Singleton_In; auto.
  apply occurs_in_fundefs_correct.
Qed.

Corollary not_occurs_in_fundefs_iff_used_vars_fundefs : forall e a,
  occurs_in_fundefs a e = false <-> ~ In _ (used_vars_fundefs e) a.
Proof. intros. rewrite <- Disjoint_Singleton_In; auto. apply occurs_in_fundefs_correct. Qed.

Lemma eq_var_iff_Singleton_l : forall b a, eq_var a b = true <-> In _ [set a] b.
Proof.
  split; intros H; destruct (eq_var a b) eqn:Heq; try congruence.
  rewrite Peqb_eq in Heq; now subst.
  rewrite Pos.eqb_neq in Heq; contradiction Heq; now inv H.
Qed.

Lemma eq_var_iff_Singleton_r : forall a b, eq_var a b = true <-> In _ [set b] a.
Proof.
  split; intros H; destruct (eq_var a b) eqn:Heq; try congruence.
  rewrite Peqb_eq in Heq; now subst.
  rewrite Pos.eqb_neq in Heq; contradiction Heq; now inv H.
Qed.

Ltac translate_used_vars_to_firstorder a :=
  repeat (
    repeat rewrite <- occurs_in_exp_iff_used_vars in *; simpl in *;
    repeat rewrite <- occurs_in_fundefs_iff_used_vars_fundefs in *; simpl in *;
    repeat rewrite orb_true_iff in *;
    repeat rewrite (eq_var_iff_Singleton_r a) in *;
    repeat rewrite (eq_var_iff_Singleton_l a) in *;
    repeat rewrite occurs_in_vars_correct in *;
    repeat rewrite occurs_in_exp_iff_used_vars in *;
    repeat rewrite occurs_in_fundefs_iff_used_vars_fundefs in *;
    repeat rewrite In_or_Iff_Union in *
  ).

Local Ltac solve_used_vars_lemma :=
  intros;
  rewrite Ensemble_iff_In_iff; intros a;
  translate_used_vars_to_firstorder a;
  firstorder.

Lemma used_vars_Econstr : forall x c args e,
  used_vars (Econstr x c args e) <--> x |: FromList args :|: used_vars e.
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Ecase_nil : forall x,
  used_vars (Ecase x []) <--> [set x].
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Ecase_cons : forall x c e arms,
  used_vars (Ecase x ((c, e) :: arms)) <--> used_vars e :|: used_vars (Ecase x arms).
Proof.
  induction arms.
  - intros; rewrite Ensemble_iff_In_iff; intros a.
    translate_used_vars_to_firstorder a.
    firstorder.
  - destruct a; rewrite Ensemble_iff_In_iff; intros a.
    translate_used_vars_to_firstorder a.
    clear IHarms; firstorder.
Qed.

Lemma used_vars_Eproj : forall x c n y e,
  used_vars (Eproj x c n y e) <--> x |: (y |: used_vars e).
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Efun : forall fds e,
  used_vars (Efun fds e) <--> used_vars_fundefs fds :|: used_vars e.
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Eapp: forall f t args,
  used_vars (Eapp f t args) <--> f |: FromList args.
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Eprim : forall x p args e,
  used_vars (Eprim x p args e) <--> x |: FromList args :|: used_vars e.
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Ehalt : forall x, used_vars (Ehalt x) <--> [set x].
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Fcons : forall f t v e fds,
  used_vars_fundefs (Fcons f t v e fds) <-->
  f |: FromList v :|: used_vars e :|: used_vars_fundefs fds.
Proof. solve_used_vars_lemma. Qed.

Lemma used_vars_Fnil : used_vars_fundefs Fnil <--> Empty_set _.
Proof. solve_used_vars_lemma. Qed.

Ltac normalize_used_vars := 
  match goal with
  | |- context [ used_vars (Econstr _ _ _ _) ] => rewrite used_vars_Econstr
  | |- context [ used_vars (Eproj _ _ _ _ _) ] => rewrite used_vars_Eproj
  | |- context [ used_vars (Ecase _ []) ] => rewrite used_vars_Ecase_nil
  | |- context [ used_vars (Ecase _ (_ :: _)) ] => rewrite used_vars_Ecase_cons
  | |- context [ used_vars (Efun _ _) ] => rewrite used_vars_Efun
  | |- context [ used_vars (Eapp _ _ _) ] => rewrite used_vars_Eapp
  | |- context [ used_vars (Eprim _ _ _ _) ] => rewrite used_vars_Eprim
  | |- context [ used_vars (Ehalt _) ] => rewrite used_vars_Ehalt
  | |- context [ used_vars_fundefs (Fcons _ _ _ _ _) ] => rewrite used_vars_Fcons
  | |- context [ used_vars_fundefs Fnil ] => rewrite used_vars_Fnil
  | [ H : context [ used_vars (Econstr _ _ _ _)         ] |- _ ] => rewrite used_vars_Econstr in H
  | [ H : context [ used_vars (Eproj _ _ _ _ _)         ] |- _ ] => rewrite used_vars_Eproj in H
  | [ H : context [ used_vars (Ecase _ [])              ] |- _ ] => rewrite used_vars_Ecase_nil in H
  | [ H : context [ used_vars (Ecase _ (_ :: _))        ] |- _ ] => rewrite used_vars_Ecase_cons in H
  | [ H : context [ used_vars (Efun _ _)                ] |- _ ] => rewrite used_vars_Efun in H
  | [ H : context [ used_vars (Eapp _ _ _)              ] |- _ ] => rewrite used_vars_Eapp in H
  | [ H : context [ used_vars (Eprim _ _ _ _)           ] |- _ ] => rewrite used_vars_Eprim in H
  | [ H : context [ used_vars (Ehalt _)                 ] |- _ ] => rewrite used_vars_Ehalt in H
  | [ H : context [ used_vars_fundefs (Fcons _ _ _ _ _) ] |- _ ] => rewrite used_vars_Fcons in H
  | [ H : context [ used_vars_fundefs Fnil              ] |- _ ] => rewrite used_vars_Fnil in H
  end.

(** Now that we have used vars, we can make tactics on Ensembles that work with used_vars *)

Ltac normalize_vars :=
  (* Rewrite single terms *)
  repeat (normalize_used_vars || normalize_bound_var || normalize_occurs_free).

Ltac normalize_Ensemble :=
  normalize_vars;
  repeat lazymatch goal with
  | |- context [ FromList [] ] => rewrite FromList_nil
  | |- context [ FromList (_ :: _) ] => rewrite FromList_cons
  end;
  normalize_Ensemble'.

Ltac Ensembles_to_logic := normalize_Ensemble; Ensembles_to_logic'.

(** Solve goals of the form
     preord_env_P pr cenv S k rho rho'
    -----------------------------------
     preord_env_P pr cenv T k rho rho'
    
    where "obviously" S \subset T *)
Ltac preord_env_P_antimon :=
  eapply preord_env_P_antimon; [eassumption|];
  Ensembles_to_logic; intuition assumption.

Goal forall f g (x : var) (S T : Ensemble var) (e1 : exp) e2,
    ~ In _ (f S :|: g T) x /\ ~ In _ (used_vars e2 :&: used_vars e2) x.
Proof.
  intros.
  Ensembles_to_logic.
Abort.

(** Some convenient tactics for goals about \subset
    Assumes goal of the form S1 :|: ... :|: Sn \subset T1 :|: ... :|: Tm *)

(* Trivial cases: S \subset S and Empty_set \subset S *)
Ltac trivial_subset :=
  match goal with
  | |- ?S \subset ?S => apply Included_refl
  | |- Empty_set _ \subset ?S => apply Included_Empty_set 
  end.

Goal forall A (P Q R : Ensemble A), P :|: Q :|: R \subset P :|: R :|: Q.
  intros.
  Ensembles_to_logic.
  firstorder assumption.
Abort.

Section beta_contraction_correct.

Context {St : Type} {IH : InlineHeuristic St}.
Context {pr : prims} {cenv : ctor_env} {P : Post} {PG : PostG}.

Definition extend_with (sig : M.t var) (rho : env) : env :=
  let fix go xys :=
    match xys with
    | [] => rho
    | (x, y) :: xys' =>
      match M.get y rho with
      | Some v => M.set x v (go xys')
      | None => M.remove x (go xys')
      end
    end
  in go (M.elements sig).

Lemma option_not_exists_None : forall {A} {lhs : option A}, (~ exists x, lhs = Some x) <-> lhs = None.
Proof.
  split.
  - destruct lhs; intros; auto.
    exfalso; apply H; now exists a.
  - intros; subst; intros [? H]; inversion H.
Qed.

Lemma contrapositive : forall {P Q : Prop}, (P -> Q) -> (~ Q -> ~ P). Proof. tauto. Qed.

Lemma of_list_None_not_In {A} {xys : list (var * A)} {x} :
  M.get x (Maps.PTree_Properties.of_list xys) = None -> ~ List.In x (map fst xys).
Proof.
  rewrite <- option_not_exists_None.
  apply contrapositive.
  apply Maps.PTree_Properties.of_list_dom.
Qed.

Lemma split_map_fst : forall {A B} {xys : list (A * B)}, fst (split xys) = map fst xys.
Proof.
  induction xys as [| [x y] xs' IH']; auto; simpl.
  destruct (split xs') eqn:Hsplit; simpl in *.
  now rewrite IH'.
Qed.

(* TODO copied from uncurry_correct.v *)
Fixpoint sizeof_exp e : nat :=
  match e with
  | Econstr x _ ys e => 1 + length ys + sizeof_exp e
  | Ecase x l =>
    (1 + (fix sizeof_l l :=
            match l with
              [] => 0
            | (t, e) :: l => 1 + sizeof_exp e + sizeof_l l
            end) l)%nat
  | Eproj x _ _ y e => 1 + sizeof_exp e
  | Efun fds e => 1 + sizeof_fundefs fds + sizeof_exp e
  | Eletapp x _ _ ys e => 1 + sizeof_exp e
  | Eapp x _ ys => 1 + length ys
  | Eprim x _ ys e => 1 + length ys + sizeof_exp e
  | Ehalt x => 1
  end
with sizeof_fundefs f : nat := 
  match f with
  | Fcons f t v e fds => 1 + sizeof_exp e + sizeof_fundefs fds
  | Fnil => 0
  end.


(** Extensional equality on environments *)

Definition map_ext_eq_inj {A} f (m n : M.t A) := forall x, M.get x m = M.get (f x) n.
Definition map_ext_eq {A} (m n : M.t A) := map_ext_eq_inj (fun x => x) m n.
Definition map_dom {A} (m : M.t A) : Ensemble positive := fun x => exists y, M.get x m = Some y.
Definition map_cod {A} (m : M.t A) : Ensemble A := fun y => exists x, M.get x m = Some y.

Lemma map_ext_eq_refl : forall {A} (m : M.t A), map_ext_eq m m.
Proof. unfold map_ext_eq, map_ext_eq_inj; intros; auto. Qed.

Lemma map_ext_eq_set : forall {A} (m n : M.t A) x y,
  map_ext_eq m n -> map_ext_eq (M.set x y m) (M.set x y n).
Proof.
  unfold map_ext_eq, map_ext_eq_inj; intros.
  split_var_eq x x0; subst; repeat (rewrite M.gss || rewrite M.gso); auto.
Qed.

Lemma map_ext_eq_get_list_subst : forall {A} (rho rho' : M.t A) xs,
  map_ext_eq rho rho' -> get_list xs rho = get_list xs rho'.
Proof.
  unfold map_ext_eq, map_ext_eq_inj; simpl; intros.
  induction xs; auto; simpl.
  rewrite H.
  destruct (M.get _ _); auto.
  now rewrite IHxs.
Qed.

(*
Section bstep_cost_subst.

Definition weak_value_eq v1 v2 :=
  match v1, v2 with
  | Vfun rho1 fds1 f1, Vfun rho2 fds2 f2 =>
    map_ext_eq rho1 rho2 /\ fds1 = fds2 /\ f1 = f2
  | v1, v2 => v1 = v2
  end.

Lemma weak_value_eq_refl : forall v, weak_value_eq v v.
Proof. unfold weak_value_eq; destruct v; intuition. apply map_ext_eq_refl. Qed.

Definition map_ext_weak_eq rho rho' := forall x,
  match M.get x rho, M.get x rho' with
  | Some v1, Some v2 => weak_value_eq v1 v2
  | None, None => True
  | _, _ => False
  end.

Lemma map_ext_weak_eq_set : forall m n x y,
  map_ext_weak_eq m n -> map_ext_weak_eq (M.set x y m) (M.set x y n).
Proof.
  unfold map_ext_weak_eq; intros.
  split_var_eq x x0; subst.
  - repeat rewrite M.gss.
    apply weak_value_eq_refl.
  - repeat rewrite M.gso; auto.
    destruct (M.get x0 m) eqn:Hx0m,
      (M.get x0 n) eqn:Hx0n;
      specialize H with (x := x0);
      rewrite Hx0m, Hx0n in H; auto.
Qed.

Lemma map_ext_weak_eq_get_list_subst' : forall rho rho' xs,
  map_ext_weak_eq rho rho' ->
  match get_list xs rho, get_list xs rho' with
  | Some vs1, Some vs2 => Forall2 weak_value_eq vs1 vs2
  | None, None => True
  | _, _ => False
  end.
Proof.
  unfold map_ext_weak_eq, map_ext_eq_inj; simpl; intros.
  induction xs; auto; simpl; try constructor.
  destruct (get_list xs rho) eqn:Hgetxs,
    (get_list xs rho') eqn:Hgetxs',
    (M.get a rho) eqn:Hgeta,
    (M.get a rho') eqn:Hgeta';
    specialize H with (x := a);
    rewrite Hgeta, Hgeta' in H;
    auto.
Qed.

Lemma map_ext_weak_eq_get_list_subst : forall rho rho' xs vs,
  map_ext_weak_eq rho rho' ->
  get_list xs rho = Some vs -> exists vs',
  get_list xs rho' = Some vs' /\ Forall2 weak_value_eq vs vs'.
Proof.
  intros.
  pose (H' := map_ext_weak_eq_get_list_subst' rho rho' xs).
  rewrite H0 in H'.
Admitted.

Lemma map_ext_eq_bstep_cost_subst : forall e rho rho' v c,
  map_ext_weak_eq rho rho' ->
  bstep_cost pr cenv rho e v c ->
  bstep_cost pr cenv rho' e v c.
Proof.
  intros e; remember (sizeof_exp e) as n.
  generalize dependent e; pattern n; apply lt_wf_ind; clear n.
  intros n IHn e He; intros; destruct e.
  Ltac a_constructor := 
    let cleanup :=
      first
        [ reflexivity
        | eassumption
        | lazymatch goal with
          | H : map_ext_eq _ _ |- M.get _ _ = Some _ =>
            rewrite H; eassumption
          end
        | erewrite map_ext_weak_eq_get_list_subst; eauto
        | idtac
        ]
    in
    first
      [ eapply BStepc_constr; cleanup
      | eapply BStepc_proj; cleanup
      | eapply BStepc_case; cleanup
      | eapply BStepc_app; cleanup
      | eapply BStepc_letapp; cleanup
      | eapply BStepc_fun; cleanup
      | eapply BStepc_prim; cleanup
      | eapply BStepc_halt; cleanup ].
  Ltac attack := 
    try lazymatch goal with H : bstep_cost _ _ _ _ _ _ |- _ => inv H end;
    a_constructor.
  Ltac apply_IH :=
    lazymatch reverse goal with
    | H : forall _, _ |- _ =>
      eapply H; eauto; try (simpl; omega)
    end;
    try apply map_ext_weak_eq_set; auto.
  - inv H0.
    eapply BStepc_constr.
    destruct (map_ext_weak_eq_get_list_subst rho rho' l vs) as [? [? ?]]; auto.
    eassumption.
    apply_IH. 
  - subst n; induction l.
    + attack. lazymatch goal with H : find_tag_nth [] _ _ _ |- _ => inv H end.
    + destruct a.
      lazymatch goal with H : bstep_cost _ _ _ _ _ _ |- _ => inv H end.
      lazymatch goal with H : find_tag_nth _ _ _ _ |- _ => inv H end.
      * a_constructor.
        constructor.
        apply_IH.
      * a_constructor.
        apply find_tag_lt; eauto.
        apply_IH.
        admit.
  - attack; apply_IH.
  - attack; apply_IH.
  - attack.
    admit.
  - attack; apply_IH.
  - attack; apply_IH.
  - attack.
Qed. 

End bstep_cost_subst.

Lemma map_ext_eq_preord_exp_subst : forall k rho1 rho2 rho1' rho2' e1 e2,
  map_ext_eq rho1 rho1' ->
  map_ext_eq rho2 rho2' ->
  preord_exp pr cenv k P PG (e1, rho1') (e2, rho2') ->
  preord_exp pr cenv k P PG (e1, rho1) (e2, rho2).
Proof.
  unfold preord_exp; intros. Abort.
 *)

Lemma extend_with_spec : forall sig rho, map_ext_eq_inj (apply_r sig) (extend_with sig rho) rho.
Proof.
  unfold map_ext_eq_inj, extend_with, apply_r; intros.
  rewrite <- Maps.PTree_Properties.of_list_elements with (m := sig).
  remember Maps.PTree_Properties.of_list as of_list eqn:Heqoflist.
  unfold var in *.
  remember (M.elements sig) as xys eqn:Heqxys.
  assert (Hnorepet : Coqlib.list_norepet (map fst xys)) by (subst xys; apply M.elements_keys_norepet).
  clear Heqxys.
  match goal with |- M.get x (?f xys) = _ => remember f as go end.
  assert (Hnotfound : forall x xys, ~ List.In x (map fst xys) -> M.get x (go xys) = M.get x rho). {
    revert Heqgo; clear; induction xys as [| [x' y'] xys' IH]; intros; subst go; auto.
    - assert (x <> x') by (intros contra; subst; contradiction H; now left).
      assert (~ List.In x (map fst xys')) by (intros contra; contradiction H; now right).
      destruct (M.get y' rho); [rewrite M.gso; auto|].
      rewrite M.gro; auto.
  }
  destruct (Maps.PTree.get x (of_list _ xys)) eqn:Hget.
  - subst of_list; apply Maps.PTree_Properties.in_of_list in Hget.
    induction xys as [| [x' y'] xys' IH']; [inversion Hget|].
    inversion Hnorepet; subst hd; subst tl.
    inversion Hget.
    + inversion H; subst x'; subst y'; clear H.
      rewrite Heqgo; rewrite <- Heqgo.
      destruct (M.get e rho) eqn:Hgete; [now rewrite M.gss|now rewrite M.grs].
    + assert (x <> x'). {
        intros contra; subst.
        apply in_split_l in H.
        rewrite split_map_fst in H.
        contradiction.
      }
      rewrite Heqgo; rewrite <- Heqgo.
      destruct (M.get y' rho).
      * rewrite M.gso by auto.
        rewrite IH'; auto.
      * rewrite M.gro by auto.
        rewrite IH'; auto.
  - subst of_list; apply of_list_None_not_In in Hget.
    rewrite Hnotfound; auto.
Qed.

Lemma set_extend_with_comm : forall x v sig rho,
  M.get x sig = None ->
  ~ In _ (map_cod sig) x ->
  map_ext_eq (M.set x v (extend_with sig rho)) (extend_with sig (M.set x v rho)).
Proof.
  unfold map_ext_eq, map_ext_eq_inj; intros.
  rewrite extend_with_spec.
  split_var_eq x x0; subst.
  - rewrite M.gss. unfold apply_r. unfold var, M.elt in *; rewrite H. now rewrite M.gss.
  - rewrite M.gso; auto. rewrite extend_with_spec.
    assert (apply_r sig x0 <> x). {
      intros contra.
      contradiction H0.
      rewrite <- contra.
      unfold apply_r, var, M.elt in *.
      destruct (M.get x0 sig) eqn:Hget; try congruence.
      subst. unfold In, map_cod; eexists; eauto.
    }
    rewrite M.gso; auto.
Qed.

Definition contains_fun_map (fm : fun_map) (rho : env) : Prop :=
  Forall
    (fun '(f, (t, xs, e)) => exists rho' fl f',
        M.get f rho = Some (Vfun rho' fl f') /\
        find_def f' fl = Some (t, xs, e))
    (M.elements fm).

Arguments pbind : simpl never.
Arguments ret : simpl never.
Arguments preord_env_P : simpl never.
Arguments preord_exp : simpl never.

(*
Theorem beta_contraction0_correct : forall e sig fm s k rho rho1,
  let rho' := extend_with sig rho1 in
  unique_bindings e ->
  preord_env_P pr cenv (occurs_free e) k PG rho rho' ->
  contains_fun_map fm rho ->
  contains_fun_map fm rho' ->
  {{ fun st _ => used_vars e \subset from_fresh st }}
     beta_contract St IH 0 e sig fm s
  {{ fun st _ e' st' _ => preord_exp pr cenv k P PG (e, rho) (e', extend_with sig rho') }}.
Proof.
  intros e; pattern e; revert e; apply exp_ind'; intros.
  - (* Econstr *)
    simpl.
  - (* Ecase [] *) admit.
  - (* Ecase (::) *) admit.
  - (* Eproj *) admit.
  - (* Eletapp *) admit.
  - (* Efun *) admit.
  - (* Eapp *) admit.
  - (* Eprim *) admit.
  - (* Ehalt *) admit. 
Admitted. *)


Lemma extend_with_apply_r : forall k sig rho rho' x,
  preord_env_P pr cenv (FromList [x] :|: map_cod sig) k PG rho rho' ->
  preord_var_env pr cenv k PG (extend_with sig rho) rho' x (apply_r sig x).
Proof.
  intros.
  unfold preord_var_env, apply_r.
  rewrite extend_with_spec.
  apply H.
  unfold var in *; destruct (M.get x sig) eqn:Hx.
  - right; now exists x.
  - left; now constructor.
Qed.

Lemma Forall2_extend_with_apply_r_list : forall l k sig rho rho',
  preord_env_P pr cenv (FromList l :|: map_cod sig) k PG rho rho' ->
  Forall2 (preord_var_env pr cenv k PG (extend_with sig rho) rho') l (apply_r_list sig l).
Proof.
  induction l; intros; [constructor|].
  constructor; [apply extend_with_apply_r|apply IHl]; preord_env_P_antimon.
Qed.

Context {PostPP : post_compat P P}.
Context {PostRefl : post_refl P}.

(* The helper function beta_contract_aux blows up all the time when proving stuff.
   Stow it away in a fresh variable so we can actually see the goal. *)
Definition abbrev {A} {x : A} := x.
Ltac fold_aux :=
  (* match goal with sig : M.t var, fm : fun_map, s : St |- _ => *)
  lazymatch goal with |- context [_ <- ?f ?e ?sig ?fm ?s ;; _] =>
    let beta_contract_aux := fresh "beta_contract_aux" in
    pose (beta_contract_aux := @abbrev _ f);
    change f with beta_contract_aux
  end(* end*).

(* To unfold one recursive iteration *)
Ltac unfold_aux :=
  lazymatch goal with aux := @abbrev _ ?f |- _ =>
    let Hrewrite := fresh "H" in
    assert (Hrewrite : aux = f) by reflexivity;
    rewrite Hrewrite;
    rewrite <- Hrewrite;
    clear Hrewrite
  end.

Definition beta_contraction_metric := fun '(e, d) => (sizeof_exp e + d)%nat.

(* Some seemingly arbitrary things + lemmas about eta expansion on nats, needed by spark_evaluation *)
Definition opaque_id {A} (x: A) := x.
Arguments opaque_id : simpl never.
Lemma nat_eta {A} d (f : nat -> A) : match d with 0%nat => f 0%nat | S d' => f (S d') end = f d.
Proof. now destruct d. Qed.
Definition nat_split {R} (n:nat) (f g:nat->R) :=
  match n with
  | 0%nat => opaque_id f 0%nat
  | S n' => opaque_id g (S n')
  end.
Lemma nat_merge : forall {R} n (f g : nat->R), (forall m, f (S m) = g (S m)) -> nat_split n f g = f n.
Proof. intros; unfold nat_split; destruct n; auto. Qed.

(* We need to expose a constructor of the d argument in order for Coq to reduce the call to
   beta_contract. Since many cases don't depend at all on the value of d, using [destruct d]
   to do this ends up duplicating a bunch of cases. spark_evaluation will use [destruct d]
   and some hacks to prove that the two subcases are essentially the same case and merge them. *)
Ltac spark_evaluation :=
  lazymatch goal with
  | |- {{_}} beta_contract ?St ?IH ?d ?e ?sig ?fm ?s {{_}} =>
    (* Expose a case split on d so that beta_contract actually gets applied.
       The rhs of S d' arm must be of the form opaque_id f (S d') where d'∉fv(f).
       This way we can pattern match on f. opaque_id is there to prevent beta reduction *)
    let expanded := constr:(
      match d with
      | 0%nat => beta_contract St IH 0%nat e sig fm s 
      | S d' => opaque_id (fun d'' => beta_contract St IH (S (Nat.pred d''))%nat e sig fm s) (S d')
      end
    ) in
    replace (beta_contract St IH d e sig fm s) with expanded by (now destruct d);
    (* Expand out beta_contract in each case arm *)
    simpl (beta_contract _ _ _ _ _ _ _);
    (* Fold recursive calls back up *)
    lazymatch goal with
    | |- context [_ <- ?f _ sig _ _ ;; _] =>
      (* Fold d = 0 arm *)
      let Heq := fresh "Heq" in
      assert (Heq : f = beta_contract St IH 0%nat) by reflexivity;
      rewrite Heq; clear Heq;
      (* Fold S d' arm *)
      let new_arm :=
        lazymatch goal with
        | |- context [opaque_id ?f] =>
          let res := constr:(fun d''' => ltac:(
            let new_body := fresh "new_body" in
            let body_ty := type of (f d''') in
            evar (new_body : body_ty);
            assert (f (S (Nat.pred d''')) = new_body) by (
              lazymatch goal with
              | |- context [_ <- ?f _ sig _ _ ;; _] =>
                replace f with (beta_contract St IH (S (Nat.pred d'''))) by reflexivity
              end;
              subst new_body;
              reflexivity);
            exact new_body))
          in
          eval lazy zeta in res
        end
      in
      lazymatch goal with
      | |- context [opaque_id ?f] =>
        replace f with new_arm by (lazy zeta; reflexivity)
      end
    | |- ?G => idtac
    end;
    (* Massage d = 0 arm to be of the form opaque_id ?f 0%nat *)
    lazymatch goal with
    | |- {{_}} match _ with 0%nat => ?e | S _ => _ end {{_}} =>
      let e' := fresh "e'" in
      let He' := fresh "He'" in
      let ty := type of e in
      evar (e' : ty);
      assert (He' : e = e') by (subst e'; reflexivity);
      progress pattern (0%nat) in e' || idtac "Didn't progress on" e';
      change e with (opaque_id e');
      clear He';
      subst e';
      lazymatch goal with
      | |- context [opaque_id (?f ?x)] =>
        change (opaque_id (f x)) with (opaque_id f x)
      end
    end;
    (* Rewrite the match expression in terms of nat_split and then prove that the two arms
       are equivalent. *)
    lazymatch goal with |- {{_}} ?e {{_}} =>
    lazymatch e with (match ?n with 0%nat => opaque_id ?f 0%nat | S _ => opaque_id ?g (S _) end) =>
      change e with (nat_split n f g)
    end end;
    rewrite nat_merge by reflexivity
  end.

Ltac Intros' :=
  repeat lazymatch goal with
  | |- forall _ : (), _ => intros []
  | |- forall _, _ => intro
  end.
Ltac Intros :=
  repeat lazymatch goal with
  | |- forall _ : (), _ => intros []
  | |- forall _, _ => intro
  | |- {{_}} _ {{fun _ _ _ _ _ => forall _, _}} => apply post_universal
  end.

Ltac Intro x := apply post_universal; intro x.

Ltac bind_next := eapply bind_triple''; Intros'.

Ltac ret := apply return_triple; Intros.

Ltac mon_apply H :=
  first
    [ apply H
    | eapply H
    | eapply pre_strenghtening; [|apply H]
    | eapply pre_strenghtening; [|eapply H]
    | eapply pre_strenghtening; [|eapply H]
    | eapply pre_strenghtening; [|eapply post_weakening; [|apply H]]
    | eapply pre_strenghtening; [|eapply post_weakening; [|eapply H]]
    ].

Ltac choose_post P :=
  match goal with H : ?P' ?st ?s ?x ?st' ?s' |- _ => match H with P =>
    pattern st, s, x, st', s'; apply P
  end end.

(* UB(e) ->
   ρ ∼σ ρ' ->  (* this is preord_env_P_inj *)
   BV(e) ∩ dom(σ) = ϕ ->
   UV(e) ∩ cod(σ) = ϕ ->
   {{_}} _ {{e' => (e, ρ) ∼ (e', ρ') }}
*)

Section beta_contraction_correct'.

Ltac gen x := generalize dependent x.

Notation "'(' rho ',' e ')' '⇓' '{' c '}' v" :=
  (bstep_cost _ _ rho e v c)
  (at level 60, only printing).

Notation "rho1 '~' '{' k '}' rho2 'on' '{' S '}' 'under' '{' f '}'" :=
  (preord_env_P_inj pr cenv PG S k f rho1 rho2)
  (at level 60, only printing).

Notation "rhoe1 '~' '{' k '}' rhoe2" :=
  (preord_exp pr cenv k P PG rhoe1 rhoe2)
  (at level 60, only printing).

Notation "v1 '~' '{' k '}' v2" :=
  (preord_val pr cenv k PG v1 v2)
  (only printing).

Notation "S '⊆' T" := (S \subset T) (at level 60, only printing).

Notation "S ∩ T = ∅" := (Disjoint _ S T) (at level 60, only printing).

Notation "sig '[' x ']'" := (apply_r sig x) (at level 60, only printing).
Notation "sig '[' x ']'" := (shrink_cps.apply_r sig x) (at level 60, only printing).
Notation "sig '[' xs ']'" := (apply_r_list sig xs) (at level 60, only printing).
Notation "sig '[' xs ']'" := (shrink_cps.apply_r_list sig xs) (at level 60, only printing).
Notation "rho '[' xs '↦' vs ']'" :=
  (set_list (combine xs vs) rho) (at level 60, left associativity, only printing).
Notation "m '[' x '↦' v ']'" :=
  (M.set x v m) (at level 60, left associativity, only printing).
Notation "m '[' x ']'" := (M.get x m) (only printing).
Notation "m '[' xs ']'" := (get_list xs m) (only printing).
Notation "'FV'" := occurs_free (only printing).
Notation "'BV'" := bound_var (only printing).
Notation "'UV'" := used_vars (only printing).

Theorem freshen_exp_triple : forall e,
  {{ fun st _ => used_vars e \subset from_fresh st }}
     freshen_exp e
  {{ fun _ _ e' st' _ =>
     (forall rho v c, bstep_cost pr cenv rho e v c <-> bstep_cost pr cenv rho e' v c) /\
     occurs_free e <--> occurs_free e' /\
     used_vars e' \subset from_fresh st' }}.
Admitted.

Fixpoint complete_bundle (B : fundefs) clo rho :=
  forall f, In _ (name_in_fundefs B) f -> exists f', M.get f rho = Some (Vfun clo B f').

Definition fun_map_inv k sig fm rho rho' := forall f ft vs e rho_clo B f',
  M.get (apply_r sig f) fm = Some (ft, vs, e) -> 
  M.get f rho = Some (Vfun rho_clo B f') ->
  (* rho and fm agree syntactically on each known function f *)
  find_def f' B = Some (ft, vs, e) /\
  (* The captured environment agrees with rho' on free variables in B *)
  preord_env_P_inj pr cenv PG (occurs_free_fundefs B) k (apply_r sig) rho_clo rho' /\
  (* Every other function in the bundle is also in rho *)
  preord_env_P_inj pr cenv PG (occurs_free_fundefs B) k (apply_r sig)
                   (def_funs B B rho_clo rho_clo) rho'.
  (* complete_bundle B rho_clo rho. *)

Theorem beta_contraction_correct : forall e d sig fm s,
  unique_bindings e ->
  Disjoint _ (bound_var e :|: map_dom fm) (map_dom sig) ->
  Disjoint _ (bound_var e) (map_dom fm) ->
  Disjoint _ (used_vars e) (map_cod sig) ->
  {{ fun st _ => used_vars e \subset from_fresh st }}
     beta_contract St IH d e sig fm s
  {{ fun _ _ e' _ _ => forall k rho rho',
     fun_map_inv k sig fm rho rho' ->
     preord_env_P_inj pr cenv PG (occurs_free e) k (apply_r sig) rho rho' ->
     preord_exp pr cenv k P PG (e, rho) (e', rho') }}.
Proof.
  (* To discharge the simpler cases that come up when applying IH *)
  Ltac cleanup :=
    lazymatch goal with
    | |- post_compat _ _ => apply PostPP
    | |- post_refl _ => apply PostRefl
    | |- _ = beta_contraction_metric (_, _) => reflexivity
    | H : unique_bindings (_ _) |- _ => inv H; auto
    | |- (beta_contraction_metric (_, _) < beta_contraction_metric (_, _))%nat => simpl; omega
    | H : used_vars (_ _) \subset from_fresh _ |- used_vars _ \subset from_fresh _ =>
      let H' := fresh "H" in
      let elt := fresh "elt" in
      revert H; Ensembles_to_logic; intros H' elt;
      specialize H' with (x := elt);
      revert H';
      Ensembles_to_logic;
      firstorder
    | |- Disjoint _ _ _ =>
      repeat lazymatch goal with H : Disjoint _ _ _ |- _ => revert H end;
      Ensembles_to_logic;
      intuition
    | H : preord_env_P_inj _ _ _ _ _ _ _ _ |- preord_var_env _ _ _ _ _ _ ?x (shrink_cps.apply_r _ ?x) =>
      apply H; match goal with |- ?f ?x => change (In _ f x) end;
      Ensembles_to_logic; intuition
    | |- Forall2 (preord_var_env _ _ _ _ _ _) ?l (shrink_cps.apply_r_list _ ?l) =>
      eapply Forall2_preord_var_env_map; eauto;
      Ensembles_to_logic; auto
    | _ => idtac
    end.
  (* Set up strong induction over the custom metric.
     IH gives the statement for all subterms of e and all smaller values of d. *)
  intros e d; remember (beta_contraction_metric (e, d)) as med.
  generalize dependent e; generalize dependent d.
  pattern med; apply lt_wf_ind; clear med.
  intros med IHmed' d e Hmed sig fm s Huniq Hdom Hdom_fm Hcod; destruct e.
  - (* Econstr *)
    spark_evaluation. bind_next. ret.
    (* We need to figure out what Q is. *)
    eapply preord_exp_constr_compat; cleanup; cleanup.
    (* We've found Q. *)
    gen k; gen rho; gen rho'.
    choose_post H.
    Intro vs1; Intro vs2; Intro Hvs.
    mon_apply IHmed'; Intros; cleanup; cleanup.
    admit.
  - (* Ecase *)
    spark_evaluation.
    subst med; induction l.
    + bind_next; [|ret].
      ret.
      assert (x = []) by choose_post H; subst.
      admit.
      simpl; auto.
    + admit.
  - (* Eproj *)
    spark_evaluation. bind_next. ret.
    eapply preord_exp_proj_compat; cleanup; cleanup.
    gen k; gen rho; gen rho'.
    choose_post H.
    Intro v1; Intro v2; Intro Hvs.
    mon_apply IHmed'; Intros; cleanup; cleanup.
    admit.
  - (* Eletapp *)
    destruct d; simpl.
    + admit.
    + destruct (update_letApp _ _ _ _ _ _), b.
      destruct (M.get _ _) eqn:Hget.
      destruct p.
      destruct p.
      bind_next; [|mon_apply freshen_exp_triple].
      Print inline_letapp.
      destruct (inline_letapp _ _) eqn:Hctx.
      destruct p.
      apply pre_eq_state_lr; Intros.
      mon_apply IHmed'.
      4:reflexivity.
      2: {
        simpl; Intros.
        Print fun_map_inv.
        unfold preord_exp; intros.
        match goal with H : bstep_cost _ _ _ _ _ _ |- _ => inv H end.
        SearchAbout app_ctx.
        assert (Hctx_step : exists c'', (c'' <= c + c' + 1 + Datatypes.length l)%nat /\
                       bstep_cost pr cenv rho'' (e1 |[ e ]|) v2 c''). {
          admit.
        }
        destruct Hctx_step as [? [? ?]].
        match goal with H : forall _ _ _, fun_map_inv _ _ _ _ _ -> _ |- _ =>
          edestruct (H k) as [? [? [? [? ?]]]]; try apply H7; try omega
        end.
        admit. admit.
        do 2 eexists; split; try eassumption; split.
        admit.
        eapply preord_val_monotonic; eauto; omega.
      }
      (* Unfolding preord_exp and stepping forward from the Eletapp should hopefully give
         extended environment + reduced expression that resemble x', rho'
         Can then apply IH to these *)
      all: admit.
  - (* Efun *)
    spark_evaluation.
    destruct (update_funDef St IH f sig s).
    bind_next. bind_next. ret.
    eapply preord_exp_fun_compat; cleanup.
    gen k; gen rho; gen rho'.
    choose_post H.
    mon_apply IHmed'; Intros; cleanup; cleanup.
    admit.
    admit.
    admit.
    admit.
    admit.
  - (* Eapp *)
    rename f into ft, v into f, l into ys.
    destruct d; simpl.
    + destruct (update_App _ _ _ _ _ _), b.
      admit.
      admit.
    + destruct (update_App _ _ _ _ _ _), b.
      destruct (M.get _ _) eqn:Hget.
      repeat match goal with |- context [let (_, _) := ?p in _] => destruct p end.
      bind_next; [|eapply pre_strenghtening; [|apply freshen_exp_triple]].
      eapply pre_eq_state_lr.
      rename l into xs, f0 into ft', e into body, x into body'.
      intros st0 [] [Hfreshen [Hfreshfv Hfreshuv]].
      mon_apply IHmed'; cleanup.
      2: {
        intros st0' [] e' st1 [] Hused IHmed [? []] k rho rho' Hinv Henv; subst st0'.
        intros v' c' Hle Hstep.
        inv Hstep.
        match goal with H : bstep_cost _ _ _ _ _ _ |- _ => rename H into Hstep end.
        rename rho'0 into rho_cap, fl into B, xs0 into xs'', e into body'', ft into ft''.
        pose (Hinv' := Hinv).
        unfold fun_map_inv in Hinv'.
        specialize Hinv' with (rho_clo := rho_cap) (B := B) (e := body) (f' := f') (vs := xs)
          (f := f) (ft := ft').
        edestruct Hinv' as [Hfind_def [Hrho_cap Hbundle]]; try assumption.
        assert (ft'' = ft') by congruence;
        assert (xs'' = xs) by congruence;
        assert (body'' = body) by congruence.
        subst ft'' xs'' body''.
        rewrite Hfreshen in Hstep.
        edestruct (IHmed k rho'' rho') as [? [? [? [? ?]]]];
          try match goal with |- bstep_cost _ _ _ _ _ _ => eassumption end;
          try omega.
        Print add_fundefs.
        - unfold fun_map_inv.
          unfold fun_map_inv in Hinv.
          intros f'' ft'' xs'' e'' rho_clo'' B'' f'''.
          (* There are 3 cases: f'' in xs, f'' in B, and f'' in rho_cap
             - f'' in rho_cap: fm[sig[f'']] = Some (ft'', xs'', e'') ->
                               rho_cap[f''] = Some (Vfun rho_clo'' B'' f''') ->
                               find_def f''' B'' = Some (ft'', xs'', e'') /\
                               rho_clo'' ~ {k} rho' on {fv_fds B''} under {sig [xs↦xig ys]} /\
                               complete_bundle B'' rho_clo'' rho''
               Hinv says find_def f''' B'' = Some (ft'', xs'', e'') /\
                         rho_clo'' ~ {k} rho' on {fv_fds B''} under {apply_r sig} /\
                         complete_bundle B'' rho_clo'' rho
          *)
          split_var_in_list f'' xs; [|split_var_in_fundefs f'' B Hfds].
          + (* f'' in xs *)
            intros Hfm Hrho''.
            (* Hinv says find_def f''' B'' = Some (ft'', xs'', e'') /\
                         rho_clo'' ~ {k} rho' on {occurs_free_fundefs B''} under {apply_r sig} /\
                         def_funs B B rho_clo'' rho_clo'' ~ {k} rho' on {fv_fds B''} under sig
                         (* complete_bundle B'' rho_clo'' rho *)
              Need rho_clo'' ~ {k} rho' on {FV_fundefs B''} under {apply_r (sig[xs↦sig ys])}
                 and similar for def_funs B B rho_clo'' rho_clo''
              Agree on xs because rho_clo''[x in xs] = v in vs = rho[y in ys] for some y
                              and rho'[sig[x in xs]] = rho'[y in ys]
                              and rho, rho' agree on fv(App f ys) ⊇ ys *)
            admit.
          + (* f'' in B *)
            intros Hfm Hrho''.
            (* f'' in B: fm[sig[f'']] = Some (ft'', xs'', e'') ->
                         rho''[f''] = Some (Vfun rho_cap B f''') ->
                         find_def f''' B = Some (ft'', xs'', e'') /\
                         rho_cap ~{k} rho' on {FV_fds B} under {apply_r (sig[xs↦sig ys])} /\
                         similar for rho_cap[B] ~ rho'
               So rho[f''] = Some (Vfun rho_cap B f''')
               So Hinv says find_def f''' B = Some (ft'', xs'', e'') /\
                            rho_cap ~{k} rho' on {FV_fds B} under {apply_r sig} /\
                            complete_bundle B rho_cap rho
               Need complete_bundle B rho'', this is obvious because rho'' defined by def_funs
               and xs ∩ B = ∅ or else violate UB *)
            admit.
          + (* f'' in rho_cap *)
          match goal with |- context [M.get (apply_r (set_list ?xys sig) ?x) fm] =>
            assert (Hnosig : M.get (apply_r (set_list xys sig) x) fm = M.get (apply_r sig x) fm)
          end. { admit. }
          rewrite Hnosig.
          assert (Hnotin : ~ List.In f'' xs). { admit. }
          erewrite <- set_lists_not_In with (rho'0 := rho''); eauto.
          (* Can use fact that dom sig ∩ dom fm = ∅ *)
        (*{ unfold fun_map_inv.
          intros.
          assert (~ List.In f l0) by admit.
          Search def_funs M.get. (* get_fundefs *)
          erewrite <- set_lists_not_In; eauto.
          edestruct H3 as [? [? ?]].
          match goal with H : M.get ?x fm = Some _ |- ?lhs = _ => assert (Heq : M.get x fm = lhs) end.
          match goal with |- M.get ?x fm = M.get ?y fm => assert (Hnotin : x = y) end. admit.
          rewrite Hnotin; reflexivity.
          rewrite <- Heq; eassumption.
          split; [|split]; try eassumption.
          admit.
          admit.
        }*) admit.
        - (* occurs_free body' <--> occurs_free body *) admit.
        - do 2 eexists.
          split; [|split]; [eassumption| |eapply preord_val_monotonic; eauto; omega].
          admit.
      }
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
  - (* Eprim *)
    spark_evaluation. bind_next. ret.
    eapply preord_exp_prim_compat; cleanup; cleanup.
    gen k; gen rho; gen rho'.
    choose_post H.
    Intro v1; Intro v2; Intro Hvs.
    mon_apply IHmed'; Intros; cleanup; cleanup.
    admit.
  - (* Ehalt *)
    spark_evaluation. ret.
    eapply preord_exp_halt_compat; cleanup; cleanup.
Admitted.
End beta_contraction_correct'.

End beta_contraction_correct.
