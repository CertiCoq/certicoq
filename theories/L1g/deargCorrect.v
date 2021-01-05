From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Btauto.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import RelationClasses.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ECSubst.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import EInversion.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import ETyping.
From MetaCoq.Template Require Import utils.
Require Import L1g.dearg.

Import ListNotations.

Import EAstUtils.

Local Notation "Σ 'e⊢' s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.

Ltac propify :=
  unfold is_true in *;
  repeat
    match goal with
    | [H: context[Nat.eqb _ _ = false] |- _] => rewrite Nat.eqb_neq in H
    | [H: context[Nat.eqb _ _ = true] |- _] => rewrite Nat.eqb_eq in H
    | [H: context[Nat.ltb _ _ = false] |- _] => rewrite Nat.ltb_ge in H
    | [H: context[Nat.ltb _ _ = true] |- _] => rewrite Nat.ltb_lt in H
    | [H: context[Nat.leb _ _ = false] |- _] => rewrite Nat.leb_gt in H
    | [H: context[Nat.leb _ _ = true] |- _] => rewrite Nat.leb_le in H
    | [H: context[andb _ _ = false] |- _] => rewrite Bool.andb_false_iff in H
    | [H: context[andb _ _ = true] |- _] => rewrite Bool.andb_true_iff in H
    | [H: context[negb _ = false] |- _] => rewrite Bool.negb_false_iff in H
    | [H: context[negb _ = true] |- _] => rewrite Bool.negb_true_iff in H
    | [H: context[orb _ _ = false] |- _] => rewrite Bool.orb_false_iff in H
    | [H: context[orb _ _ = true] |- _] => rewrite Bool.orb_true_iff in H
    | [|- context[Nat.eqb _ _ = false]] => rewrite Nat.eqb_neq
    | [|- context[Nat.eqb _ _ = true]] => rewrite Nat.eqb_eq
    | [|- context[Nat.ltb _ _ = false]] => rewrite Nat.ltb_ge
    | [|- context[Nat.ltb _ _ = true]] => rewrite Nat.ltb_lt
    | [|- context[Nat.leb _ _ = false]] => rewrite Nat.leb_gt
    | [|- context[Nat.leb _ _ = true]] => rewrite Nat.leb_le
    | [|- context[andb _ _ = false]] => rewrite Bool.andb_false_iff
    | [|- context[andb _ _ = true]] => rewrite Bool.andb_true_iff
    | [|- context[negb _ = false]] => rewrite Bool.negb_false_iff
    | [|- context[negb _ = true]] => rewrite Bool.negb_true_iff
    | [|- context[orb _ _ = false]] => rewrite Bool.orb_false_iff
    | [|- context[orb _ _ = true]] => rewrite Bool.orb_true_iff
    end.

(**** Basic auxiliary lemmas ****)
Lemma Forall_snoc {A} (P : A -> Prop) (l : list A) (a : A) :
  Forall P (l ++ [a]) ->
  Forall P l /\ P a.
Proof.
  intros all.
  apply Forall_app in all.
  intuition.
  now inversion H0.
Qed.

Lemma Forall_repeat {A} (P : A -> Prop) (a : A) (n : nat) :
  P a ->
  Forall P (repeat a n).
Proof.
  intros pa.
  now induction n; constructor.
Qed.

Lemma alli_Alli {A} (f : nat -> A -> bool) (l : list A) (n : nat) :
  alli f l n -> Alli (fun n a => f n a) n l.
Proof.
  intros a.
  induction l in n, a |- *.
  - constructor.
  - cbn in *.
    propify.
    constructor; [easy|].
    now apply IHl.
Qed.

Lemma Alli_alli {A} (f : nat -> A -> bool) (n : nat) (l : list A) :
  Alli (fun n a => f n a) n l -> alli f l n.
Proof.
  intros a.
  induction l in n, a |- *.
  - easy.
  - depelim a.
    cbn.
    now rewrite i, IHl.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) (l : list A) :
  Alli (fun n a => P n (f a)) n l ->
  Alli P n (map f l).
Proof. now induction 1; cbn; constructor. Qed.

Lemma skipn_firstn_slice {A} n n' (l : list A) :
  n <= n' ->
  skipn n (firstn n' l) ++ skipn n' l = skipn n l.
Proof.
  intros le.
  induction n in n, n', le, l |- *.
  - now rewrite !skipn_0, firstn_skipn.
  - destruct n'; [easy|].
    destruct l; [easy|].
    rewrite firstn_cons, !skipn_cons.
    apply IHn.
    lia.
Qed.

(**** Auxiliary lemmas about closedn ****)
Lemma closedn_mkApps k hd args :
  closedn k hd ->
  Forall (closedn k) args ->
  closedn k (mkApps hd args).
Proof.
  intros clos_hd clos_args.
  induction args in k, hd, args, clos_hd, clos_args |- * using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn.
  propify.
  now apply Forall_snoc in clos_args as (clos_args & clos_x).
Qed.

Lemma closed_mkApps hd args :
  closed hd ->
  Forall (closedn 0) args ->
  closed (mkApps hd args).
Proof. now intros; apply closedn_mkApps. Qed.

Lemma closed_mkApps_inv hd args :
  closed (mkApps hd args) ->
  closed hd /\
  Forall (closedn 0) args.
Proof.
  revert hd.
  induction args using List.rev_ind; [easy|]; intros hd clos.
  rewrite mkApps_app in clos.
  cbn in clos.
  propify.
  specialize (IHargs hd ltac:(easy)).
  split; [easy|].
  apply app_Forall; [easy|].
  constructor; easy.
Qed.

Lemma closed_mkApps_head hd args :
  closed (mkApps hd args) ->
  closed hd.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Lemma closed_mkApps_args hd args :
  closed (mkApps hd args) ->
  Forall (closedn 0) args.
Proof.
  intros clos.
  now pose proof (closed_mkApps_inv _ _ clos).
Qed.

Definition decl_closed (decl : EAst.global_decl) : bool :=
  match decl with
  | ConstantDecl cst =>
    match cst_body cst with
    | Some body => closed body
    | _ => true
    end
  | _ => true
  end.

Definition env_closed (Σ : EAst.global_declarations) : bool :=
  forallb (decl_closed ∘ snd) Σ.

Arguments Nat.ltb : simpl nomatch.

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert n k k'.
  induction t using term_forall_list_ind; intros n' k k' clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n);
      cbn; propify; lia.
  - induction X; cbn in *; propify; easy.
  - erewrite <- IHt by eassumption.
    easy.
  - erewrite <- IHt1 at 1 by easy.
    erewrite <- IHt2 by easy.
    easy.
  - easy.
  - split; [easy|].
    destruct clos as (_ & clos).
    induction X; cbn in *; propify; easy.
  - rewrite map_length.
    revert n' k k' clos.
    induction X; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHX n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
  - rewrite map_length.
    revert n' k k' clos.
    induction X; intros n' k k' clos; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k)) _) by easy.
      f_equal.
      lia.
    + erewrite <- (IHX n' (S k) (S k'));
        repeat (f_equal; try lia).
      rewrite <- (proj2 clos);
        repeat (f_equal; try lia).
Qed.

Lemma closedn_subst s k k' t :
  Forall (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  revert k k'.
  induction t using term_forall_list_ind; intros k k' all clos;
    cbn in *; auto; propify.
  - destruct (Nat.leb_spec k' n); cbn in *; propify.
    + destruct nth_error eqn:eq;
        cbn in *.
      * apply closedn_lift.
        rewrite Forall_forall in all.
        apply nth_error_In in eq.
        easy.
      * propify.
        apply nth_error_None in eq.
        lia.
    + lia.
  - induction X; cbn in *; propify; easy.
  - erewrite <- (IHt _ (S k')); [|easy|rewrite <- clos; f_equal; lia].
    f_equal; lia.
  - split; [easy|].
    erewrite <- (IHt2 _ (S k')); [|easy|].
    + f_equal; lia.
    + rewrite <- (proj2 clos); f_equal; lia.
  - easy.
  - split; [easy|].
    induction X; cbn in *; propify; easy.
  - rewrite map_length.
    revert k k' all clos.
    induction X; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHX _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
  - rewrite map_length.
    revert k k' all clos.
    induction X; intros k k' all all'; cbn in *; propify; [easy|].
    destruct x; cbn in *.
    split.
    + erewrite <- (p _ (S (#|l| + k'))); [|easy|].
      * f_equal; lia.
      * rewrite <- (proj1 all').
        f_equal; lia.
    + erewrite <- (IHX _ (S k')); [|easy|].
      * repeat (f_equal; try lia).
      * rewrite <- (proj2 all').
        repeat (f_equal; try lia).
Qed.

Lemma closedn_subst0 s k t :
  Forall (closedn k) s ->
  closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros all clos.
  rewrite <- (Nat.add_0_r k).
  apply closedn_subst; [easy|].
  now rewrite Nat.add_0_r.
Qed.

Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros clost closu.
  rewrite closed_subst by easy.
  apply closedn_subst0.
  - constructor; [|easy].
    now eapply closed_upwards.
  - cbn.
    now rewrite Nat.add_1_r.
Qed.

(**** Auxiliary lemmas about wcbv eval ****)
Section fix_flags.
Context {wfl : WcbvFlags}.

Lemma eval_tApp_head Σ hd arg v :
  Σ e⊢ tApp hd arg ▷ v ->
  ∑ hdv, Σ e⊢ hd ▷ hdv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_tApp_arg Σ hd arg v :
  Σ e⊢ tApp hd arg ▷ v ->
  ∑ argv, Σ e⊢ arg ▷ argv.
Proof.
  intros ev.
  now depelim ev.
Qed.

Lemma eval_mkApps_head Σ hd args v :
  Σ e⊢ mkApps hd args ▷ v ->
  ∑ hdv, Σ e⊢ hd ▷ hdv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  specialize (IHargs _ _ ev) as (? & ?).
  now apply eval_tApp_head in e.
Qed.

Lemma eval_mkApps_args Σ hd args v :
  Σ e⊢ mkApps hd args ▷ v ->
  ∑ argsv, All2 (eval Σ) args argsv.
Proof.
  revert hd v.
  induction args; intros hd v ev; [easy|].
  cbn in *.
  apply eval_mkApps_head in ev as ev_hd.
  destruct ev_hd as (hdv & ev_hd).
  specialize (IHargs _ _ ev) as (argsv & all).
  apply eval_tApp_arg in ev_hd as (argv & ev_arg).
  exists (argv :: argsv).
  now constructor.
Qed.

Lemma eval_tApp_heads Σ hd hd' hdv arg v :
  Σ e⊢ hd ▷ hdv ->
  Σ e⊢ hd' ▷ hdv ->
  Σ e⊢ tApp hd arg ▷ v ->
  Σ e⊢ tApp hd' arg ▷ v.
Proof.
  intros ev_hd ev_hd' ev_app.
  depind ev_app.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_box.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_beta.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_fix_value.
  - rewrite (eval_deterministic ev_hd ev_app1) in *.
    now eapply eval_app_cong.
  - easy.
Qed.

Derive Signature for eval.
Derive NoConfusionHom for term.

Lemma eval_tLetIn_inv Σ na val body res :
  Σ e⊢ tLetIn na val body ▷ res ->
  ∑ val_res,
    Σ e⊢ val ▷ val_res ×
    Σ e⊢ csubst val_res 0 body ▷ res.
Proof. intros ev; depelim ev; easy. Qed.

Lemma eval_tLambda_inv Σ na body v :
  Σ e⊢ tLambda na body ▷ v ->
  v = tLambda na body.
Proof. now intros ev; depelim ev. Qed.

Lemma eval_tApp_tLambda_inv Σ na body a v :
  Σ e⊢ tApp (tLambda na body) a ▷ v ->
  ∑ av,
    Σ e⊢ a ▷ av ×
    Σ e⊢ csubst av 0 body ▷ v.
Proof.
  intros ev.
  depelim ev.
  - now apply eval_tLambda_inv in ev1.
  - apply eval_tLambda_inv in ev1.
    inversion ev1; subst; clear ev1.
    easy.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - apply eval_tLambda_inv in ev1.
    solve_discr.
  - now apply eval_tLambda_inv in ev1 as ->.
  - easy.
Qed.

Lemma eval_mkApps_heads Σ hd hd' hdv args v :
  Σ e⊢ hd ▷ hdv ->
  Σ e⊢ hd' ▷ hdv ->
  Σ e⊢ mkApps hd args ▷ v ->
  Σ e⊢ mkApps hd' args ▷ v.
Proof.
  revert hd hd' hdv v.
  induction args as [|a args]; intros hd hd' hdv v ev_hd ev_hd' ev.
  - cbn in *.
    now rewrite (eval_deterministic ev ev_hd) in *.
  - cbn in *.
    apply eval_mkApps_head in ev as ev_app_hd.
    destruct ev_app_hd as (app_hdv & ev_app_hd).
    eapply IHargs.
    2: {
      eapply eval_tApp_heads; [| |exact ev_app_hd].
      all: easy.
    }
    + easy.
    + easy.
Qed.

Lemma lookup_env_find Σ kn :
  ETyping.lookup_env Σ kn =
  option_map snd (find (fun '(kn', _) => if kername_eq_dec kn kn' then true else false) Σ).
Proof.
  induction Σ as [|(kn' & decl) Σ IH]; [easy|].
  cbn.
  now destruct (kername_eq_dec kn kn').
Qed.

Lemma closed_constant Σ kn cst body :
  env_closed Σ ->
  ETyping.declared_constant Σ kn cst ->
  EAst.cst_body cst = Some body ->
  closed body.
Proof.
  intros env_clos decl_const body_eq.
  unfold ETyping.declared_constant in decl_const.
  rewrite lookup_env_find in decl_const.
  destruct (find _ _) eqn:find; [|easy].
  apply find_some in find.
  eapply forallb_forall in env_clos; [|exact (proj1 find)].
  destruct p.
  cbn in *.
  noconf decl_const.
  cbn in *.
  now rewrite body_eq in env_clos.
Qed.

Lemma closed_unfold_fix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_fix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_fix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.fix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.fix_subst_length.
Qed.

Lemma closed_unfold_cofix mfix idx narg fn :
  closed (tFix mfix idx) ->
  ETyping.unfold_cofix mfix idx = Some (narg, fn) ->
  closed fn.
Proof.
  cbn.
  intros clos_fix fix_eq.
  rewrite Nat.add_0_r in *.
  unfold ETyping.unfold_cofix in *.
  destruct (nth_error mfix idx) eqn:Heq; [|easy].
  noconf fix_eq.
  eapply closedn_subst0.
  - clear Heq.
    unfold ETyping.cofix_subst.
    generalize #|mfix|.
    induction n as [|n IH]; [easy|].
    constructor.
    + cbn.
      now rewrite Nat.add_0_r.
    + easy.
  - apply nth_error_In in Heq.
    apply forallb_Forall in clos_fix.
    rewrite Forall_forall in clos_fix.
    now rewrite ETyping.cofix_subst_length.
Qed.

Lemma all_closed Σ args args' :
  Forall (closedn 0) args ->
  All2 (eval Σ) args args' ->
  Forall2 (fun t v => closed t -> closed v) args args' ->
  Forall (closedn 0) args'.
Proof.
  intros args_clos args_eval impl_clos.
  induction args_eval; [easy|].
  depelim args_clos.
  depelim impl_clos.
  easy.
Qed.

Lemma closed_iota_red pars c args brs :
  Forall (fun a => closed a) args ->
  Forall (fun t => closed t.2) brs ->
  closed (ETyping.iota_red pars c args brs).
Proof.
  intros clos_args clos_brs.
  unfold ETyping.iota_red.
  apply closed_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now apply Forall_skipn.
Qed.

Lemma closed_cunfold_fix defs n narg f :
  cunfold_fix defs n = Some (narg, f) ->
  closed (tFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_fix_cunfold_eq in eq by easy.
  now eapply closed_unfold_fix.
Qed.

Lemma closed_cunfold_cofix defs n narg f :
  cunfold_cofix defs n = Some (narg, f) ->
  closed (tCoFix defs n) ->
  closed f.
Proof.
  intros eq clos.
  rewrite <- closed_unfold_cofix_cunfold_eq in eq by easy.
  now eapply closed_unfold_cofix.
Qed.

Lemma eval_closed Σ t v :
  Σ e⊢ t ▷ v ->
  env_closed Σ ->
  closed t ->
  closed v.
Proof.
  intros ev env_clos clos.
  induction ev; cbn in *; propify.
  - easy.
  - apply IHev3.
    now apply closed_csubst.
  - apply IHev2.
    now apply closed_csubst.
  - apply IHev2.
    apply closed_iota_red.
    + now eapply closed_mkApps_args.
    + now apply forallb_Forall.
  - subst brs.
    cbn in *.
    propify.
    apply IHev2.
    apply closed_mkApps; [easy|].
    clear.
    induction n; [constructor|].
    constructor; easy.
  - apply IHev3.
    split; [|easy].
    destruct clos as (clos & _).
    specialize (IHev1 clos).
    apply closed_mkApps_inv in IHev1 as (? & ?).
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_fix.
  - easy.
  - apply IHev.
    split; [|easy].
    destruct clos as (clos & _).
    apply closed_mkApps_inv in clos.
    cbn in *.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    apply closed_mkApps_inv in clos.
    apply closed_mkApps; [|easy].
    now eapply closed_cunfold_cofix.
  - apply IHev.
    now eapply closed_constant.
  - apply IHev2.
    apply closed_mkApps_args in IHev1; [|easy].
    rewrite nth_nth_error in *.
    destruct (nth_error _ _) eqn:nth_eq.
    + apply nth_error_In in nth_eq.
      rewrite Forall_forall in IHev1.
      now apply IHev1.
    + easy.
  - easy.
  - easy.
  - easy.
Qed.

Fixpoint deriv_length {Σ t v} (ev : Σ e⊢ t ▷ v) : nat :=
  match ev with
  | eval_atom _ _ => 1
  | red_cofix_case _ _ _ _ _ _ _ _ _ ev
  | red_cofix_proj _ _ _ _ _ _ _ _ ev
  | eval_delta _ _ _ _ _ _ ev
  | eval_proj_prop _ _ _ _ _ ev _ => S (deriv_length ev)
  | eval_box _ _ _ ev1 ev2
  | eval_zeta _ _ _ _ _ ev1 ev2
  | eval_iota _ _ _ _ _ _ _ ev1 _ ev2
  | eval_iota_sing _ _ _ _ _ _ _ _ ev1 _ _ ev2
  | eval_fix_value _ _ _ _ _ _ _ _ ev1 ev2 _ _
  | eval_proj _ _ _ _ _ _ ev1 _ ev2
  | eval_app_cong _ _ _ _ ev1 _ ev2 => S (deriv_length ev1 + deriv_length ev2)
  | eval_beta _ _ _ _ _ _ ev1 ev2 ev3
  | eval_fix _ _ _ _ _ _ _ _ ev1 ev2 _ ev3 =>
    S (deriv_length ev1 + deriv_length ev2 + deriv_length ev3)
  end.

Lemma deriv_length_min {Σ t v} (ev : Σ e⊢ t ▷ v) :
  1 <= deriv_length ev.
Proof. destruct ev; cbn in *; lia. Qed.

Lemma eval_tApp_deriv {Σ hd arg v} (ev : Σ e⊢ tApp hd arg ▷ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ▷ hdv) argv (ev_arg : Σ e⊢ arg ▷ argv),
    S (deriv_length ev_hd + deriv_length ev_arg) <= deriv_length ev.
Proof.
  depelim ev; cbn in *;
    try now eexists _, ev1, _, ev2.
  easy.
Qed.

Fixpoint sum_deriv_lengths {Σ ts tsv} (a : All2 (eval Σ) ts tsv) : nat :=
  match a with
  | All2_nil => 0
  | All2_cons _ _ _ _ ev a => deriv_length ev + sum_deriv_lengths a
  end.

Fixpoint app_All2
         {A B}
         {T : A -> B -> Type}
         {la lb la' lb'}
         (a1 : All2 T la lb)
         (a2 : All2 T la' lb') : All2 T (la ++ la') (lb ++ lb').
Proof.
  destruct a1.
  - exact a2.
  - refine (All2_cons t _).
    exact (app_All2 _ _ _ _ _ _ _ a1 a2).
Defined.

Lemma eval_mkApps_deriv {Σ hd args v} (ev : Σ e⊢ mkApps hd args ▷ v) :
  ∑ hdv (ev_hd : Σ e⊢ hd ▷ hdv) argsv (ev_args : All2 (eval Σ) args argsv),
    deriv_length ev_hd + #|args| + sum_deriv_lengths ev_args <= deriv_length ev.
Proof.
  revert hd v ev.
  induction args; intros hd v ev; cbn in *.
  - eexists _, ev, [], All2_nil.
    now cbn.
  - specialize (IHargs _ _ ev) as (hdv & ev_hd & argsv & ev_args & len).
    specialize (eval_tApp_deriv ev_hd) as (hdv' & ev_hdv' & argv & ev_argv & len').
    eexists _, ev_hdv', (argv :: argsv).
    exists (All2_cons ev_argv ev_args).
    cbn in *.
    lia.
Qed.

Lemma All2_split_eq
      {X Y} {T : X -> Y -> Type}
      {xs ys xs' ys'}
      (a : All2 T (xs ++ xs') (ys ++ ys')) :
  #|xs| = #|ys| ->
  ∑ apref asuf, a = app_All2 apref asuf.
Proof.
  intros eq.
  induction xs in xs, ys, xs', ys', a, eq |- *.
  - destruct ys; [|easy].
    cbn in *.
    now exists All2_nil, a.
  - destruct ys; [easy|].
    cbn in *.
    depelim a.
    specialize (IHxs ys xs' ys' a ltac:(easy)) as (apref & asuf & ->).
    now exists (All2_cons t apref), asuf.
Qed.

Lemma All2_rev_rect X Y (T : X -> Y -> Type) (P : forall xs ys, All2 T xs ys -> Type) :
  P [] [] All2_nil ->
  (forall x y xs ys (t : T x y) (a : All2 T xs ys),
      P xs ys a -> P (xs ++ [x]) (ys ++ [y]) (app_All2 a (All2_cons t All2_nil))) ->
  forall xs ys (a : All2 T xs ys), P xs ys a.
Proof.
  intros nil_case snoc_case.
  induction xs using MCList.rev_ind; intros ys a.
  - now depelim a.
  - destruct ys as [|y ys _] using MCList.rev_ind.
    + apply All2_length in a as ?.
      rewrite app_length in *.
      now cbn in *.
    + unshelve epose proof (All2_split_eq a _) as (? & ? & ->).
      * apply All2_length in a.
        rewrite !app_length in a.
        now cbn in *.
      * depelim x1.
        depelim x3.
        apply snoc_case.
        apply IHxs.
Qed.

Inductive All2_eval_app_spec Σ : list term -> term ->
                                 list term -> term ->
                                 forall ts tsv, All2 (eval Σ) ts tsv -> Type :=
| All2_eval_app_intro {ts tsv} (a : All2 (eval Σ) ts tsv)
                      {x xv} (evx : Σ e⊢ x ▷ xv) :
    All2_eval_app_spec
      Σ ts x tsv xv
      (ts ++ [x])
      (tsv ++ [xv])
      (app_All2 a (All2_cons evx All2_nil)).

Derive Signature for All2.
Derive NoConfusionHom for All2.

Lemma All2_eval_snoc_elim
      {Σ ts tsv x xv} (a : All2 (eval Σ) (ts ++ [x]) (tsv ++ [xv])) :
  All2_eval_app_spec Σ ts x tsv xv _ _ a.
Proof.
  unshelve epose proof (All2_split_eq a _) as (? & ev & ->).
  - apply All2_length in a.
    rewrite !app_length in a.
    now cbn in *.
  - depelim ev.
    depelim ev.
    constructor.
Qed.

Lemma eval_tApp_heads_deriv {Σ hd hd' hdv arg v}
      (ev_hd : Σ e⊢ hd ▷ hdv)
      (ev_hd' : Σ e⊢ hd' ▷ hdv)
      (ev_app : Σ e⊢ tApp hd arg ▷ v) :
  ∑ (ev_app' : Σ e⊢ tApp hd' arg ▷ v),
    (deriv_length ev_app + deriv_length ev_hd' = deriv_length ev_app' + deriv_length ev_hd)%nat.
Proof.
  depind ev_app.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_box|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_beta|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_fix_value|].
    cbn; lia.
  - pose proof (eval_unique_sig ev_hd ev_app1) as H; noconf H.
    unshelve eexists _; [now eapply eval_app_cong|].
    cbn; lia.
  - easy.
Qed.

Lemma eval_mkApps_heads_deriv {Σ hd hd' hdv args v}
      (ev_hd : Σ e⊢ hd ▷ hdv)
      (ev_hd' : Σ e⊢ hd' ▷ hdv)
      (ev_apps : Σ e⊢ mkApps hd args ▷ v) :
  ∑ (ev_apps' : Σ e⊢ mkApps hd' args ▷ v),
  (deriv_length ev_apps + deriv_length ev_hd' = deriv_length ev_apps' + deriv_length ev_hd)%nat.
Proof.
  revert hd hd' hdv v ev_hd ev_hd' ev_apps.
  induction args using MCList.rev_ind; intros; cbn in *.
  - pose proof (eval_unique_sig ev_hd ev_apps) as H; noconf H.
    exists ev_hd'; lia.
  - revert ev_apps; rewrite !mkApps_app; intros.
    cbn in *.
    eapply eval_tApp_head in ev_apps as ev_apps'.
    destruct ev_apps' as (? & ev_apps').
    specialize (IHargs _ _ _ _ ev_hd ev_hd' ev_apps') as (ev_apps'' & ?).
    pose proof (eval_tApp_heads_deriv ev_apps' ev_apps'' ev_apps) as (ev & ?).
    exists ev.
    lia.
Qed.

End fix_flags.

(**** Dearging ****)
Lemma dearg_lambdas_nil t :
  dearg_lambdas [] t = t.
Proof.
  induction t; auto.
  cbn.
  now rewrite IHt2.
Qed.

(* We use our own "properly ordered" contexts to represent the lambdas/lets
   that we debox away. Unlike the rest of MetaCoq, these contexts actually
   have the first declaration at the beginning. *)
Fixpoint subst_context (t : term) (k : nat) (Γ : context) : context :=
  match Γ with
  | [] => []
  | cd :: Γ => map_decl (csubst t k) cd :: subst_context t (S k) Γ
  end.

Definition mkLambda_or_LetIn (cd : context_decl) (t : term) : term :=
  match decl_body cd with
  | None => tLambda (decl_name cd) t
  | Some body => tLetIn (decl_name cd) body t
  end.

Definition it_mkLambda_or_LetIn (Γ : context) (u : term) : term :=
  fold_right mkLambda_or_LetIn u Γ.

Fixpoint decompose_body_masked (mask : bitmask) (t : term) : context * term :=
  match mask, t with
  | _, tLetIn na val body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vdef na val :: Γ, t)
  | b :: mask, tLambda na body =>
    let (Γ, t) := decompose_body_masked mask body in
    (vass na :: Γ, t)
  | _, _ => ([], t)
  end.

Definition vasses (Γ : context) : context :=
  filter (fun cd => match decl_body cd with
                    | Some _ => false
                    | None => true
                    end) Γ.

Lemma vasses_app Γ Γ' :
  vasses (Γ ++ Γ') = vasses Γ ++ vasses Γ'.
Proof.
  unfold vasses.
  now rewrite filter_app.
Qed.

Ltac refold :=
  repeat
    match goal with
    | [H: context[fold_right _ ?t ?Γ] |- _] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [|- context[fold_right _ ?t ?Γ]] => progress (fold (it_mkLambda_or_LetIn Γ t) in * )
    | [H: context[filter _ ?Γ] |- _] => progress (fold (vasses Γ) in * )
    | [|- context[filter _ ?Γ]] => progress (fold (vasses Γ) in * )
    end.

Lemma decompose_body_masked_spec mask Γ t t' :
  valid_dearg_mask mask t ->
  (Γ, t') = decompose_body_masked mask t ->
  #|vasses Γ| = #|mask| /\
  it_mkLambda_or_LetIn Γ t' = t.
Proof.
  revert Γ t' mask.
  induction t using term_forall_list_ind; intros Γ t' mask valid_mask eq.
  all: cbn in *.
  all: try solve [destruct mask; [|easy]; inversion eq; easy].
  - destruct mask as [|b mask]; inversion eq; subst; clear eq; [easy|].
    cbn in *.
    destruct (decompose_body_masked mask t) as (Γ' & t'') eqn:decomp_eq.
    inversion H0; subst; clear H0.
    symmetry in decomp_eq.
    cbn.
    refold.
    propify.
    now destruct (IHt _ _ _ (proj2 valid_mask) decomp_eq) as (-> & ->).
  - destruct (decompose_body_masked mask t2) eqn:decomp_eq.
    symmetry in decomp_eq.
    destruct (IHt2 _ _ _ valid_mask decomp_eq).
    now destruct mask; inversion eq; subst.
Qed.

Lemma valid_dearg_mask_spec mask t :
  valid_dearg_mask mask t ->
  ∑ Γ inner,
    #|vasses Γ| = #|mask| /\ it_mkLambda_or_LetIn Γ inner = t.
Proof.
  intros is_valid.
  destruct (decompose_body_masked mask t) as (Γ & inner) eqn:decomp.
  exists Γ, inner.
  now apply decompose_body_masked_spec.
Qed.

Lemma subst_it_mkLambda_or_LetIn t k Γ u :
  csubst t k (it_mkLambda_or_LetIn Γ u) =
  it_mkLambda_or_LetIn (subst_context t k Γ) (csubst t (k + length Γ) u).
Proof.
  revert t k u.
  induction Γ as [|cd Γ IH]; intros t k u.
  - cbn.
    f_equal; lia.
  - cbn in *; refold.
    destruct cd as [na [val|]];
      cbn in *; refold;
      repeat (f_equal; rewrite ?IH; try lia).
Qed.

Lemma length_subst_context t k Γ :
  #|subst_context t k Γ| = #|Γ|.
Proof.
  revert t k.
  induction Γ; [easy|]; intros t k.
  cbn.
  now rewrite IHΓ.
Qed.

Lemma is_dead_closed k t n :
  closedn k t ->
  k <= n ->
  is_dead n t.
Proof.
  revert k n.
  induction t using term_forall_list_ind; intros k n' clos klen;
    cbn in *; auto.
  - propify.
    destruct (Nat.eqb_spec n n'); lia.
  - induction X; [easy|].
    cbn in *.
    propify.
    easy.
  - easy.
  - propify.
    easy.
  - propify.
    easy.
  - propify.
    induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - easy.
  - revert k n' clos klen.
    induction X; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    rewrite <- Nat.add_succ_r in *.
    now eapply IHX.
  - revert k n' clos klen.
    induction X; [easy|]; intros k n' clos klen.
    destruct x.
    cbn in *.
    propify.
    split; [easy|].
    rewrite <- Nat.add_succ_r in *.
    now eapply IHX.
Qed.

Lemma is_dead_csubst k t u k' :
  is_dead k t ->
  closedn k u ->
  k < k' ->
  is_dead k (csubst u k' t).
Proof.
  revert k u k'.
  induction t using term_forall_list_ind; intros k u k' use_eq clos kltn;
    cbn in *; propify; auto.
  - destruct (Nat.compare_spec k' n) as [->| |].
    + now apply is_dead_closed with k.
    + cbn.
      propify.
      lia.
    + cbn.
      propify.
      lia.
  - induction X; [easy|].
    cbn in *.
    propify.
    easy.
  - apply IHt; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - split; [easy|].
    apply IHt2; [easy| |easy].
    now eapply closed_upwards.
  - induction X; [easy|].
    destruct x.
    cbn in *.
    propify.
    easy.
  - rewrite map_length.
    revert k k' kltn use_eq clos.
    induction X; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply p; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
      apply IHX; [easy|easy|].
      now eapply closed_upwards.
  - rewrite map_length.
    revert k k' kltn use_eq clos.
    induction X; [easy|]; intros k k' kltn use_eq clos.
    destruct x.
    cbn in *.
    propify.
    split.
    + apply p; [easy| |easy].
      now eapply closed_upwards.
    + rewrite <- !Nat.add_succ_r in *.
      apply IHX; [easy|easy|].
      now eapply closed_upwards.
Qed.

Lemma valid_dearg_mask_nil t : valid_dearg_mask [] t.
Proof. induction t; easy. Qed.

Lemma valid_dearg_mask_csubst mask t u k :
  valid_dearg_mask mask t ->
  closed u ->
  valid_dearg_mask mask (csubst u k t).
Proof.
  revert mask u k.
  induction t using term_forall_list_ind; intros mask u k valid_mask clos;
    cbn in *;
    try solve [now destruct mask].
  - destruct mask; [|easy].
    apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    propify.
    split.
    + destruct b; [|easy].
      propify.
      now apply (is_dead_csubst 0).
    + now apply IHt.
Qed.

Lemma vasses_subst_context t k Γ :
  vasses (subst_context t k Γ) = vasses Γ.
Proof.
  revert t k.
  induction Γ as [|cd Γ IH]; [easy|]; intros t k.
  cbn in *.
  unfold map_decl.
  destruct cd.
  cbn in *.
  destruct decl_body; cbn.
  - easy.
  - f_equal.
    easy.
Qed.

Lemma dearg_lambdas_subst mask s k Γ inner :
  #|vasses Γ| = #|mask| ->
  dearg_lambdas mask (subst [s] k (it_mkLambda_or_LetIn Γ inner)) =
  subst [s] k (dearg_lambdas mask (it_mkLambda_or_LetIn Γ inner)).
Proof.
  revert mask s k inner.
  induction Γ as [|cd Γ IH]; intros mask s k inner len_eq.
  - destruct mask; [|easy].
    cbn in *.
    rewrite !dearg_lambdas_nil.
    now f_equal.
  - destruct cd as [na [body|]];
      cbn in *; refold.
    + now rewrite IH by easy.
    + destruct mask as [|[] mask].
      * easy.
      * rewrite IH by easy.
        cbn in *.
        unfold subst1.
        now rewrite !distr_subst.
      * now rewrite IH.
Qed.

Lemma dearg_single_masked mask t args :
  #|mask| <= #|args| ->
  dearg_single mask t args = mkApps t (masked mask args).
Proof.
  intros le.
  induction mask in mask, t, args, le |- *.
  - now destruct args.
  - destruct args; [easy|].
    now destruct a; cbn in *; apply IHmask.
Qed.

Lemma eval_dearg_lambdas_inv {wfl:WcbvFlags} Σ mask Γ inner v :
  env_closed Σ ->
  closed (it_mkLambda_or_LetIn Γ inner) ->
  #|mask| = #|vasses Γ| ->
  Σ e⊢ dearg_lambdas mask (it_mkLambda_or_LetIn Γ inner) ▷ v ->
  ∑ tv, Σ e⊢ it_mkLambda_or_LetIn Γ inner ▷ tv.
Proof.
  intros env_clos clos len_eq ev.
  induction #|Γ| as [|Γlen IH] eqn:Γlen_eq in Γ, mask, inner, v, clos, len_eq, ev |- *.
  - destruct Γ, mask; try easy.
    cbn in *.
    now rewrite dearg_lambdas_nil in *.
  - destruct Γ as [|[na [body|]] Γ];
      cbn in *; refold.
    + easy.
    + apply eval_tLetIn_inv in ev as (bodyv & ev_body & ev_let).
      propify.
      assert (closed bodyv) by (now eapply eval_closed).
      rewrite closed_subst in ev_let by easy.
      rewrite <- dearg_lambdas_subst in ev_let by easy.
      rewrite <- closed_subst in ev_let by easy.
      rewrite subst_it_mkLambda_or_LetIn in ev_let.
      cbn in *.
      apply IH in ev_let as (tv & ev_tv).
      * exists tv.
        rewrite <- subst_it_mkLambda_or_LetIn in ev_tv.
        now econstructor.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * now rewrite length_subst_context.
    + destruct mask as [|[] mask].
      * easy.
      * eexists.
        now eapply eval_atom.
      * eexists.
        now eapply eval_atom.
Qed.

Lemma no_use_subst k t s s' :
  is_dead k t ->
  subst [s] k t = subst [s'] k t.
Proof.
  revert k.
  induction t using term_forall_list_ind; cbn in *; intros k no_use; propify.
  - easy.
  - destruct (Nat.leb_spec k n).
    + now rewrite !(proj2 (nth_error_None _ _)) by (cbn; lia).
    + easy.
  - easy.
  - f_equal.
    induction X; [easy|].
    cbn in *.
    propify.
    now f_equal.
  - now f_equal.
  - now f_equal.
  - now f_equal.
  - easy.
  - easy.
  - f_equal; [easy|].
    destruct no_use as (_ & no_use).
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal; [|easy].
    now f_equal.
  - now f_equal.
  - f_equal.
    revert k no_use.
    induction X; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply p.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- Nat.add_succ_r in *.
      now apply IHX.
  - f_equal.
    revert k no_use.
    induction X; [easy|]; intros k no_use.
    unfold map_def in *.
    destruct x; cbn in *; propify.
    f_equal.
    + f_equal.
      apply p.
      rewrite <- (proj1 no_use).
      now f_equal.
    + rewrite <- !Nat.add_succ_r in *.
      now apply IHX.
Qed.

Lemma masked_nil {X} mask :
  @masked X mask [] = [].
Proof. now destruct mask as [|[] ?]. Qed.

Lemma All2_masked {X Y} {T : X -> Y -> Type} xs ys mask :
  All2 T xs ys ->
  All2 T (masked mask xs) (masked mask ys).
Proof.
  intros all.
  induction all in mask |- *.
  - now rewrite !masked_nil.
  - destruct mask as [|[] mask]; [now constructor| |]; cbn in *.
    + now apply IHall.
    + now constructor.
Qed.

Lemma dearg_lambdas_correct {wfl:WcbvFlags} Σ body args mask v :
  env_closed Σ ->
  closed body ->
  Forall (closedn 0) args ->
  valid_dearg_mask mask body ->
  #|mask| <= #|args| ->
  Σ e⊢ mkApps body args ▷ v ->
  Σ e⊢ mkApps (dearg_lambdas mask body) (masked mask args) ▷ v.
Proof.
  intros env_clos body_clos args_clos valid_mask l ev.
  destruct (valid_dearg_mask_spec _ _ valid_mask) as (Γ & inner & vasses_len & <-).
  induction #|Γ| as [|Γlen IH] eqn:eq
    in Γ, mask, valid_mask, args, body_clos, args_clos, inner, ev, l, vasses_len |- *.
  1: { destruct Γ, mask, args; try easy; cbn in *;
       now rewrite dearg_lambdas_nil. }
  destruct Γ as [|[na [body|]] Γ];
    cbn in *; refold.
  - easy.
  - apply eval_mkApps_head in ev as ev_let.
    destruct ev_let as (letv & ev_let).
    apply eval_tLetIn_inv in ev_let as ev_subst.
    destruct ev_subst as (bodyv & ev_body & ev_subst).
    propify.
    assert (closed bodyv) by (now eapply eval_closed).
    unshelve epose proof
             (IH args mask
                 (subst_context bodyv 0 Γ)
                 (csubst bodyv #|Γ| inner)
                 _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      eapply (eval_mkApps_heads _ _ _ letv); [easy|easy|].
      now eapply eval_mkApps_heads; [exact ev_let| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + rewrite <- subst_it_mkLambda_or_LetIn in IH.
      apply eval_mkApps_head in IH as ev_top.
      destruct ev_top as (topv & ev_top).
      rewrite subst_it_mkLambda_or_LetIn in ev_top.
      apply eval_dearg_lambdas_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite <- subst_it_mkLambda_or_LetIn in ev_top.
        eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
        econstructor; [easy|].
        rewrite !closed_subst in * by easy.
        now rewrite <- dearg_lambdas_subst.
  - destruct mask as [|b mask]; [easy|];
      cbn in *; refold.
    destruct args as [|a args]; cbn in *; [easy|].
    apply eval_mkApps_head in ev as ev_app.
    destruct ev_app as (appv & ev_app).
    apply eval_tApp_tLambda_inv in ev_app as ev_subst.
    destruct ev_subst as (av & ev_a & ev_subst).
    assert (closed av).
    { apply Forall_inv in args_clos.
      now eapply eval_closed. }
    unshelve epose proof
    (IH args mask
        (subst_context av 0 Γ)
        (csubst av #|Γ| inner)
        _ _ _ _ _ _ _) as IH.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now apply closed_csubst.
    + now apply Forall_inv_tail in args_clos.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      propify.
      now apply valid_dearg_mask_csubst.
    + easy.
    + rewrite <- subst_it_mkLambda_or_LetIn.
      now eapply eval_mkApps_heads; [exact ev_app| |]; easy.
    + now rewrite vasses_subst_context.
    + now rewrite length_subst_context.
    + apply eval_mkApps_head in IH as ev_top.
      destruct ev_top as (topv & ev_top).
      apply eval_dearg_lambdas_inv in ev_top as ev_sub_top; cycle 1.
      * easy.
      * rewrite <- subst_it_mkLambda_or_LetIn.
        now apply closed_csubst.
      * now rewrite vasses_subst_context.
      * rewrite <- !subst_it_mkLambda_or_LetIn in *.
        destruct ev_sub_top as (sub_top & ev_sub_top).
        rewrite !closed_subst in * by easy.
        destruct b; cbn in *.
        -- eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
           unfold subst1.
           rewrite <- dearg_lambdas_subst by easy.
           propify.
           now erewrite no_use_subst.
        -- eapply eval_mkApps_heads; [| |now eauto]; [now eauto|].
           rewrite dearg_lambdas_subst in ev_top by easy.
           rewrite <- closed_subst in ev_top by easy.
           eapply eval_beta; [|easy|easy].
           now eapply eval_atom.
Qed.

Section dearg_correct.
Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).
Notation get_ctor_mask := (get_ctor_mask ind_masks).
Notation get_mib_masks := (get_mib_masks ind_masks).
Notation get_const_mask := (get_const_mask const_masks).
Notation dearg := (dearg ind_masks const_masks).
Notation dearg_aux := (dearg_aux ind_masks const_masks).
Notation dearg_env := (dearg_env ind_masks const_masks).
Notation dearg_decl := (dearg_decl ind_masks const_masks).
Notation dearg_cst := (dearg_cst ind_masks const_masks).
Notation dearg_case := (dearg_case ind_masks).
Notation dearg_proj := (dearg_proj ind_masks).
Notation valid_case_masks := (valid_case_masks ind_masks).
Notation valid_proj := (valid_proj ind_masks).
Notation valid_cases := (valid_cases ind_masks).
Notation valid_masks_decl := (valid_masks_decl ind_masks const_masks).
Notation valid_masks_env := (valid_masks_env ind_masks const_masks).
Notation is_expanded_aux := (is_expanded_aux ind_masks const_masks).
Notation is_expanded := (is_expanded ind_masks const_masks).
Notation is_expanded_env := (is_expanded_env ind_masks const_masks).

Lemma dearg_aux_mkApps args args' hd :
  dearg_aux args (mkApps hd args') = dearg_aux (map dearg args' ++ args) hd.
Proof.
  revert args hd.
  induction args' as [|a args' IH]; intros args hd; [easy|].
  cbn.
  now rewrite IH.
Qed.

Lemma dearg_mkApps hd args :
  dearg (mkApps hd args) = dearg_aux (map dearg args) hd.
Proof.
  unfold dearg.
  now rewrite dearg_aux_mkApps, app_nil_r.
Qed.

Ltac refold' :=
  refold;
  change (dearg_aux []) with dearg in *.

Lemma subst_dearg_single s k mask t  args :
  subst s k (dearg_single mask t args) =
  dearg_single mask (subst s k t) (map (subst s k) args).
Proof.
  induction mask as [|[] mask IH] in mask, args, k, t |- *; cbn in *.
  - now rewrite subst_mkApps.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      now rewrite <- commut_lift_subst.
    + apply IH.
  - destruct args.
    + cbn.
      f_equal.
      rewrite IH.
      cbn.
      now rewrite commut_lift_subst.
    + apply IH.
Qed.

Lemma lift_dearg_single n k mask t args :
  lift n k (dearg_single mask t args) = dearg_single mask (lift n k t) (map (lift n k) args).
Proof.
  induction mask as [|[] mask IH] in mask, t, args, k |- *; cbn in *.
  - now rewrite lift_mkApps.
  - destruct args.
    + cbn.
      rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
  - destruct args; cbn.
    + rewrite IH.
      cbn.
      now symmetry; rewrite permute_lift.
    + apply IH.
Qed.

Lemma dearg_lambdas_lift mask n k t :
  dearg_lambdas mask (lift n k t) = lift n k (dearg_lambdas mask t).
Proof.
  induction t in mask, n, k, t |- *; cbn in *; try easy.
  - now destruct (_ <=? _).
  - destruct mask as [|[] mask]; [easy| |].
    + rewrite IHt.
      change tBox with (lift n k tBox).
      now rewrite <- distr_lift_subst10.
    + now rewrite IHt.
Qed.

Lemma lift_dearg_aux n k args t :
  lift n k (dearg_aux args t) = dearg_aux (map (lift n k) args) (lift n k t).
Proof.
  induction t in k, args, t |- * using term_forall_list_ind; cbn in *.
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    now destruct (_ <=? _).
  - now rewrite lift_mkApps.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    now rewrite IHt1, IHt2.
  - rewrite IHt1.
    cbn.
    now rewrite IHt2.
  - apply lift_dearg_single.
  - now rewrite lift_dearg_single.
  - destruct p.
    rewrite lift_mkApps.
    f_equal.
    unfold dearg_case.
    destruct (get_mib_masks _); last first.
    + cbn.
      rewrite IHt.
      f_equal.
      induction X; [easy|].
      cbn.
      now rewrite p, IHX.
    + cbn.
      rewrite IHt.
      f_equal.
      unfold mapi.
      generalize 0.
      induction X; [easy|]; intros ?.
      cbn in *.
      rewrite IHX.
      f_equal.
      now rewrite <- dearg_lambdas_lift, p.
  - destruct s as ((ind & c) & npars).
    rewrite lift_mkApps.
    f_equal.
    unfold dearg_proj.
    destruct (get_mib_masks _); cbn; now rewrite IHt.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite map_length.
    induction X in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHX.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite p.
  - rewrite lift_mkApps.
    cbn.
    f_equal.
    f_equal.
    rewrite map_length.
    induction X in k |- *; [easy|].
    cbn in *.
    rewrite <- Nat.add_succ_r.
    rewrite IHX.
    f_equal.
    unfold map_def.
    cbn.
    f_equal.
    now rewrite p.
Qed.

Lemma lift_dearg n k t :
  lift n k (dearg t) = dearg (lift n k t).
Proof. apply lift_dearg_aux. Qed.

Lemma is_dead_lift_other k k' n t :
  k < k' ->
  is_dead k (lift n k' t) = is_dead k t.
Proof.
  intros lt.
  induction t using term_forall_list_ind in t, k, k', lt |- *; cbn in *.
  - easy.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in *);
       lia.
  - easy.
  - induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - easy.
  - easy.
  - rewrite IHt by easy.
    f_equal.
    induction X; [easy|].
    cbn.
    now rewrite p0, IHX.
  - now rewrite IHt.
  - rewrite map_length.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite map_length.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by lia.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
Qed.

Lemma is_dead_lift_all k k' n t :
  k <= k' ->
  k' < n + k ->
  is_dead k' (lift n k t).
Proof.
  intros l1 l2.
  induction t using term_forall_list_ind in t, n, k, k', l1, l2 |- *; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; cbn; propify; lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy.
    cbn.
    clear IHt.
    induction X; [easy|].
    cbn.
    now rewrite p0.
  - rewrite map_length.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite map_length.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
Qed.

Lemma is_dead_subst_other k k' s t :
  k < k' ->
  is_dead k (subst s k' t) = is_dead k t.
Proof.
  intros lt.
  induction t in t, k, k', lt |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?, (_ =? _) eqn:?; propify; subst.
    + lia.
    + destruct (nth_error _ _) eqn:nth.
      * now apply is_dead_lift_all.
      * cbn.
        destruct (_ =? _) eqn:?; propify; [|easy].
        apply nth_error_None in nth.
        lia.
    + cbn.
      now rewrite Nat.eqb_refl.
    + cbn.
      propify.
      lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy; cbn; clear IHt.
    f_equal.
    induction X; [easy|].
    cbn.
    now rewrite p0.
  - rewrite map_length.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
  - rewrite map_length.
    induction X in X, m, k, k', lt |- *; [easy|].
    cbn.
    rewrite p by easy.
    f_equal.
    rewrite <- !Nat.add_succ_r.
    now apply IHX.
Qed.

Lemma valid_dearg_mask_lift mask n k t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (lift n k t).
Proof.
  intros valid.
  induction t in mask, n, k, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    destruct b; [|now apply IHt].
    propify.
    now rewrite is_dead_lift_other by easy.
Qed.

Lemma valid_dearg_mask_subst mask s k t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (subst s k t).
Proof.
  intros valid.
  induction t in mask, k, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now apply valid_dearg_mask_nil.
  - destruct mask; [easy|].
    destruct b; [|now apply IHt].
    propify.
    now rewrite is_dead_subst_other by easy.
Qed.

Lemma subst_dearg_lambdas s k mask t :
  valid_dearg_mask mask t ->
  subst s k (dearg_lambdas mask t) = dearg_lambdas mask (subst s k t).
Proof.
  intros valid.
  induction t in k, mask, t, valid |- *; cbn in *; try easy.
  - destruct mask; [|easy].
    now rewrite dearg_lambdas_nil.
  - destruct mask as [|[] mask]; [easy| |]; cbn in *; propify.
    + unfold subst1.
      now rewrite distr_subst, IHt.
    + now rewrite IHt.
  - now rewrite IHt2.
Qed.

Lemma subst_dearg_case s k ind c discr brs :
  valid_case_masks ind c brs ->
  subst s k (dearg_case ind c discr brs) =
  dearg_case ind c (subst s k discr) (map (on_snd (subst s k)) brs).
Proof.
  intros valid.
  unfold dearg_case, valid_case_masks in *.
  destruct (get_mib_masks _) as [masks|]; [|easy].
  cbn.
  f_equal.
  rewrite map_mapi, mapi_map.
  propify.
  destruct valid as (? & valid).
  eapply Alli_mapi_spec; [apply alli_Alli; eassumption|].
  clear valid.
  intros ? [] valid.
  cbn in *.
  unfold dearg_case_branch.
  cbn.
  f_equal.
  propify.
  now apply subst_dearg_lambdas.
Qed.

Lemma dearg_single_enough_args mask t args :
  dearg_single mask t args =
  mkApps (dearg_single mask t (firstn #|mask| args)) (skipn #|mask| args).
Proof.
  induction mask as [|b mask IH] in mask, t, args |- *; cbn in *.
  - now rewrite skipn_0.
  - destruct args as [|a args].
    + now rewrite skipn_nil.
    + cbn.
      rewrite skipn_cons.
      destruct b; apply IH.
Qed.

Lemma dearg_expanded_aux k t args :
  is_expanded_aux k t ->
  dearg_aux args t = mkApps (dearg_aux (firstn k args) t) (skipn k args).
Proof.
  intros expanded.
  induction t in k, t, args, expanded |- * using term_forall_list_ind; cbn in *;
    refold';
    try now rewrite mkApps_nested, firstn_skipn.
  - propify; intuition auto.
    now erewrite IHt1 by eassumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite mkApps_nested, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_const_mask s| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - propify.
    symmetry; rewrite dearg_single_enough_args; symmetry.
    rewrite mkApps_nested, firstn_firstn.
    replace (Init.Nat.min _ _) with #|get_ctor_mask i n| by lia.
    rewrite dearg_single_enough_args.
    f_equal.
    now rewrite skipn_firstn_slice by assumption.
  - destruct p.
    now rewrite mkApps_nested, firstn_skipn.
  - destruct s as ((ind & c) & npars).
    now rewrite mkApps_nested, firstn_skipn.
Qed.

Lemma dearg_expanded t args :
  is_expanded t ->
  dearg_aux args t = mkApps (dearg t) args.
Proof. apply dearg_expanded_aux. Qed.

Lemma is_expanded_aux_lift k n k' t :
  is_expanded_aux k (lift n k' t) = is_expanded_aux k t.
Proof.
  induction t in n, k, k', t |- * using term_forall_list_ind; cbn in *; auto.
  - now destruct (_ <=? _).
  - induction X; [easy|].
    cbn in *.
    now rewrite p, IHX.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt.
    f_equal.
    induction X; [easy|].
    cbn in *.
    now rewrite p0, IHX.
  - induction X in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in k' |- *; [easy|].
    cbn.
    rewrite <- Nat.add_succ_r.
    now rewrite p, IHX.
Qed.

Lemma is_expanded_lift n k t :
  is_expanded (lift n k t) = is_expanded t.
Proof. apply is_expanded_aux_lift. Qed.

Lemma is_dead_mkApps k t args :
  is_dead k (mkApps t args) = is_dead k t && forallb (is_dead k) args.
Proof.
  induction args using List.rev_ind; cbn in *.
  - now btauto.
  - rewrite mkApps_app, forallb_app.
    cbn.
    rewrite IHargs.
    now btauto.
Qed.

Lemma is_dead_lift k k' n t :
  k' <= k ->
  n + k' <= k ->
  is_dead k (lift n k' t) = is_dead (k - n) t.
Proof.
  intros l1 l2.
  induction t in k, k', n, t, l1, l2 |- * using term_forall_list_ind; cbn in *; auto.
  - repeat
      (try destruct (_ <=? _) eqn:?; propify;
       try destruct (_ =? _) eqn:?; propify;
       cbn in *);
       lia.
  - induction X; [easy|].
    cbn in *.
    now rewrite p.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - rewrite IHt by easy.
    f_equal.
    induction X; cbn in *; [easy|].
    now rewrite p0.
  - rewrite map_length.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHX by easy.
    now replace (S (k - n)) with (S k - n) by lia.
  - rewrite map_length.
    induction X in X, m, k, k', n, l1, l2 |- *; [easy|].
    cbn in *.
    rewrite p by easy.
    cbn.
    rewrite <- !Nat.add_succ_r.
    rewrite IHX by easy.
    now replace (S (k - n)) with (S k - n) by lia.
Qed.

Lemma is_dead_dearg_single k mask t args :
  is_dead k t ->
  Forall (is_dead k) args ->
  is_dead k (dearg_single mask t args).
Proof.
  intros no_use args_no_use.
  induction mask as [|[] mask IH] in k, mask, t, args, no_use, args_no_use |- *; cbn in *.
  - rewrite is_dead_mkApps, no_use.
    now apply forallb_Forall.
  - destruct args; cbn.
    + apply IH; [|easy].
      rewrite is_dead_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + apply IH; [easy|].
      now inversion args_no_use.
  - destruct args; cbn.
    + apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      rewrite is_dead_lift by lia.
      cbn.
      now rewrite Nat.sub_0_r.
    + inversion args_no_use.
      apply IH; [|easy].
      cbn.
      now propify.
Qed.

Ltac bia :=
  repeat (destruct (is_dead _ _); cbn;
          rewrite ?Bool.orb_true_r, ?Bool.orb_false_r, ?Bool.andb_false_r; auto).

Lemma is_dead_subst s k k' t :
  k' <= k ->
  is_dead k (subst [s] k' t) =
  is_dead (S k) t && (is_dead k' t || is_dead (k - k') s).
Proof.
  intros le.
  induction t in t, k, k', le |- * using term_forall_list_ind; cbn in *; auto.
  - destruct (_ <=? _) eqn:?; propify; cbn.
    + destruct (nth_error _ _) eqn:nth.
      * replace n with k' in * by (now apply nth_error_Some_length in nth; cbn in * ).
        rewrite Nat.sub_diag in nth.
        cbn in *.
        noconf nth.
        rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq _ _)) by easy.
        now rewrite is_dead_lift.
      * cbn.
        apply nth_error_None in nth.
        cbn in *.
        repeat (destruct (_ =? _) eqn:?; propify); auto; try lia.
    + destruct (n =? k) eqn:?, (n =? S k) eqn:?, (n =? k') eqn:?; propify; cbn in *; auto; lia.
   - induction X; [easy|].
     cbn.
     rewrite !p, !IHX by easy.
     bia.
   - now rewrite IHt.
   - rewrite IHt1, IHt2 by easy.
     replace (S k - S k') with (k - k') by lia.
     bia.
   - rewrite IHt1, IHt2 by easy.
     bia.
   - rewrite IHt by easy.
     clear IHt.
     induction X; cbn in *; [bia|].
     rewrite p0 by easy.
     bia; cbn in *.
     + now rewrite Bool.orb_true_r in IHX.
     + now rewrite Bool.orb_false_r in IHX.
   - rewrite map_length.
     induction X in X, m, k, k', le |- *; cbn in *; [easy|].
     rewrite p by easy.
     specialize (IHX (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHX.
     bia.
   - rewrite map_length.
     induction X in X, m, k, k', le |- *; cbn in *; [easy|].
     rewrite p by easy.
     specialize (IHX (S k) (S k') ltac:(lia)).
     rewrite !Nat.sub_succ in *.
     replace (#|l| + k - (#|l| + k')) with (k - k') by lia.
     rewrite <- !Nat.add_succ_r.
     rewrite IHX.
     bia.
Qed.

Lemma is_dead_dearg_lambdas k mask t :
  is_dead k (dearg_lambdas mask t) = is_dead k t.
Proof.
  induction t in k, mask, t |- *; cbn in *; try easy.
  destruct mask as [|[] mask]; [easy| |]; cbn in *.
  - unfold subst1.
    rewrite is_dead_subst, IHt, Nat.sub_0_r by easy.
    cbn.
    now btauto.
  - now rewrite IHt.
Qed.

Lemma is_dead_dearg_case k ind npars discr brs :
  is_dead k (dearg_case ind npars discr brs) =
  is_dead k discr && forallb (is_dead k) (map snd brs).
Proof.
  unfold dearg_case.
  destruct (get_mib_masks _); cbn; [|now rewrite forallb_map].
  f_equal.
  unfold mapi.
  generalize 0.
  induction brs; intros; [easy|].
  cbn in *.
  rewrite IHbrs.
  f_equal.
  now rewrite is_dead_dearg_lambdas.
Qed.

Lemma is_dead_dearg_aux k t args :
  is_dead k t ->
  Forall (is_dead k) args ->
  is_dead k (dearg_aux args t).
Proof.
  intros no_use args_no_use.
  induction t using term_forall_list_ind in k, t, args, no_use, args_no_use |- *;
    cbn in *; rewrite ?is_dead_mkApps; cbn.
  - now apply forallb_Forall.
  - now rewrite no_use; apply forallb_Forall.
  - now apply forallb_Forall.
  - propify; split; [|now apply forallb_Forall].
    induction X; [easy|]; cbn in *; propify.
    now rewrite p, IHX.
  - rewrite IHt by easy.
    now apply forallb_Forall.
  - propify.
    rewrite IHt1, IHt2 by easy.
    split; [easy|now apply forallb_Forall].
  - propify.
    now rewrite IHt1.
  - now apply is_dead_dearg_single.
  - now apply is_dead_dearg_single.
  - destruct p.
    rewrite is_dead_mkApps, is_dead_dearg_case.
    propify.
    split; [|now apply forallb_Forall].
    split; [now apply IHt|].
    induction X; [easy|]; cbn in *; propify.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - destruct s as ((ind & c) & npars).
    rewrite is_dead_mkApps.
    propify; split; [|now apply forallb_Forall].
    unfold dearg_proj.
    now destruct (get_mib_masks _); apply IHt.
  - rewrite map_length.
    propify; split; [|now apply forallb_Forall].
    induction X in k, m, X, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
  - rewrite map_length.
    propify; split; [|now apply forallb_Forall].
    induction X in k, m, X, no_use |- *; [easy|].
    cbn in *; propify.
    rewrite <- !Nat.add_succ_r in *.
    rewrite p by easy.
    split; [easy|].
    now apply IHX.
Qed.

Lemma valid_dearg_mask_dearg mask t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (dearg t).
Proof.
  intros valid.
  induction t in mask, t, valid |- *; cbn in *; try easy;
    try solve [destruct mask; [|easy]; apply valid_dearg_mask_nil].
  destruct mask as [|[] mask]; try easy.
  cbn in *.
  propify.
  now rewrite is_dead_dearg_aux.
Qed.

Lemma valid_case_masks_dearg_branches ind npars brs :
  valid_case_masks ind npars brs ->
  valid_case_masks ind npars (map (on_snd dearg) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  destruct valid.
  split; [easy|].
  apply Alli_alli.
  apply alli_Alli in H0.
  apply Alli_map.
  eapply Alli_impl; [eassumption|].
  cbn.
  intros n [] valid.
  propify.
  split; [easy|].
  now apply valid_dearg_mask_dearg.
Qed.

Lemma dearg_aux_subst s k t args :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg_aux (map (subst (map dearg s) k ∘ dearg) args) (subst s k t) =
  subst (map dearg s) k (dearg_aux (map dearg args) t).
Proof.
  intros vcases es.
  induction t using term_forall_list_ind in s, k, t, args, vcases, es |- *; cbn in *; refold'.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    destruct (_ <=? _) eqn:?; propify; [|easy].
    rewrite nth_error_map.
    destruct (nth_error _ _) eqn:nth; cbn.
    + rewrite dearg_expanded, lift_dearg; [easy|].
      rewrite is_expanded_lift.
      now eapply nth_error_forall in nth; [|eassumption].
    + now rewrite map_length.
  - now rewrite subst_mkApps, map_map.
  - rewrite subst_mkApps, map_map.
    cbn in *.
    rewrite !map_map.
    f_equal.
    f_equal.
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal.
    + now apply (p _ _ []).
    + now apply IHX.
  - rewrite subst_mkApps, map_map.
    cbn.
    f_equal.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    propify.
    f_equal.
    f_equal.
    + now apply (IHt1 _ _ []).
    + now apply (IHt2 _ _ []).
  - propify.
    specialize (IHt1 s k (t2 :: args)).
    cbn in *.
    rewrite <- IHt1 by easy.
    f_equal.
    f_equal.
    now apply (IHt2 _ _ []).
  - now rewrite subst_dearg_single, map_map.
  - now rewrite subst_dearg_single, map_map.
  - destruct p.
    propify.
    rewrite subst_mkApps, !map_map, subst_dearg_case by (now apply valid_case_masks_dearg_branches).
    f_equal.
    f_equal; [now apply (IHt _ _ [])|].
    destruct vcases as ((_ & vcases) & _).
    clear -X vcases es X.
    induction X; [easy|].
    cbn in *.
    propify.
    f_equal; [f_equal|].
    + now apply (p _ _ []).
    + now apply IHX.
  - destruct s0 as ((ind & c) & npars).
    rewrite subst_mkApps, map_map.
    f_equal.
    unfold dearg_proj.
    cbn in *; propify.
    f_equal.
    now apply (IHt _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite map_length.
    revert k; induction X; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHX].
    unfold map_def; cbn.
    f_equal.
    now apply (p _ _ []).
  - rewrite subst_mkApps, map_map.
    cbn.
    rewrite !map_map.
    f_equal.
    cbn.
    f_equal.
    rewrite map_length.
    revert k; induction X; intros k; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    f_equal; [|now apply IHX].
    unfold map_def; cbn.
    f_equal.
    now apply (p _ _ []).
Qed.

Lemma dearg_subst s k t :
  valid_cases t ->
  Forall (fun s => is_expanded s) s ->
  dearg (subst s k t) = subst (map dearg s) k (dearg t).
Proof. now intros; apply (dearg_aux_subst _ _ _ []). Qed.

Lemma valid_cases_mkApps_inv hd args :
  valid_cases (mkApps hd args) ->
  valid_cases hd /\ Forall valid_cases args.
Proof.
  intros valid.
  induction args using List.rev_ind; [easy|].
  rewrite mkApps_app in *.
  cbn in *.
  propify.
  intuition auto.
  apply app_Forall; intuition.
Qed.

Lemma is_expanded_aux_mkApps_eq n hd args :
  is_expanded_aux n (mkApps hd args) =
  is_expanded_aux (n + #|args|) hd && forallb is_expanded args.
Proof.
  induction args in args, n |- * using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, forallb_app.
    cbn.
    rewrite IHargs.
    rewrite app_length, Bool.andb_true_r.
    cbn in *.
    rewrite !Bool.andb_assoc.
    symmetry; rewrite Bool.andb_comm; symmetry.
    rewrite <- !Bool.andb_assoc.
    f_equal.
    f_equal.
    f_equal.
    lia.
Qed.

Lemma is_expanded_mkApps_eq hd args :
  is_expanded (mkApps hd args) = is_expanded_aux #|args| hd && forallb is_expanded args.
Proof. now apply is_expanded_aux_mkApps_eq. Qed.

Lemma is_expanded_aux_mkApps_inv n hd args :
  is_expanded_aux n (mkApps hd args) ->
  is_expanded_aux (n + #|args|) hd /\ Forall is_expanded args.
Proof.
  intros exp.
  rewrite is_expanded_aux_mkApps_eq in exp.
  propify.
  split; [easy|].
  now apply forallb_Forall.
Qed.

Lemma is_expanded_aux_mkApps n hd args :
  is_expanded_aux (n + #|args|) hd ->
  Forall (fun a => is_expanded a) args ->
  is_expanded_aux n (mkApps hd args).
Proof.
  intros exp_hd exp_args.
  rewrite is_expanded_aux_mkApps_eq.
  rewrite exp_hd.
  now apply forallb_Forall.
Qed.

Lemma is_expanded_aux_upwards n t n' :
  is_expanded_aux n t ->
  n <= n' ->
  is_expanded_aux n' t.
Proof.
  intros exp l.
  induction t in n, t, n', l, exp |- * using term_forall_list_ind; cbn in *; propify; easy.
Qed.

Lemma is_expanded_csubst s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (csubst s k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (Nat.compare_spec k n0) as [<-| |].
    + now eapply is_expanded_aux_upwards.
    + easy.
    + easy.
  - easy.
  - induction X; [easy|].
    cbn in *; propify.
    now rewrite p, IHX.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    rewrite IHt by easy.
    split; [easy|].
    induction X; [easy|].
    cbn in *.
    propify.
    now rewrite p0, IHX.
  - easy.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
Qed.

Lemma is_expanded_aux_subst s n t k :
  is_expanded_aux 0 s ->
  is_expanded_aux n t ->
  is_expanded_aux n (subst [s] k t).
Proof.
  intros exps expt.
  induction t in s, n, t, k, exps, expt |- * using term_forall_list_ind; cbn in *.
  - easy.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      rewrite is_expanded_aux_lift.
      now eapply is_expanded_aux_upwards.
    + now rewrite nth_error_nil in nth.
  - easy.
  - induction X; [easy|].
    cbn in *; propify.
    now rewrite p, IHX.
  - now apply IHt.
  - now propify.
  - now propify.
  - easy.
  - easy.
  - propify.
    rewrite IHt by easy.
    split; [easy|].
    induction X; [easy|].
    cbn in *.
    propify.
    now rewrite p0, IHX.
  - easy.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
  - induction X in m, X, k, expt |- *; [easy|].
    cbn in *.
    propify.
    rewrite <- !Nat.add_succ_r.
    now rewrite p, IHX.
Qed.

Lemma is_expanded_substl s n t :
  Forall (fun s => is_expanded s) s ->
  is_expanded_aux n t ->
  is_expanded_aux n (substl s t).
Proof.
  intros all exp.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in all.
  now apply is_expanded_csubst.
Qed.

Lemma Forall_is_expanded_fix_subst defs :
  Forall (is_expanded ∘ dbody) defs ->
  Forall is_expanded (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma Forall_is_expanded_cofix_subst defs :
  Forall (is_expanded ∘ dbody) defs ->
  Forall is_expanded (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma is_expanded_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_fix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl; [|easy].
  now apply Forall_is_expanded_fix_subst.
Qed.

Lemma is_expanded_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  Forall (fun d => is_expanded (dbody d)) defs ->
  is_expanded f.
Proof.
  intros cuf all.
  unfold cunfold_cofix in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forall in nth; [|eassumption].
  noconf cuf.
  apply is_expanded_substl; [|easy].
  now apply Forall_is_expanded_cofix_subst.
Qed.

Lemma lookup_env_Forall {P} Σ kn decl :
  lookup_env Σ kn = Some decl ->
  Forall P Σ ->
  P (kn, decl).
Proof.
  intros look all.
  rewrite lookup_env_find in look.
  destruct find as [(? & decl')|] eqn:find; cbn in *; [|congruence].
  noconf look.
  apply find_some in find as (isin & name_eq).
  unfold eq_kername in *.
  destruct kername_eq_dec as [->|]; [|congruence].
  rewrite Forall_forall in all.
  eauto.
Qed.

Lemma is_expanded_constant Σ kn cst body :
  is_expanded_env Σ ->
  declared_constant Σ kn cst ->
  cst_body cst = Some body ->
  is_expanded body.
Proof.
  intros exp_env decl body_eq.
  unfold is_expanded_env in *.
  apply forallb_Forall in exp_env.
  eapply lookup_env_Forall in exp_env; eauto.
  destruct cst; cbn in *.
  now rewrite body_eq in exp_env.
Qed.

Lemma eval_is_expanded_aux {wfl:WcbvFlags} Σ t v k :
  Σ e⊢ t ▷ v ->
  is_expanded_env Σ ->
  is_expanded_aux k t ->
  is_expanded_aux k v .
Proof.
  intros ev exp_env exp_t.
  induction ev in t, v, k, ev, exp_t |- *; auto; cbn in *; propify.
  - apply IHev3.
    apply is_expanded_csubst; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    apply is_expanded_csubst; intuition auto.
    now eapply is_expanded_aux_upwards.
  - apply IHev2.
    unfold ETyping.iota_red.
    specialize (IHev1 0 ltac:(easy)).
    apply is_expanded_aux_mkApps_inv in IHev1 as (exp_hd & exp_args); cbn in *.
    apply is_expanded_aux_mkApps.
    + rewrite nth_nth_error.
      destruct (nth_error _ _) eqn:nth; [|easy].
      eapply nth_error_forall in nth; [|now eapply forallb_Forall].
      now eapply is_expanded_aux_upwards.
    + now apply Forall_skipn.
  - apply IHev2.
    apply is_expanded_aux_mkApps.
    + subst brs.
      cbn in *.
      now propify; eapply is_expanded_aux_upwards.
    + now apply Forall_repeat.
  - apply IHev3; clear IHev3.
    specialize (IHev1 (S k)).
    specialize (IHev2 0).
    propify; split; [easy|].
    intuition auto.
    apply is_expanded_aux_mkApps_inv in H2 as (? & ?).
    apply is_expanded_aux_mkApps.
    + apply (is_expanded_aux_upwards 0); [|lia].
      eapply is_expanded_cunfold_fix; [eassumption|].
      now apply forallb_Forall.
    + easy.
  - easy.
  - apply IHev; clear IHev.
    propify; split; [|easy].
    destruct exp_t.
    apply is_expanded_aux_mkApps_inv in H as (exp_cofix & exp_args).
    apply is_expanded_aux_mkApps; [|easy].
    apply (is_expanded_aux_upwards 0); [|easy].
    eapply is_expanded_cunfold_cofix; [eassumption|].
    now apply forallb_Forall.
  - apply IHev; clear IHev.
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_cofix & exp_args).
    apply is_expanded_aux_mkApps; [|easy].
    apply (is_expanded_aux_upwards 0); [|easy].
    eapply is_expanded_cunfold_cofix; [eassumption|].
    now apply forallb_Forall.
  - apply IHev.
    apply (is_expanded_aux_upwards 0); [|easy].
    now eapply is_expanded_constant.
  - apply IHev2; clear IHev2.
    specialize (IHev1 _ exp_t).
    apply is_expanded_aux_mkApps_inv in IHev1 as (exp_hd & exp_args).
    rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    eapply nth_error_forall in nth; [|eassumption].
    now apply (is_expanded_aux_upwards 0).
  - easy.
Qed.

Lemma valid_case_masks_lift ind c brs n k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (on_snd (lift n k)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  split; [easy|].
  destruct valid as (_ & valid).
  apply Alli_alli.
  apply alli_Alli in valid.
  apply Alli_map.
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *; propify.
  split; [easy|].
  now apply valid_dearg_mask_lift.
Qed.

Lemma valid_case_masks_subst ind c brs s k :
  valid_case_masks ind c brs ->
  valid_case_masks ind c (map (on_snd (subst s k)) brs).
Proof.
  intros valid.
  unfold valid_case_masks in *.
  destruct (get_mib_masks _); [|easy].
  propify.
  split; [easy|].
  destruct valid as (_ & valid).
  apply Alli_alli.
  apply alli_Alli in valid.
  apply Alli_map.
  eapply Alli_impl; [eassumption|].
  intros ? [] val_branch.
  cbn in *; propify.
  split; [easy|].
  now apply valid_dearg_mask_subst.
Qed.

Lemma valid_cases_lift t n k :
  valid_cases t ->
  valid_cases (lift n k t).
Proof.
  intros valid_t.
  induction t in t, k, valid_t |- * using term_forall_list_ind; cbn in *; propify; auto.
  - now destruct (_ <=? _).
  - induction X; [easy|].
    cbn in *.
    now propify.
  - easy.
  - easy.
  - destruct p.
    propify.
    split; [|now apply valid_case_masks_lift].
    split; [easy|].
    destruct valid_t as ((_ & valid) & _).
    induction X; [easy|].
    cbn in *.
    now propify.
  - destruct s as ((ind & npars) & arg).
    now propify.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *.
    propify.
    now rewrite <- !Nat.add_succ_r.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *.
    propify.
    now rewrite <- !Nat.add_succ_r.
Qed.

Lemma valid_cases_subst s k t :
  valid_cases s ->
  valid_cases t ->
  valid_cases (subst [s] k t).
Proof.
  intros valid_s valid_t.
  induction t in k, t, valid_t |- * using term_forall_list_ind; cbn in *; propify; auto.
  - destruct (_ <=? _); [|easy].
    destruct (nth_error _ _) eqn:nth; [|easy].
    destruct (_ - _); cbn in *.
    + noconf nth.
      now apply valid_cases_lift.
    + now rewrite nth_error_nil in nth.
  - induction X; [easy|].
    now cbn in *; propify.
  - easy.
  - easy.
  - destruct p.
    cbn in *; propify.
    split; [|now apply valid_case_masks_subst].
    split; [easy|].
    destruct valid_t as ((_ & valid) & _).
    induction X; [easy|].
    now cbn in *; propify.
  - destruct s0 as ((ind & npars) & arg).
    now propify.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *; propify.
    now rewrite <- !Nat.add_succ_r.
  - induction X in X, k, valid_t |- *; [easy|].
    cbn in *; propify.
    now rewrite <- !Nat.add_succ_r.
Qed.

Lemma closedn_dearg_single k t args mask :
  closedn k t ->
  Forall (closedn k) args ->
  closedn k (dearg_single mask t args).
Proof.
  intros clos_t clos_args.
  induction mask as [|[] mask IH] in k, t, args, mask, clos_t, clos_args |- *; cbn in *.
  - now apply closedn_mkApps.
  - depelim clos_args; [|easy].
    cbn in *.
    apply IH; [|easy].
    pose proof (closedn_lift 1 k).
    now rewrite Nat.add_1_r in H.
  - depelim clos_args.
    + cbn.
      apply IH; [|easy].
      cbn.
      rewrite Bool.andb_true_r.
      pose proof (closedn_lift 1 k).
      now rewrite Nat.add_1_r in H.
    + apply IH; [|easy].
      cbn.
      now propify.
Qed.

Lemma closedn_dearg_lambdas k mask t :
  closedn k t ->
  closedn k (dearg_lambdas mask t).
Proof.
  intros clos.
  induction t in k, mask, t, clos |- *; auto; cbn in *.
  - destruct mask; [easy|].
    destruct b; [|easy].
    apply closedn_subst0; [easy|].
    now cbn; rewrite Nat.add_1_r.
  - now propify.
Qed.

Lemma closedn_dearg_aux k args t :
  closedn k t ->
  Forall (closedn k) args ->
  closedn k (dearg_aux args t).
Proof.
  intros clos_t clos_args.
  induction t in k, args, clos_t, clos_args |- * using term_forall_list_ind; cbn in *;
    try solve [now apply closedn_mkApps].
  - apply closedn_mkApps; [|easy].
    cbn.
    induction X; [easy|].
    cbn in *.
    now propify.
  - apply closedn_mkApps; [|easy].
    cbn.
    now propify.
  - propify.
    apply IHt1; [easy|].
    now constructor.
  - now apply closedn_dearg_single.
  - now apply closedn_dearg_single.
  - destruct p.
    apply closedn_mkApps; [|easy].
    unfold dearg_case.
    destruct (get_mib_masks _); cbn in *; propify; cycle 1.
    { split; [now apply IHt|].
      destruct clos_t as (_ & clos_brs).
      induction X; [easy|].
      now cbn in *; propify. }

    split; [now apply IHt|].
    destruct clos_t as (_ & clos_brs).
    unfold mapi.
    generalize 0.
    induction X; [easy|]; intros n'.
    cbn in *; propify.
    now split; [apply closedn_dearg_lambdas|].
  - destruct s as ((ind & c) & npars).
    apply closedn_mkApps; [|easy].
    unfold dearg_proj.
    now destruct (get_mib_masks _); apply IHt.
  - apply closedn_mkApps; [|easy].
    cbn.
    rewrite map_length.
    induction X in k, args, X, clos_t |- *; [easy|].
    cbn in *; propify.
    split; [easy|].
    rewrite <- !Nat.add_succ_r in *.
    now apply IHX.
  - apply closedn_mkApps; [|easy].
    cbn.
    rewrite map_length.
    induction X in k, args, X, clos_t |- *; [easy|].
    cbn in *; propify.
    split; [easy|].
    rewrite <- !Nat.add_succ_r in *.
    now apply IHX.
Qed.

Hint Resolve
     closedn_subst0 closed_mkApps closedn_dearg_aux closed_iota_red
     is_expanded_aux_subst is_expanded_aux_mkApps
     valid_cases_subst : dearg.
Hint Constructors Forall : dearg.

Lemma valid_cases_mkApps hd args :
  valid_cases hd ->
  Forall valid_cases args ->
  valid_cases (mkApps hd args).
Proof.
  intros valid_hd valid_args.
  induction args as [|a args IH] using List.rev_ind; [easy|].
  rewrite mkApps_app.
  cbn; propify.
  now apply Forall_snoc in valid_args.
Qed.

Lemma valid_cases_iota_red pars c args brs :
  Forall valid_cases args ->
  Forall (fun t => valid_cases t.2) brs ->
  valid_cases (iota_red pars c args brs).
Proof.
  intros valid_args valid_brs.
  unfold iota_red.
  apply valid_cases_mkApps.
  - rewrite nth_nth_error.
    destruct (nth_error _ _) eqn:nth; [|easy].
    now eapply nth_error_forall in nth; [|eassumption].
  - now eapply Forall_skipn.
Qed.

Lemma valid_cases_substl s t :
  Forall (fun s => closed s) s ->
  Forall valid_cases s ->
  valid_cases t ->
  valid_cases (substl s t).
Proof.
  intros clos_s valid_s valid_t.
  unfold substl.
  induction s using List.rev_ind; [easy|].
  rewrite fold_left_app.
  cbn.
  apply Forall_snoc in clos_s as (? & ?).
  apply Forall_snoc in valid_s as (? & ?).
  rewrite closed_subst by easy.
  now apply valid_cases_subst.
Qed.

Lemma Forall_closed_fix_subst defs :
  Forall (closedn #|defs| ∘ dbody) defs ->
  Forall (closedn 0) (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - apply forallb_Forall.
    eapply Forall_impl; [eassumption|].
    intros.
    now rewrite Nat.add_0_r.
  - now apply IHl.
Qed.

Lemma Forall_closed_cofix_subst defs :
  Forall (closedn #|defs| ∘ dbody) defs ->
  Forall (closedn 0) (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - apply forallb_Forall.
    eapply Forall_impl; [eassumption|].
    intros.
    now rewrite Nat.add_0_r.
  - now apply IHl.
Qed.

Lemma Forall_valid_cases_fix_subst defs :
  Forall (valid_cases ∘ dbody) defs ->
  Forall valid_cases (fix_subst defs).
Proof.
  intros all.
  unfold fix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma Forall_valid_cases_cofix_subst defs :
  Forall (valid_cases ∘ dbody) defs ->
  Forall valid_cases (cofix_subst defs).
Proof.
  intros all.
  unfold cofix_subst.
  induction defs at 2; constructor; cbn in *.
  - now apply forallb_Forall.
  - now apply IHl.
Qed.

Lemma valid_cases_cunfold_fix defs i narg f :
  cunfold_fix defs i = Some (narg, f) ->
  closed (tFix defs i) ->
  valid_cases (tFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_fix in *.
  cbn in *.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  eapply nth_error_forallb in clos_defs as ?.
  eapply nth_error_forallb in valid_defs as ?.
  rewrite nth in *.
  cbn in *.
  noconf cuf.
  apply valid_cases_substl.
  - apply Forall_closed_fix_subst.
    apply forallb_Forall.
    eapply forallb_impl; [|exact clos_defs].
    intros.
    now rewrite Nat.add_0_r in *.
  - apply Forall_valid_cases_fix_subst.
    now apply forallb_Forall.
  - easy.
Qed.

Lemma valid_cases_cunfold_cofix defs i narg f :
  cunfold_cofix defs i = Some (narg, f) ->
  closed (tCoFix defs i) ->
  valid_cases (tCoFix defs i) ->
  valid_cases f.
Proof.
  intros cuf clos_defs valid_defs.
  unfold cunfold_cofix in *.
  cbn in *.
  eapply nth_error_forallb in clos_defs as ?.
  eapply nth_error_forallb in valid_defs as ?.
  destruct (nth_error _ _) eqn:nth; [|congruence].
  rewrite nth in *.
  cbn in *.
  noconf cuf.
  apply valid_cases_substl.
  - apply Forall_closed_cofix_subst.
    apply forallb_Forall.
    eapply forallb_impl; [|exact clos_defs].
    intros.
    now rewrite Nat.add_0_r in *.
  - apply Forall_valid_cases_cofix_subst.
    now apply forallb_Forall.
  - easy.
Qed.

Lemma valid_cases_constant Σ kn cst body :
  valid_masks_env Σ ->
  declared_constant Σ kn cst ->
  cst_body cst = Some body ->
  valid_cases body.
Proof.
  intros valid_env decl_const body_eq.
  eapply forallb_Forall, lookup_env_Forall in valid_env; eauto.
  destruct cst; cbn in *.
  rewrite body_eq in valid_env.
  now propify.
Qed.

Lemma valid_dearg_mask_constant Σ kn cst body :
  valid_masks_env Σ ->
  declared_constant Σ kn cst ->
  cst_body cst = Some body ->
  valid_dearg_mask (get_const_mask kn) body.
Proof.
  intros valid_env decl_const body_eq.
  eapply forallb_Forall, lookup_env_Forall in valid_env; eauto.
  destruct cst; cbn in *.
  rewrite body_eq in valid_env.
  now propify.
Qed.

Lemma eval_valid_cases {wfl:WcbvFlags} Σ t v :
  Σ e⊢ t ▷ v ->

  env_closed Σ ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  valid_cases v.
Proof with auto with dearg.
  intros ev clos_env clos_t valid_env valid_t.
  induction ev in t, v, ev, clos_t, valid_t |- *; auto; cbn in *; propify.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    rewrite closed_subst in * by easy.
    apply IHev3; [apply closedn_subst0|apply valid_cases_subst]...
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    rewrite closed_subst in * by easy.
    apply IHev2; [apply closedn_subst0|apply valid_cases_subst]...
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    apply closed_mkApps_inv in H1 as (? & ?).
    assert (closed (iota_red pars c args brs)).
    { apply closed_iota_red; auto.
      now apply forallb_Forall. }
    eapply eval_closed in ev2 as ?...
    eapply valid_cases_mkApps_inv in H5 as (? & ?).
    apply IHev2...
    apply valid_cases_iota_red...
    apply forallb_Forall...
  - subst brs.
    cbn in *.
    propify.
    intuition auto.
    apply IHev2.
    + apply closed_mkApps...
      now apply Forall_repeat.
    + apply valid_cases_mkApps...
      now apply Forall_repeat.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply eval_closed in ev2 as ?...
    apply closed_mkApps_inv in H6 as (? & ?).
    apply valid_cases_mkApps_inv in H5 as (? & ?).
    apply H4...
    + apply closed_mkApps...
      now eapply closed_cunfold_fix.
    + split; [|easy].
      apply valid_cases_mkApps...
      eapply valid_cases_cunfold_fix; [eassumption| |]...
  - easy.
  - destruct ip.
    propify.
    intuition auto.
    apply closed_mkApps_inv in H as (? & ?).
    apply valid_cases_mkApps_inv in H3 as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    assert (closed (mkApps fn args)) by (now apply closed_mkApps).
    eapply eval_closed in ev as ?...
    + apply H1...
      intuition auto...
      apply valid_cases_mkApps...
      now eapply valid_cases_cunfold_cofix.
    + now cbn; propify.
  - destruct p as ((ind & npars) & arg).
    apply closed_mkApps_inv in clos_t as (? & ?).
    propify.
    destruct valid_t as (valid_t & valid_proj).
    apply valid_cases_mkApps_inv in valid_t as (? & ?).
    assert (closed fn) by (now eapply closed_cunfold_cofix).
    apply IHev.
    + now apply closed_mkApps.
    + split; [|easy].
      apply valid_cases_mkApps...
      now eapply valid_cases_cunfold_cofix.
  - apply IHev.
    + now eapply closed_constant.
    + now eapply valid_cases_constant.
  - intuition auto.
    eapply eval_closed in ev1 as ?...
    eapply closed_mkApps_inv in H1 as (? & ?).
    eapply valid_cases_mkApps_inv in H2 as (? & ?).
    rewrite (nth_nth_error (pars + arg) args tDummy) in *.
    destruct (nth_error _ _) eqn:nth; [|now apply IHev2].
    eapply nth_error_forall in H4; [|eassumption].
    eapply nth_error_forall in H3; [|eassumption].
    now apply IHev2.
  - easy.
Qed.

Lemma lookup_env_dearg_env Σ kn :
  lookup_env (dearg_env Σ) kn = option_map (dearg_decl kn) (lookup_env Σ kn).
Proof.
  unfold lookup_env.
  induction Σ as [|((kn', has_deps), decl) Σ IH]; [easy|].
  cbn.
  unfold eq_kername.
  destruct kername_eq_dec as [->|]; [easy|].
  apply IH.
Qed.

Lemma declared_constant_dearg Σ k cst :
  declared_constant Σ k cst ->
  ∑ cst',
    declared_constant (dearg_env Σ) k cst' ×
    cst_body cst' = option_map (dearg ∘ dearg_lambdas (get_const_mask k))
                               (EAst.cst_body cst).
Proof.
  unfold declared_constant.
  rewrite lookup_env_dearg_env.
  intros typ.
  destruct lookup_env as [decl|]; cbn in *; [|congruence].
  noconf typ.
  cbn.
  eauto.
Qed.

Inductive dearg_spec : term -> term -> Type :=
| dearg_spec_const kn args :
    dearg_spec (mkApps (tConst kn) args)
               (dearg_single (get_const_mask kn) (tConst kn) (map dearg args))
| dearg_spec_ctor ind c args :
    dearg_spec (mkApps (tConstruct ind c) args)
               (dearg_single (get_ctor_mask ind c) (tConstruct ind c) (map dearg args))
| dearg_spec_case ind npars discr brs args :
    dearg_spec (mkApps (tCase (ind, npars) discr brs) args)
               (mkApps (dearg (tCase (ind, npars) discr brs))
                       (map dearg args))
| dearg_spec_proj ind c npars t args :
    dearg_spec (mkApps (tProj (ind, c, npars) t) args)
               (mkApps (dearg (tProj (ind, c, npars) t)) (map dearg args))
| dearg_spec_other hd args :
    match hd with
    | tConst _
    | tConstruct _ _
    | tCase _ _ _
    | tProj _ _
    | tApp _ _ => False
    | _ => True
    end ->
    dearg_spec (mkApps hd args) (mkApps (dearg hd) (map dearg args)).

Lemma dearg_elim t :
  dearg_spec t (dearg t).
Proof.
  destruct (mkApps_elim t []).
  generalize (firstn n l) as args.
  clear n.
  intros args.
  rewrite dearg_mkApps.
  destruct f; try solve [now econstructor].
  - easy.
  - cbn in *.
    destruct p.
    eapply dearg_spec_case.
  - cbn in *.
    destruct p as ((? & ?) & ?).
    eapply dearg_spec_proj.
Qed.

Lemma valid_cases_dearg_lambdas mask t :
  valid_cases t ->
  valid_cases (dearg_lambdas mask t).
Proof.
  intros valid.
  induction t in mask, valid |- * using term_forall_list_ind; cbn in *; propify; try easy.
  destruct mask as [|[] mask]; try easy.
  now apply valid_cases_subst.
Qed.

Lemma dearg_dearg_lambdas mask t :
  valid_dearg_mask mask t ->
  valid_cases t ->
  dearg (dearg_lambdas mask t) = dearg_lambdas mask (dearg t).
Proof.
  intros vm vc.
  induction t in mask, vm, vc |- * using term_forall_list_ind; cbn in *; propify; try easy;
    try solve [destruct mask; [|easy]; now rewrite dearg_lambdas_nil].
  - destruct mask as [|[] mask]; cbn in *; propify; try easy.
    + refold'.
      unfold subst1.
      rewrite dearg_subst; cbn in *.
      * now rewrite IHt.
      * now apply valid_cases_dearg_lambdas.
      * easy.
    + refold'; now rewrite IHt.
  - now refold'; rewrite IHt2.
Qed.

Lemma dearg_substl s t :
  Forall (closedn 0) s ->
  Forall valid_cases s ->
  Forall is_expanded s ->
  valid_cases t ->
  dearg (substl s t) = substl (map dearg s) (dearg t).
Proof.
  intros clos valid exp valid_t.
  induction s using List.rev_ind; [easy|].
  unfold substl.
  rewrite map_app, !fold_left_app.
  cbn.
  apply Forall_snoc in clos.
  apply Forall_snoc in valid.
  apply Forall_snoc in exp.
  rewrite closed_subst by easy.
  refold'.
  rewrite dearg_subst.
  - cbn.
    rewrite <- closed_subst by (now apply closedn_dearg_aux).
    f_equal.
    now apply IHs.
  - now apply valid_cases_substl.
  - easy.
Qed.

Lemma fix_subst_dearg defs :
  fix_subst (map (map_def dearg) defs) = map dearg (fix_subst defs).
Proof.
  unfold fix_subst.
  rewrite map_length.
  induction #|defs|; [easy|].
  cbn in *.
  f_equal.
  apply IHn.
Qed.

Lemma cofix_subst_dearg defs :
  cofix_subst (map (map_def dearg) defs) = map dearg (cofix_subst defs).
Proof.
  unfold cofix_subst.
  rewrite map_length.
  induction #|defs|; [easy|].
  cbn in *.
  f_equal.
  apply IHn.
Qed.

Lemma dearg_cunfold_fix defs i narg fn :
  cunfold_fix defs i = Some (narg, fn) ->
  closed (tFix defs i) ->
  valid_cases (tFix defs i) ->
  is_expanded (tFix defs i) ->
  cunfold_fix (map (map_def dearg) defs) i = Some (narg, dearg fn).
Proof.
  intros cuf clos_fix valid_fix exp_fix.
  cbn in *.
  unfold cunfold_fix in *.
  rewrite nth_error_map.
  destruct (nth_error _ _) eqn:nth; [|easy].
  cbn in *.
  noconf cuf.
  f_equal.
  f_equal.
  rewrite dearg_substl.
  - f_equal; apply fix_subst_dearg.
  - apply Forall_closed_fix_subst.
    setoid_rewrite Nat.add_0_r in clos_fix.
    now apply forallb_Forall.
  - apply Forall_valid_cases_fix_subst.
    now apply forallb_Forall.
  - apply Forall_is_expanded_fix_subst.
    now apply forallb_Forall.
  - eapply nth_error_forallb in valid_fix.
    now rewrite nth in valid_fix.
Qed.

Lemma dearg_cunfold_cofix defs i narg fn :
  cunfold_cofix defs i = Some (narg, fn) ->
  closed (tCoFix defs i) ->
  valid_cases (tCoFix defs i) ->
  is_expanded (tCoFix defs i) ->
  cunfold_cofix (map (map_def dearg) defs) i = Some (narg, dearg fn).
Proof.
  intros cuf clos_fix valid_fix exp_fix.
  cbn in *.
  unfold cunfold_cofix in *.
  rewrite nth_error_map.
  destruct (nth_error _ _) eqn:nth; [|easy].
  cbn in *.
  noconf cuf.
  f_equal.
  f_equal.
  rewrite dearg_substl.
  - f_equal; apply cofix_subst_dearg.
  - apply Forall_closed_cofix_subst.
    setoid_rewrite Nat.add_0_r in clos_fix.
    now apply forallb_Forall.
  - apply Forall_valid_cases_cofix_subst.
    now apply forallb_Forall.
  - apply Forall_is_expanded_cofix_subst.
    now apply forallb_Forall.
  - eapply nth_error_forallb in valid_fix.
    now rewrite nth in valid_fix.
Qed.

Lemma isBox_mkApps hd args :
  isBox (mkApps hd args) = isBox hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, app_length.
    cbn.
    rewrite Nat.add_comm.
    cbn.
    now rewrite Bool.andb_false_r.
Qed.

Lemma isLambda_mkApps hd args :
  isLambda (mkApps hd args) = isLambda hd && (#|args| =? 0).
Proof.
  destruct args using List.rev_ind.
  - cbn.
    now rewrite Bool.andb_true_r.
  - rewrite mkApps_app, app_length.
    cbn.
    symmetry; propify.
    right; easy.
Qed.

Lemma eval_mkApps_tConstruct {wfl:WcbvFlags} Σ ind c args argsv
      (a : All2 (eval Σ) args argsv) :
  Σ e⊢ mkApps (tConstruct ind c) args ▷ mkApps (tConstruct ind c) argsv.
Proof.
  revert argsv a.
  induction args using MCList.rev_ind; intros argsv all.
  - depelim all.
    cbn.
    now constructor.
  - destruct argsv as [|? ? _] using MCList.rev_ind.
    { apply All2_length in all as len.
      rewrite app_length in len; cbn in *; lia. }
    destruct (All2_eval_snoc_elim all).
    rewrite !mkApps_app.
    cbn.
    eapply eval_app_cong.
    + easy.
    + now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps by easy.
    + assumption.
Qed.

Ltac facts :=
  (repeat
     match goal with
     | [H: ?Σ e⊢ ?t ▷ ?v |- _] =>
       match goal with
       | [H': is_true (closed v) |- _] =>
         fail 1
       | _ => idtac
       end;
       assert (closed v) by (apply (eval_closed _ _ _ H); trivial)
     end);
  (repeat
     match goal with
     | [H: ?Σ e⊢ ?t ▷ ?v |- _] =>
       match goal with
       | [H': is_true (valid_cases v) |- _] =>
         fail 1
       | _ => idtac
       end;
       assert (valid_cases v) by (apply (eval_valid_cases _ _ _ H); trivial)
     end);
  (repeat
     match goal with
     | [H: ?Σ e⊢ ?t ▷ ?v |- _] =>
       match goal with
       | [H': is_true (is_expanded v) |- _] =>
         fail 1
       | _ => idtac
       end;
       assert (is_expanded v) by (apply (eval_is_expanded_aux _ _ _ 0 H); trivial)
     end).

Section dearg.
  Context {wfl:WcbvFlags}.
  Context (n : nat).
  Context (Σ : global_declarations).
  Context (clos_Σ : env_closed Σ).
  Context (valid_Σ : valid_masks_env Σ).
  Context (exp_Σ : is_expanded_env Σ).
  Context (IH : forall t v : term,
        closed t ->
        valid_cases t ->
        is_expanded t ->
        forall ev : Σ e⊢ t ▷ v,
        deriv_length ev <= n ->
        dearg_env Σ e⊢ dearg t ▷ dearg v).

  Lemma eval_tApp_dearg {hd arg v} :
    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    closed arg ->
    valid_cases arg ->
    is_expanded arg ->
    forall (ev : Σ e⊢ tApp hd arg ▷ v),
      deriv_length ev <= S n ->
      dearg_env Σ e⊢ tApp (dearg hd) (dearg arg) ▷ dearg v.
  Proof with auto with dearg.
    intros clos_hd valid_hd exp_hd clos_arg valid_arg exp_arg ev ev_len.
    depind ev; cbn in *.
    - apply eval_box with (dearg t').
      + now unshelve eapply (IH _ _ _ _ _ ev1).
      + now unshelve eapply (IH _ _ _ _ _ ev2).
    - apply (eval_beta _ _ na (dearg b) _ (dearg a')).
      + now unshelve eapply (IH _ _ _ _ _ ev1).
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + facts.
        clear IHev1 IHev2 IHev3.
        revert ev3 ev_len.
        cbn in *.
        rewrite !closed_subst; [|now apply closedn_dearg_aux|easy].
        intros.
        rewrite <- (dearg_subst [a']) by easy.
        unshelve eapply (IH _ _ _ _ _ ev3)...
        * apply is_expanded_aux_subst...
        * lia.
    - facts.
      apply (eval_fix
                _ _
                (map (map_def dearg) mfix)
                idx
                (map dearg argsv)
                _
                (dearg av)
                (dearg fn)).
      + unshelve epose proof (IH _ _ _ _ _ ev1 _) as ev; trivial.
        1: lia.
        rewrite dearg_mkApps in ev.
        apply ev.
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + apply closed_mkApps_inv in H0 as (? & ?).
        apply valid_cases_mkApps_inv in H2 as (? & ?).
        apply is_expanded_aux_mkApps_inv in H4 as (? & ?).
        rewrite map_length.
        now apply dearg_cunfold_fix.
      + apply closed_mkApps_inv in H0 as (? & ?).
        apply valid_cases_mkApps_inv in H2 as (? & ?).
        apply is_expanded_aux_mkApps_inv in H4 as (? & ?).
        apply closed_cunfold_fix in e as ?; auto.
        apply valid_cases_cunfold_fix in e as ?; auto.
        apply forallb_Forall in H4.
        apply is_expanded_cunfold_fix in e as ?; auto.
        rewrite dearg_mkApps, dearg_expanded in IHev3 by easy.
        apply IHev3...
        * apply valid_cases_mkApps...
        * apply is_expanded_aux_mkApps...
          erewrite is_expanded_aux_upwards; [|eassumption|easy].
          cbn.
          easy.
        * lia.
    - facts.
      rewrite dearg_expanded by assumption.
      cbn.
      rewrite dearg_mkApps.
      cbn -[map_subterms].
      apply (eval_fix_value _ _ _ _ _ _ _ narg (dearg fn)).
      + unshelve epose proof (IH _ _ _ _ _ ev1 _) as ev; trivial.
        1: lia.
        rewrite dearg_mkApps in ev.
        apply ev.
      + now unshelve eapply (IH _ _ _ _ _ ev2).
      + apply closed_mkApps_inv in H0 as (? & ?).
        apply valid_cases_mkApps_inv in H2 as (? & ?).
        apply is_expanded_aux_mkApps_inv in H4 as (? & ?).
        now apply dearg_cunfold_fix.
      + rewrite map_length.
        lia.
    - facts.
      rewrite dearg_expanded by trivial.
      cbn.
      apply eval_app_cong.
      + now unshelve eapply (IH _ _ _ _ _ ev1 _).
      + destruct (dearg_elim f'); cbn.
        * apply is_expanded_aux_mkApps_inv in H4 as (? & ?).
          cbn in *; propify.
          rewrite dearg_single_masked by (now rewrite map_length).
          now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps.
        * apply is_expanded_aux_mkApps_inv in H4 as (? & ?).
          cbn in *; propify.
          rewrite dearg_single_masked by (now rewrite map_length).
          now rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps.
        * unfold dearg_case.
          now destruct (get_mib_masks _);
            rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps.
        * unfold dearg_proj.
          now destruct (get_mib_masks _);
            rewrite isLambda_mkApps, isFixApp_mkApps, isBox_mkApps.
        * rewrite !isLambda_mkApps, !isFixApp_mkApps, !isBox_mkApps in *
            by now destruct hd.
          rewrite map_length.
          now destruct hd.
      + now unshelve eapply (IH _ _ _ _ _ ev2 _).
    - easy.
  Qed.

  Lemma eval_mkApps_dearg hd args v :
    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    Forall (closedn 0) args ->
    Forall valid_cases args ->
    Forall is_expanded args ->
    forall (ev : Σ e⊢ mkApps hd args ▷ v),
      deriv_length ev <= n ->
      dearg_env Σ e⊢ mkApps (dearg hd) (map dearg args) ▷ dearg v.
  Proof.
    intros clos_hd valid_hd exp_hd clos_args valid_args exp_args ev ev_len.
    pose proof (eval_mkApps_deriv ev) as (hdv & ev_hd & argsv & ev_args & ev_args_len).
    induction ev_args using All2_rev_rect; cbn in *.
    - assert (hdv = v) as -> by (now eapply eval_deterministic).
      unshelve eapply (IH _ _ _ _ _ ev_hd _); auto.
      lia.
    - revert ev ev_len ev_args_len.
      rewrite map_app, !mkApps_app by easy.
      cbn.
      intros.
      rewrite <- dearg_expanded, <- dearg_mkApps by easy.
      unshelve eapply eval_tApp_dearg; auto.
      + apply closed_mkApps; auto.
        now apply Forall_snoc in clos_args.
      + apply valid_cases_mkApps; auto.
        now apply Forall_snoc in valid_args.
      + apply is_expanded_aux_mkApps; [now eapply is_expanded_aux_upwards|].
        now apply Forall_snoc in exp_args.
      + now apply Forall_snoc in clos_args.
      + now apply Forall_snoc in valid_args.
      + now apply Forall_snoc in exp_args.
  Qed.

  Lemma eval_mkApps_dearg_reduce {hd args v} :
    closed hd ->
    valid_cases hd ->
    is_expanded hd ->

    Forall (closedn 0) args ->
    Forall valid_cases args ->
    Forall is_expanded args ->
    (args = [] -> dearg_env Σ e⊢ dearg hd ▷ dearg v) ->
    forall (ev : Σ e⊢ mkApps hd args ▷ v),
      deriv_length ev <= S n ->
      dearg_env Σ e⊢ mkApps (dearg hd) (map dearg args) ▷ dearg v.
  Proof.
    intros clos_hd valid_hd exp_hd clos_args valid_args exp_args no_args ev ev_len.
    destruct args as [|? ? _] using MCList.rev_ind; cbn in *; [easy|].
    revert ev ev_len.
    rewrite map_app, !mkApps_app.
    cbn.
    intros.
    pose proof (eval_tApp_deriv ev) as (? & ? & ? & ? & ?).
    eapply eval_tApp_heads.
    2: { unshelve eapply eval_mkApps_dearg.
         2: eassumption.
         all: auto.
         - now apply Forall_snoc in clos_args.
         - now apply Forall_snoc in valid_args.
         - now apply Forall_snoc in exp_args.
         - lia. }
    1: { unshelve eapply IH.
         2: eassumption.
         - apply Forall_snoc in clos_args.
           now apply closed_mkApps.
         - apply Forall_snoc in valid_args.
           now apply valid_cases_mkApps.
         - apply is_expanded_aux_mkApps; [now eapply is_expanded_aux_upwards|].
           now apply Forall_snoc in exp_args.
         - lia. }
      unshelve eapply eval_tApp_dearg.
      all: auto.
    - apply Forall_snoc in clos_args.
      now apply closed_mkApps.
    - apply Forall_snoc in valid_args.
      now apply valid_cases_mkApps.
    - apply Forall_snoc in exp_args.
      apply is_expanded_aux_mkApps; [|easy].
      now eapply is_expanded_aux_upwards.
    - now apply Forall_snoc in clos_args.
    - now apply Forall_snoc in valid_args.
    - now apply Forall_snoc in exp_args.
  Qed.
End dearg.

Lemma env_closed_dearg Σ :
  env_closed Σ ->
  env_closed (dearg_env Σ).
Proof.
  intros clos.
  induction Σ as [|((kn & has_deps) & decl) Σ IH]; [easy|].
  cbn in *.
  destruct decl; [|easy].
  cbn in *.
  propify; split; [|easy].
  destruct (cst_body c); [|easy].
  cbn in *.
  eapply closedn_dearg_aux; [|easy].
  now eapply closedn_dearg_lambdas.
Qed.

Lemma valid_dearg_mask_dearg_aux mask t :
  valid_dearg_mask mask t ->
  valid_dearg_mask mask (dearg t).
Proof.
  intros valid.
  induction t in mask, t, valid |- *; auto; cbn in *;
    try (now destruct mask; [apply valid_dearg_mask_nil|]).
  destruct mask; [easy|].
  propify; split; [|easy].
  destruct b; [|easy].
  propify.
  now rewrite is_dead_dearg_aux.
Qed.

Lemma masked_length {X} m (xs : list X) :
  #|m| <= #|xs| ->
  #|masked m xs| = count_zeros m + #|xs| - #|m|.
Proof.
  intros len.
  induction m in xs, len |- *; cbn in *.
  - now destruct xs.
  - destruct xs; cbn in *; [easy|].
    destruct a; cbn in *.
    + rewrite IHm by easy.
      now unfold count_zeros.
    + rewrite IHm by easy.
      now unfold count_zeros.
Qed.

Lemma masked_app {X} m m' (xs : list X) :
  masked (m ++ m') xs = firstn (count_zeros m) (masked m xs) ++ masked m' (skipn #|m| xs).
Proof.
  induction m in m', xs |- *; cbn in *; [easy|].
  destruct xs.
  - destruct a; cbn.
    + now rewrite firstn_nil, skipn_nil, masked_nil.
    + now rewrite skipn_nil, masked_nil.
  - destruct a; cbn.
    + now rewrite IHm, skipn_S.
    + f_equal.
      apply IHm.
Qed.

Lemma masked_map {X Y} m (f : X -> Y) xs :
  masked m (map f xs) = map f (masked m xs).
Proof.
  induction m as [|[] m IH] in xs |- *; [easy| |]; cbn in *.
  - destruct xs; cbn in *; [easy|].
    apply IH.
  - destruct xs; cbn in *; [easy|].
    f_equal; apply IH.
Qed.

Lemma filter_length {X} (f : X -> bool) (xs : list X) :
  #|filter f xs| <= #|xs|.
Proof.
  induction xs; [easy|].
  cbn.
  destruct (f a); cbn; lia.
Qed.

Lemma map_repeat {X Y} (f : X -> Y) x n :
  map f (repeat x n) = repeat (f x) n.
Proof.
  induction n; [easy|].
  now cbn; rewrite IHn.
Qed.

Lemma nth_error_masked {X} m (xs : list X) n :
  nth n m false = false ->
  nth_error (masked m xs) (n - count_ones (firstn n m)) =
  nth_error xs n.
Proof.
  intros not_removed.
  induction n in m, xs, not_removed |- *; cbn in *.
  - destruct xs; [now rewrite masked_nil|].
    destruct m; [easy|].
    now destruct b.
  - destruct m; cbn in *; [easy|].
    destruct xs; cbn in *.
    + now rewrite nth_error_nil.
    + destruct b; cbn in *.
      * now apply IHn.
      * rewrite Nat.sub_succ_l; [now apply IHn|].
        transitivity #|firstn n m|; [|now rewrite firstn_length].
        apply filter_length.
Qed.

Lemma is_propositional_ind_dearg_env Σ ind :
  is_propositional_ind (dearg_env Σ) ind =
  is_propositional_ind Σ ind.
Proof.
  unfold is_propositional_ind.
  rewrite lookup_env_dearg_env.
  destruct lookup_env; cbn in *; [|reflexivity].
  destruct g; cbn in *; auto.
  unfold dearg_mib.
  destruct get_mib_masks; [|reflexivity].
  cbn.
  rewrite nth_error_mapi.
  now destruct nth_error.
Qed.

Lemma dearg_correct {wfl:WcbvFlags} Σ t v :
  env_closed Σ ->
  closed t ->

  valid_masks_env Σ ->
  valid_cases t ->

  is_expanded_env Σ ->
  is_expanded t ->

  Σ e⊢ t ▷ v ->
  dearg_env Σ e⊢ dearg t ▷ dearg v.
Proof.
  intros clos_env clos_t valid_env valid_t exp_env exp_t.
  enough (forall n (ev : Σ e⊢ t ▷ v),
             deriv_length ev <= n ->
             dearg_env Σ e⊢ dearg t ▷ dearg v).
  { intros ev.
    eapply (H _ ev).
    apply le_refl. }
  induction n as [|n IH] in t, v, clos_t, valid_t, exp_t |- *; intros ev deriv_len.
  { now pose proof (deriv_length_min ev). }
  destruct (dearg_elim t).
  - apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn in *; propify.
    rewrite dearg_single_masked by (now rewrite map_length).
    specialize (eval_mkApps_deriv ev) as (? & ev_const & argsv & ev_args & deriv).
    depelim ev_const; cbn in *; [|easy].
    eapply declared_constant_dearg in isdecl as isdecl_dearg.
    destruct isdecl_dearg as (cst_dearg & decl_dearg & body_dearg).
    rewrite e in body_dearg; cbn in *.

    enough (dearg_env Σ
            e⊢ mkApps (dearg (dearg_lambdas (get_const_mask kn) body))
                      (masked (get_const_mask kn) (map dearg args)) ▷ dearg v) as ev'.
    { eapply eval_mkApps_head in ev' as ev_hd.
      destruct ev_hd as (hdv & ev_hd).
      eapply eval_mkApps_heads.
      3: eassumption.
      1: eassumption.
      econstructor; eassumption. }

    rewrite dearg_dearg_lambdas by
        eauto using valid_dearg_mask_constant, valid_cases_constant.
    assert (∑ ev' : Σ e⊢ mkApps body args ▷ v,
               deriv_length ev' < deriv_length ev) as (ev_body & deriv_body).
    { unshelve epose proof (eval_mkApps_heads_deriv _ ev_const ev) as (ev' & ?).
      - now econstructor.
      - exists ev'.
        now cbn in *. }

    apply dearg_lambdas_correct.
    + now apply env_closed_dearg.
    + apply closedn_dearg_aux; [|easy].
      now eapply closed_constant.
    + apply Forall_map.
      apply closed_mkApps_inv in clos_t as (? & clos_args).
      eapply Forall_impl; [exact clos_args|].
      intros.
      now apply closedn_dearg_aux.
    + apply valid_dearg_mask_dearg_aux.
      now eapply valid_dearg_mask_constant.
    + now rewrite map_length.
    + unshelve eapply eval_mkApps_dearg.
      6: exact IH.
      all: auto.
      * now eapply closed_constant.
      * now eapply valid_cases_constant.
      * now eapply is_expanded_constant.
      * now apply closed_mkApps_inv in clos_t.
      * now apply valid_cases_mkApps_inv in valid_t.
      * lia.

  - specialize (eval_mkApps_deriv ev) as (? & ev_constr & argsv & ev_args & deriv).
    assert (v = mkApps (tConstruct ind c) argsv) as ->.
    { eapply eval_deterministic; try eassumption.
      now apply eval_mkApps_tConstruct. }
    rewrite dearg_mkApps.
    cbn.
    apply All2_length in ev_args as ?.
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn in *; propify.
    rewrite !dearg_single_masked by (now rewrite map_length).
    assert (ev_args_dearg: All2 (eval (dearg_env Σ)) (map dearg args) (map dearg argsv)).
    { assert (all_smaller: sum_deriv_lengths ev_args <= n).
      { pose proof (deriv_length_min ev_constr).
        lia. }
      apply closed_mkApps_inv in clos_t as (_ & clos_apps).
      apply valid_cases_mkApps_inv in valid_t as (_ & valid_apps).
      clear -clos_apps valid_apps exp_args IH ev_args all_smaller.
      induction ev_args; cbn in *.
      - now constructor.
      - unshelve epose proof (IHev_args _ _ _ _) as ev_suf; auto.
        + now depelim clos_apps.
        + now depelim valid_apps.
        + now depelim exp_args.
        + lia.
        + unshelve epose proof (IH _ _ _ _ _ r _) as ev_dearg; auto.
          * now depelim clos_apps.
          * now depelim valid_apps.
          * now depelim exp_args.
          * lia. }

    now apply eval_mkApps_tConstruct, All2_masked.
  - facts.
    apply closed_mkApps_inv in clos_t as (clos_t & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_t & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    intros ->.
    cbn in *; propify; refold'.
    destruct clos_t as (clos_discr & clos_brs).
    destruct valid_t as ((valid_discr & valid_brs) & valid_brs_masks).
    destruct exp_hd as (exp_discr & exp_brs).
    unfold dearg_case.
    (* We need induction as casing on a cofix involves casing on whatever it evaluates to *)
    depind ev; cbn in *.
    + (* Normal pattern match *)
      clear IHev1 IHev2.
      facts.
      clear clos_args valid_args exp_args.
      apply closed_mkApps_inv in H2 as (clos_hd & clos_args).
      apply valid_cases_mkApps_inv in H3 as (valid_hd & valid_args).
      apply is_expanded_aux_mkApps_inv in H4 as (exp_hd & exp_args).
      cbn in *; propify.
      apply (eval_iota _ _ _ _ c (masked (get_ctor_mask ind c) (map dearg args))).
      * unshelve epose proof (IH _ _ _ _ _ ev1 _); auto.
        1: lia.
        rewrite dearg_mkApps in *.
        cbn in *.
        now rewrite dearg_single_masked in * by (now rewrite map_length).
      * rewrite is_propositional_ind_dearg_env; eauto.
      * destruct (get_mib_masks _) eqn:mm; cycle 1.
        { cbn in *.
          unfold get_ctor_mask.
          rewrite mm.
          cbn.
          unfold iota_red in *.
          rewrite <- map_skipn, nth_map by easy.
          cbn.
          unshelve eapply eval_mkApps_dearg.
          6: exact IH.
          all: auto.
          1-3: rewrite nth_nth_error; destruct (nth_error _ _) eqn:nth; [|easy].
          - now eapply nth_error_forallb in clos_brs; rewrite nth in *.
          - now eapply nth_error_forallb in valid_brs; rewrite nth in *.
          - now eapply nth_error_forallb in exp_brs; rewrite nth in *.
          - now apply Forall_skipn.
          - now apply Forall_skipn.
          - now apply Forall_skipn.
          - lia. }

        cbn.
        unfold get_ctor_mask.
        rewrite mm.
        unfold iota_red in *.
        revert ev2 deriv_len.
        rewrite !nth_nth_error, nth_error_mapi, nth_error_map, option_map_two.
        intros.
        destruct (nth_error _ _) eqn:nth; cycle 1.
        { cbn in *.
          eapply eval_mkApps_head in ev2 as ev'.
          destruct ev' as (? & ev_contra).
          now depelim ev_contra. }
        cbn in *.
        replace
          (skipn (count_zeros (param_mask m))
                 (masked (param_mask m ++ get_branch_mask m ind c) (map dearg args)))
          with
            (masked (get_branch_mask m ind c)
                             (skipn #|param_mask m| (map dearg args))); cycle 1.
        { clear.
          generalize (get_branch_mask m ind c) as m2.
          generalize (map dearg args) as ts.
          generalize (param_mask m) as m1.
          intros m1 ts m2.
          induction m1 in ts, m2 |- *; intros.
          - cbn.
            now rewrite !skipn_0.
          - destruct a; cbn in *.
            + destruct ts; [now rewrite !skipn_nil, !masked_nil|].
              rewrite skipn_S.
              now apply IHm1.
            + destruct ts; [now rewrite !skipn_nil, !masked_nil|].
              rewrite !skipn_S.
              now apply IHm1. }

        unfold valid_case_masks in valid_brs_masks.
        rewrite mm in valid_brs_masks.
        propify.
        destruct valid_brs_masks as (<- & valid_brs_masks).

        apply dearg_lambdas_correct.
        -- now apply env_closed_dearg.
        -- eapply nth_error_forallb in clos_brs.
           rewrite nth in clos_brs.
           now apply closedn_dearg_aux.
        -- apply Forall_skipn.
           apply Forall_map.
           eapply Forall_impl; [exact clos_args|].
           intros; now apply closedn_dearg_aux.
        -- apply alli_Alli in valid_brs_masks.
           unshelve eapply Alli_nth_error in valid_brs_masks.
           4: eassumption.
           destruct p.
           cbn in *; propify.
           now apply valid_dearg_mask_dearg_aux.
        -- unfold get_ctor_mask in *.
           rewrite mm in *.
           rewrite app_length in *.
           rewrite <- map_skipn, map_length.
           rewrite skipn_length by lia.
           lia.
        -- rewrite <- map_skipn.
           unshelve eapply eval_mkApps_dearg.
           6: exact IH.
           all: eauto.
           ++ now eapply nth_error_forallb in clos_brs; rewrite nth in *.
           ++ now eapply nth_error_forallb in valid_brs; rewrite nth in *.
           ++ now eapply nth_error_forallb in exp_brs; rewrite nth in *.
           ++ now apply Forall_skipn.
           ++ now apply Forall_skipn.
           ++ now apply Forall_skipn.
           ++ lia.
    + clear IHev1 IHev2.
      (* Singleton pattern match *)
      subst brs; cbn in *; propify.
      set (branch_mask := match get_mib_masks (inductive_mind ind) with
                          | Some mm => get_branch_mask mm ind 0
                          | None => []
                          end).
      apply (eval_iota_sing _ _ _ _ _ (n - count_ones branch_mask)
                            (dearg_lambdas branch_mask (dearg f))).
      * eauto.
      * unshelve eapply (IH _ tBox); eauto.
        lia.
      * rewrite is_propositional_ind_dearg_env; eauto.
      * destruct (get_mib_masks _); cbn in *; [easy|].
        now rewrite dearg_lambdas_nil, Nat.sub_0_r.
      * replace (repeat tBox _) with (masked branch_mask (repeat tBox n)); cycle 1.
        { unfold valid_case_masks in valid_brs_masks.
          destruct (get_mib_masks _).
          - clear -valid_brs_masks.
            cbn in *; propify.
            destruct valid_brs_masks as (_ & (bound & _) & _).
            change (get_branch_mask m ind 0) with branch_mask in bound.
            induction branch_mask in n, bound |- *; cbn in *.
            + now rewrite Nat.sub_0_r.
            + destruct n; [easy|].
              cbn.
              destruct a; cbn.
              * now apply IHbranch_mask.
              * pose proof (filter_length id branch_mask).
                rewrite Nat.sub_succ_l by easy.
                cbn; f_equal.
                now apply IHbranch_mask.
          - cbn.
            now rewrite Nat.sub_0_r. }

        apply dearg_lambdas_correct.
        -- now apply env_closed_dearg.
        -- now apply closedn_dearg_aux.
        -- now apply Forall_repeat.
        -- apply valid_dearg_mask_dearg_aux.
           unfold valid_case_masks in valid_brs_masks.
           destruct (get_mib_masks _); cbn in *; propify; [easy|].
           apply valid_dearg_mask_nil.
        -- rewrite repeat_length.
           unfold valid_case_masks in valid_brs_masks.
           destruct (get_mib_masks _); cbn in *; [|easy].
           now propify.
        -- change tBox with (dearg tBox).
           rewrite <- map_repeat.
           unshelve eapply eval_mkApps_dearg.
           6: exact IH.
           all: auto.
           ++ easy.
           ++ easy.
           ++ easy.
           ++ now apply Forall_repeat.
           ++ now apply Forall_repeat.
           ++ now apply Forall_repeat.
           ++ lia.

    + (* Unfold cofix *)
      clear clos_args valid_args exp_args.
      apply closed_mkApps_inv in clos_discr as (clos_hd & clos_args).
      apply valid_cases_mkApps_inv in valid_discr as (valid_hd & valid_args).
      apply is_expanded_aux_mkApps_inv in exp_discr as (exp_hd & exp_args).
      cbn in *; propify.
      rewrite dearg_mkApps.
      cbn.
      apply (red_cofix_case _ _ _ _ _ narg (dearg fn)); [now eapply dearg_cunfold_cofix|].
      assert (closed fn) by now eapply closed_cunfold_cofix.
      assert (valid_cases fn) by now eapply valid_cases_cunfold_cofix.
      assert (is_expanded fn).
      { eapply is_expanded_cunfold_cofix; [eassumption|].
        now apply forallb_Forall. }
      rewrite <- dearg_expanded, <- dearg_mkApps by easy.
      unshelve eapply (IHev _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n IH ev).
      all: auto.
      * now apply closed_mkApps.
      * now apply valid_cases_mkApps.
      * apply is_expanded_aux_mkApps; [|easy].
        now eapply is_expanded_aux_upwards.
      * lia.
    + congruence.

  - facts.
    apply closed_mkApps_inv in clos_t as (clos_hd & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_hd & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_hd & exp_args).
    cbn in * |-.
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    intros ->.
    cbn in *; refold'.
    clear clos_args valid_args exp_args.
    depind ev; cbn in *.
    + (* Cofix projection *)
      propify.
      destruct valid_hd as (valid_hd & valid_proj).
      apply closed_mkApps_inv in clos_hd as (clos_hd & clos_args).
      apply valid_cases_mkApps_inv in valid_hd as (valid_hd & valid_args).
      apply is_expanded_aux_mkApps_inv in exp_hd as (exp_hd & exp_args).
      cbn in *; propify.
      rewrite dearg_mkApps.
      unfold dearg_proj.
      cbn.
      apply (red_cofix_proj _ _ _ _ _ narg (dearg fn)); [now eapply dearg_cunfold_cofix|].
      assert (closed fn) by now eapply closed_cunfold_cofix.
      assert (valid_cases fn) by now eapply valid_cases_cunfold_cofix.
      assert (is_expanded fn).
      { eapply is_expanded_cunfold_cofix; [eassumption|].
        now apply forallb_Forall. }
      rewrite <- dearg_expanded, <- dearg_mkApps by easy.
      unshelve eapply IHev.
      8: exact IH.
      all: auto.
      * now apply closed_mkApps.
      * propify; split; [|easy].
        now apply valid_cases_mkApps.
      * apply is_expanded_aux_mkApps; [|easy].
        now eapply is_expanded_aux_upwards.
      * lia.
    + (* Regular projection *)
      clear IHev1 IHev2.
      propify.
      destruct valid_hd as (valid_hd & valid_p).
      facts.
      apply closed_mkApps_inv in H2 as (clos_constr & clos_args).
      apply valid_cases_mkApps_inv in H3 as (valid_constr & valid_args).
      apply is_expanded_aux_mkApps_inv in H4 as (exp_constr & exp_args).
      cbn in *; propify.
      unfold dearg_proj.
      apply (eval_proj _ _ _ _ _ (masked (get_ctor_mask i 0) (map dearg args))).
      * unshelve epose proof (IH _ _ _ _ _ ev1 _); auto.
        1: lia.
        rewrite dearg_mkApps in *.
        cbn in *.
        now rewrite dearg_single_masked in * by (now rewrite map_length).
      * rewrite is_propositional_ind_dearg_env; eauto.
      * clear clos_constr valid_constr.
        unfold get_ctor_mask in *.
        revert ev2 deriv_len.
        rewrite !nth_nth_error.
        intros.

        destruct (get_mib_masks _) eqn:mm; cbn in *; cycle 1.
        { rewrite nth_error_map.
          destruct (nth_error _ _) eqn:nth; cbn in *; [|now depelim ev2].
          unshelve eapply (IH _ _ _ _ _ ev2).
          - now eapply nth_error_forall in clos_args; [|eassumption].
          - now eapply nth_error_forall in valid_args; [|eassumption].
          - now eapply nth_error_forall in exp_args; [|eassumption].
          - lia. }
        destruct (nth_error args _) eqn:nth; [|now depelim ev2].
        rewrite app_length in *.
        unfold valid_proj in valid_p; rewrite mm in valid_p; propify.
        destruct valid_p as (<- & arg_unused).
        rewrite masked_map, nth_error_map, masked_app.
        rewrite nth_error_app2; cycle 1.
        { rewrite firstn_length.
          lia. }
        rewrite firstn_length.
        rewrite Nat.min_l; cycle 1.
        { rewrite masked_length by easy.
          lia. }
        replace (count_zeros (param_mask m) + (arg - count_ones (firstn arg (get_branch_mask m i 0))) -
            count_zeros (param_mask m)) with (arg - count_ones (firstn arg (get_branch_mask m i 0)))
          by lia.
        rewrite nth_error_masked by easy.
        rewrite nth_error_skipn, nth.
        cbn.
        unshelve eapply (IH _ _ _ _ _ ev2 _).
        -- now eapply nth_error_forall in clos_args; [|eassumption].
        -- now eapply nth_error_forall in valid_args; [|eassumption].
        -- now eapply nth_error_forall in exp_args; [|eassumption].
        -- lia.
    + (* Project out of box *)
      clear IHev.
      propify.
      destruct valid_hd as (valid_hd & valid_p).
      unfold dearg_proj.
      apply eval_proj_prop.
      * eauto.
      * unshelve eapply (IH _ _ _ _ _ ev _); auto.
        lia.
      * rewrite is_propositional_ind_dearg_env; eauto.
    + congruence.

  - facts.
    apply closed_mkApps_inv in clos_t as (clos_t & clos_args).
    apply valid_cases_mkApps_inv in valid_t as (valid_t & valid_args).
    apply is_expanded_aux_mkApps_inv in exp_t as (exp_t & exp_args).
    unshelve eapply eval_mkApps_dearg_reduce.
    6: exact IH.
    all: auto.
    1: now destruct hd.
    intros ->.
    cbn in *.
    depelim ev; cbn in *; propify; try destruct y; refold'.
    + intuition auto.
      facts.
      econstructor.
      * now unshelve eapply (IH _ _ _ _ _ ev1 _).
      * revert ev2 deriv_len.
        rewrite !closed_subst by (auto; now apply closedn_dearg_aux).
        intros.
        change (subst0 ?a ?t) with (subst0 (map dearg [b0']) t).
        rewrite <- dearg_subst by auto.
        unshelve eapply (IH _ _ _ _ _ ev2 _).
        -- now apply closedn_subst0.
        -- now apply valid_cases_subst.
        -- now apply is_expanded_aux_subst.
        -- lia.
    + destruct t; cbn in *; try destruct y; try congruence; now constructor.
Qed.
End dearg_correct.
