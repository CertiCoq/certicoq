Require Import String List BinPos Relation_Operators.
Import ListNotations.

Definition var := positive.
Inductive exp :=
| LetIn (x : var) (b : bool) (e : exp)
| IfThenElse (x : var) (e1 : exp) (e2 : exp).

Require MetaCoq.Template.All.
Import MetaCoq.Template.BasicAst.
Require Import Prototype PrototypeGenFrame Rewriting.

MetaCoq Run
  (mk_Frame_ops
    (MPfile ["Example"; "L6"; "CertiCoq"])              
    (MPfile ["Example"; "L6"; "CertiCoq"], "exp") exp
    [var; bool]).
Instance Frame_exp : Frame exp_univ := exp_Frame_ops.
Instance AuxData_exp : AuxData exp_univ := exp_aux_data.

Notation ctx :=
  (@frames_t exp_univ Frame_exp exp_univ_exp exp_univ_exp).

(* (x ↦ b) ∈ C *)
Definition known_bool {A}
           (x : var) (b : bool)
           (C : frames_t A exp_univ_exp) :=
  exists D E, C = D >:: LetIn2 x b >++ E.

Fixpoint occurs_free (x : var) (e : exp) :=
  match e with
  | LetIn y b e =>
    x <> y /\ occurs_free x e
  | IfThenElse y e1 e2 =>
    x = y \/ occurs_free x e1 \/
    occurs_free x e2
  end.

Reserved Infix "-->" (at level 70).
Inductive rewrite_step : exp -> exp -> Prop :=
(** Case folding *)
| case_fold : forall (C : ctx) x b e1 e2 e_taken,
  known_bool x b C /\
  (if b then e1 else e2) = e_taken ->
  C ⟦ IfThenElse x e1 e2 ⟧ --> C ⟦ Rec e_taken ⟧
(** Dead variable elimination *)
| dead_var_elim : forall (C : ctx) x b e,
  ~ occurs_free x e ->
  BottomUp (C ⟦ LetIn x b e ⟧ --> C ⟦ e ⟧)
where "e1 --> e2" := (rewrite_step e1 e2).
Infix "-->*" :=
  (clos_refl_trans (univD exp_univ_exp) rewrite_step)
  (at level 70).

(** Known constructors *)

Module M := Maps.PTree.

Definition env_map := M.tree bool.

Definition env_map_invariant
  {A} (C : frames_t A exp_univ_exp) (env : env_map) :=
  forall x b, M.get x env = Some b -> known_bool x b C.

(** Use counts *)

Definition count_var (x y : var) : nat :=
  if (x =? y)%positive then 1 else 0.

Fixpoint use_count x e {struct e} : nat :=
  match e with
  | LetIn y b e => use_count x e
  | IfThenElse y e1 e2 =>
    count_var x y + use_count x e1 + use_count x e2
  end.

Definition uses_map := M.tree nat.

Definition nat_of_option_nat o :=
  match o with Some n => n | None => 0 end.
Definition get_count x uses :=
  nat_of_option_nat (M.get x uses).

Definition uses_map_invariant
           {A} (C : frames_t A exp_univ_exp) (e : univD A)
           (uses : uses_map) :=
  forall x, get_count x uses = use_count x (C ⟦ e ⟧).

Require Import Lia.
Lemma use_count_zero_implies_dead x e : use_count x e = 0 -> ~ occurs_free x e.
Proof.
  induction e; cbn; [tauto|intros H].
  assert (count_var x x0 = 0 /\ use_count x e1 = 0 /\ use_count x e2 = 0) by lia.
  unfold count_var in *; destruct (Pos.eqb_spec x x0); intuition lia.
Qed.

Definition upd_count f x (uses : uses_map) :=
  match f (M.get x uses) with
  | Some n => M.set x n uses
  | None => M.remove x uses
  end.

Fixpoint upd_uses f e uses :=
  match e with
  | LetIn y b e => upd_uses f e uses
  | IfThenElse y e1 e2 => upd_count f y (upd_uses f e1 (upd_uses f e2 uses))
  end.

Definition incr x := match x with Some n => Some (S n) | None => Some 1 end.
Definition decr x := match x with Some (S n) => Some n | _ => None end.

Definition init_use_counts e := upd_uses incr e (M.empty _).
Definition decr_use_counts e uses := upd_uses decr e uses.

Lemma iter_fuse {A} n m (f : A -> A) x : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof.
  revert m; induction n as [|n IHn]; [reflexivity|intros; cbn].
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x); now rewrite IHn.
Qed.

Lemma upd_count_correct f y x uses :
  M.get y (upd_count f x uses) = Nat.iter (count_var y x) f (M.get y uses).
Proof.
  unfold upd_count, count_var in *; cbn in *.
  destruct (Pos.eqb_spec y x); cbn in *.
  - subst; destruct (f (M.get x uses)) as [n|] eqn:Hn; now rewrite ?M.gss, ?M.grs.
  - destruct (f (M.get x uses)) as [n'|] eqn:Hn; now rewrite ?M.gso, ?M.gro by auto.
Qed.

Lemma decr_count_correct y x uses :
  get_count y (upd_count decr x uses) = get_count y uses - count_var y x.
Proof.
  unfold get_count. rewrite upd_count_correct.
  unfold count_var; destruct (M.get y uses) as [[|n]|] eqn:Hget;
    destruct (Pos.eqb_spec y x); cbn; try lia.
Qed.

Lemma upd_uses_correct f x e : forall uses,
  M.get x (upd_uses f e uses) = Nat.iter (use_count x e) f (M.get x uses).
Proof. induction e; simpl; intros; now rewrite <- ?iter_fuse, ?upd_count_correct. Qed.

Lemma nat_of_option_nat_incr n : nat_of_option_nat (incr n) = S (nat_of_option_nat n).
Proof. destruct n as [n|]; now cbn. Qed.

Lemma nat_of_option_nat_iter_incr n c : nat_of_option_nat (Nat.iter n incr c) = n + nat_of_option_nat c.
Proof.
  induction n as [|n IHn]; [reflexivity|unfold Nat.iter in *; cbn].
  now rewrite nat_of_option_nat_incr, IHn.
Qed.

Lemma nat_of_option_nat_decr n : nat_of_option_nat (decr n) = nat_of_option_nat n - 1.
Proof. destruct n as [n|]; cbn; [|auto]; destruct n; cbn; lia. Qed.

Lemma nat_of_option_nat_iter_decr n c : nat_of_option_nat (Nat.iter n decr c) = nat_of_option_nat c - n.
Proof.
  induction n as [|n IHn]; [cbn; lia|unfold Nat.iter in *; cbn].
  now rewrite nat_of_option_nat_decr, IHn.
Qed.

Lemma init_use_counts_correct x e : get_count x (init_use_counts e) = use_count x e.
Proof.
  unfold get_count, init_use_counts.
  now rewrite upd_uses_correct, nat_of_option_nat_iter_incr, M.gempty.
Qed.

Lemma decr_use_counts_correct x e uses :
  get_count x (decr_use_counts e uses) = get_count x uses - use_count x e.
Proof.
  unfold get_count, decr_use_counts.
  now rewrite upd_uses_correct, nat_of_option_nat_iter_decr.
Qed.

Definition use_count_frame {A B} (x : var) (C : exp_frame_t A B) :=
  match C with
  | LetIn0 _ e => use_count x e
  | LetIn1 _ e => use_count x e
  | LetIn2 _ _ => 0
  | IfThenElse0 e1 e2 => use_count x e1 + use_count x e2
  | IfThenElse1 y e2 => count_var x y + use_count x e2
  | IfThenElse2 y e1 => count_var x y + use_count x e1
  end.
           
Fixpoint use_count_ctx {A B} x (C : frames_t A B) :=
  match C with
  | <[]> => 0
  | C >:: f => use_count_frame x f + use_count_ctx x C
  end.

Definition use_count_tm {A : exp_univ} (x : var) (e : univD A) :=
  match A return univD A -> nat with
  | exp_univ_bool => fun _ => 0
  | exp_univ_var => count_var x
  | exp_univ_exp => use_count x
  end e.

Lemma use_count_frame_app' {A B} (x : var) (f : exp_frame_t A B) (e : univD A) :
  match A with
  | exp_univ_exp => use_count_tm x (frameD f e) = use_count_frame x f + use_count_tm x e
  | _ => True
  end.
Proof. destruct f; cbn; lia. Qed.

Corollary use_count_frame_app x (f : exp_frame_t exp_univ_exp exp_univ_exp) e :
  use_count x (frameD f e) = use_count_frame x f + use_count x e.
Proof. apply (use_count_frame_app' x f). Qed.

Lemma use_count_ctx_app' {A B} (x : var) (C : frames_t A B) (e : univD A) :
  match A with
  | exp_univ_exp => use_count_tm x (C ⟦ e ⟧) = use_count_ctx x C + use_count_tm x e
  | _ => True
  end.
Proof.
  induction C; cbn; [now destruct A|]; destruct A; [cbn|easy..].
  inversion f; subst; rewrite IHC, use_count_frame_app; lia.
Qed.

Corollary use_count_ctx_app x (C : ctx) e :
  use_count x (C ⟦ e ⟧) = use_count_ctx x C + use_count x e.
Proof. apply (use_count_ctx_app' x C). Qed.

(** Termination measure *)

Fixpoint exp_size e :=
  match e with
  | LetIn x b e => 1 + 2 + exp_size e
  | IfThenElse x e1 e2 => 1 + 1 + exp_size e1 + exp_size e2
  end.

Definition measure A : forall (C : frames_t A exp_univ_exp) (e : univD A), nat :=
  match A with
  | exp_univ_var => fun _ _ => 1
  | exp_univ_bool => fun _ _ => 1
  | exp_univ_exp => fun _ e => exp_size e
  end.

(** Obligations re: preserving invariants across recursive calls *)

Instance Preserves_env: Preserves_R (@env_map_invariant).
Proof.
  intros A B fs fs_ok f [env Henv]; destruct f;
  lazymatch goal with
  | |- Param (@env_map_invariant)
        (e_map (fun fs => fs >:: LetIn2 ?x' ?b') fs) =>
    rename x' into x, b' into b
  | _ =>
    exists env; unerase; intros x' b' Hget';
    specialize (Henv x' b' Hget');
    destruct Henv as [D [E Hctx]];
    match goal with
    | |- known_bool _ _ (_ >:: ?f) =>
      exists D, (E >:: f); now subst fs
    end
  end.
  exists (M.set x b env); unerase; intros x' b' Hget'; cbn in *.
  destruct (Pos.eq_dec x' x);
  [subst; rewrite M.gss in Hget'; inversion Hget'; now exists fs, <[]>|].
  rewrite M.gso in Hget' by auto.
  destruct (Henv x' b' Hget') as [D [E Hctx]].
  exists D, (E >:: LetIn2 x b); now subst fs.
Defined.
Extraction Inline Preserves_env.

Instance Preserves_uses_up: Preserves_S_up (@uses_map_invariant).
Proof.
  intros A B fs fs_ok f x [uses Huses];
    exists uses; unerase; apply Huses.
Defined.
Extraction Inline Preserves_uses_up.

Instance Preserves_uses_dn: Preserves_S_dn (@uses_map_invariant).
Proof.
  intros A B fs fs_ok f x [uses Huses];
    exists uses; unerase; apply Huses.
Defined.
Extraction Inline Preserves_uses_dn.

Inductive MARK := MKMARK.

Unset Strict Unquote Universe Mode.
Definition optimize :
  rewriter exp_univ_exp false (fun A C e => @measure A C e)
           rewrite_step _ (I_D_plain (D:=unit))
           _ (@env_map_invariant)
           _ (@uses_map_invariant).
Proof.
  (** Derive partial program + partial proof *)
  mk_rw.
  all: mk_easy_delay.
  (** Solve obligations related to termination *)
  all: try lazymatch goal with |- MetricDecreasing -> _ =>
    try (simpl; unfold delayD; lia);
    clear - H H1; cbn in *; subst e_taken0;
    intros _; destruct H as [_ H], b;
    apply f_equal with (f := exp_size) in H; lia end.
  - (** Using env, check whether x is in scope.
        If so, perform case folding accordingly *)
    intros _ R C C_ok x e1 e2 d r s success failure.
    destruct r as [env Henv] eqn:Hr.
    destruct (M.get x env) as [b|] eqn:Hbool; [|cond_failure].
    pose (d' := d : Delay (I_D_plain (D := unit))
                          (A:=exp_univ_exp)
                          (if b then e1 else e2)).
    cond_success success.
    specialize (success _ d' x e1 e2 b (if b then e1 else e2)).
    unshelve eapply success; unerase; auto.
    (** Decrement use counts of scrutinee + deleted branch *)
    destruct s as [uses Huses]; destruct b;
      [exists (upd_count decr x (decr_use_counts e2 uses))
      |exists (upd_count decr x (decr_use_counts e1 uses))].
    all: unerase; intros y; clear - Huses;
      specialize (Huses y); cbn in *;
      unfold Rec; rewrite use_count_ctx_app in *; cbn in *;
      rewrite decr_count_correct, decr_use_counts_correct; lia.
  - (** Using uses, check whether x is dead.
        If so, perform dead variable elimination. *)
    clear; intros _ R C C_ok x b e r [uses Huses] success failure.
    destruct (M.get x uses) as [n|] eqn:Hbool; [cond_failure|].
    cond_success success.
    assert (Hget : get_count x uses = 0)
      by (unfold get_count; now rewrite Hbool).
    apply success; auto.
    + unerase. specialize (Huses x). cbn in *.
      apply use_count_zero_implies_dead.
      rewrite Huses, use_count_ctx_app in Hget.
      cbn in Hget; lia.
    + exists uses; unerase; intros y.
      specialize (Huses y); cbn in *.
      rewrite Huses, ?use_count_ctx_app in *; now cbn.
Defined.

Set Extraction Flag 2031. (* linear let + linear beta *)
Extraction optimize.

Definition optimize_top (e : exp) : {e' : exp | e -->* e'} :=
  let res :=
    optimize I exp_univ_exp
      (erase <[]>) (erase_ok <[]>)
      e
      (exist (fun _ => True) tt I)
      (erase (exp_size e)) (erase_ok (exp_size e))
      (exist (env_map_invariant <[]>) (M.empty _)
        ltac:(abstract (intros x b; now rewrite M.gempty)))
      (exist (uses_map_invariant <[]> e) (init_use_counts e)
        (fun x => init_use_counts_correct x e))
      eq_refl
  in exist _ res.(resTree) res.(resProof).
