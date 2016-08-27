Require Import BinNat.
Require Import BinPos.
Require Import Omega.
Require Import Psatz.
Require Import Arith.
Require Import PArith.
Require Import NArith.
  SearchAbout N.lt not iff.
SearchAbout N.lt N.add ex.

Require Import L4.expression.
Require Import Basics.


Fixpoint fn {A:Type} (f: A->A) (n:nat) : A -> A :=
match n with
| O => id
| S n' => compose (fn f n') f
end.

Lemma fn_shift {A:Type} (f: A->A) : forall x start,
fn f x (f start) = f (fn f x start).
Proof using.
  induction x; auto.
  simpl. unfold compose. auto.
Qed.


Require Import L4.L4a_to_L5.
Require Import L4.L4_to_L4a.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.list.

Require Import SquiggleEq.tactics.
Print my_exp_wf_ind.
Require Import Coq.Unicode.Utf8.
Require Import List.
Require Import SquiggleEq.list.

Open Scope program_scope.

Lemma seq_spec {A:Type} (f: A->A)  :
  forall (len:nat) (start:A), 
    (L4_to_L4a.seq f start len) = map (fun n => (fn f n) start) (seq 0 len).
Proof using Type.
  induction len; intros ?; auto.
  simpl. f_equal. rewrite <- seq_shift.
  rewrite map_map. unfold compose. simpl.
  eauto.
Qed.

Lemma seq_shift {A:Type} (f: A->A)  :
  forall (len:nat) (start:A), 
    (L4_to_L4a.seq f (f start) len) = map f (L4_to_L4a.seq f start len).
Proof using Type.
  intros.
  do 2 rewrite seq_spec.
  rewrite map_map. unfold compose.
  apply eq_maps.
  intros ? _.
  apply fn_shift.
Qed.

Lemma fn_plusN : forall (n:nat) (m:N), (fn N.succ n) m = ((N.of_nat n) + m)%N.
Proof using Type.
  induction n; auto.
  intros. rewrite Nat2N.inj_succ. simpl.
  unfold compose. simpl.
  rewrite IHn.
  lia.
Qed.

Open Scope N_scope.

Lemma in_seq_Nplus :   ∀ len (start n : N),
   LIn n (L4_to_L4a.seq N.succ start len) ↔ (start <= n ∧ n < start + N.of_nat len)%N.
Proof using.
  intros.
  rewrite seq_spec.
  rewrite in_map_iff.
  setoid_rewrite fn_plusN.
  setoid_rewrite in_seq.
  split; intro H.
- exrepnd. lia.
- repnd. exists (N.to_nat (n-start)).
  lia.
Qed.


(* circularity watch: this correctness property cannot go to L4.instances. Should we have
L4.correctnessInstances for such instances? *)
Require Import L4.instances.
Require Import Common.certiClasses.



(*
Lemma mkVarPreservesLt (a b : N) : (a < b)%N -> (mkVar a < mkVar b)%positive.
Proof.
  intro H.
  unfold mkVar.
  unfold Pos.lt.
  rewrite Pos.compare_xO_xO.
  fold (Pos.lt (N.succ_pos a) (N.succ_pos b)).
  (* Obvious! Perhaps we should use MathClasses to 
        avoid hunting aroung Coq's standard library*)
Admitted.
*)



Lemma mkVarDiv : forall i, 
  N.pos (Pos.div2 (mkVar i)) = N.succ i.
Proof using Type.
  intros. simpl.
  rewrite N.succ_pos_spec. refl.
Qed.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.

Lemma in_seq_mkvar_map : forall v l,
varClass v = true
->
(In v (map mkVar l)
<-> In (N.pos (Pos.div2 v)) (map N.succ l)).
Proof using.
  intros ? ? Hvc. do 2 rewrite in_map_iff.
  split; intro H; exrepnd; subst.
- rewrite mkVarDiv. eexists; eauto.
- exists a. split; auto.
  unfold mkVar.
  clear H1. destruct v; inverts H0; inverts Hvc.
  f_equal. rewrite <- N.succ_pos_spec in H1.
  inverts H1. refl.
Qed.



Lemma L4_to_L4a_fvars: 
  (forall n (s : exp),
    L4.expression.exp_wf n s 
    -> forall v, List.In v (free_vars (L4_to_L4a n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
 ∧
  (forall n (s : exps),
    L4.expression.exps_wf n s 
    -> forall v, List.In v (flat_map free_vars (translatel mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
 ∧
  (forall n (s : efnlst),
    L4.expression.efnlst_wf n s 
    -> forall v, List.In v 
                 (flat_map free_vars (translatef mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
 ∧
  (forall n (s : branches_e),
    L4.expression.branches_wf n s 
    -> forall v, List.In v (flat_map (free_vars_bterm ∘ snd)  (translateb mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
.
Proof using.
  apply my_exp_wf_ind; try (simpl; tauto);
  intros ? ?.
(* Var_e *)
- intros Hwf ? Hin. simpl in Hin. rewrite or_false_r in Hin.
  subst. split; [ | refl].
  rewrite mkVarDiv.
  rewrite N.sub_1_r.
  rewrite N.lt_succ_pred with (z:=0%N); lia.

(* Lam_e *)
- intros Hwf Hind ? Hin.
  simpl in Hin. fold (L4_to_L4a.translate mkVar (N.succ i)) in Hin.
  rewrite list.in_app_iff in Hin.
  rewrite or_false_r in Hin.
  apply list.in_remove in Hin.
  repnd. rewrite  N.add_1_l in Hind.
  apply Hind in Hin.
  clear Hind. rename Hin into Hind.
  repnd.
  split; [ | assumption].
  apply N.lt_succ_r in Hind0.
  apply N.lt_eq_cases in Hind0.
  dorn Hind0; [assumption | subst; provefalse ].
  apply Hin0.
  clear Hin0.
  destruct v; inversion Hind. clear Hind.
  simpl in Hind0.
  unfold mkVar. 
  f_equal.
  rewrite <- N.succ_pos_spec in Hind0.
  injection Hind0. trivial.

(* App_e *)
- intros ? ? H1ind H1wf H2ind ? Hin. simpl in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  repeat (rewrite list.in_app_iff in Hin).
  rewrite or_false_r in Hin.
  dorn Hin; eauto.

(* Con_e *)
- intros ? Hwf Hind ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translatel mkVar i) in Hin.
  rewrite flat_map_bterm_nil in Hin.
  eauto.

(* Match_e *)
- intros ? ? Hwf Hind ? Hindb ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translateb mkVar i) in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  apply list.in_app_iff in Hin.
  rewrite list.flat_map_map in Hin.
  dorn Hin; eauto.
  (* the crux of this proof comes later, in the translateb case *)

(* Let_e *)
- intros ? Hwf Hind H2wf H2ind ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translate mkVar (N.succ i)) in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  repeat rewrite list.in_app_iff in Hin.
  simpl in Hin.
  rewrite or_false_r in Hin.
  dorn Hin;[eauto; fail | ].
  clear Hind Hwf. rename H2ind into Hind.
  apply list.in_remove in Hin.
  repnd. rewrite  N.add_1_l in Hind.
  apply Hind in Hin.
  clear Hind. rename Hin into Hind.
  repnd.

  (* the part below is a suffix of the lambda case *)
  split; [ | assumption].
  apply N.lt_succ_r in Hind0.
  apply N.lt_eq_cases in Hind0.
  dorn Hind0; [assumption | subst; provefalse ].
  apply Hin0.
  clear Hin0.
  destruct v; inversion Hind. clear Hind.
  simpl in Hind0.
  unfold mkVar.
  f_equal.
  rewrite <- N.succ_pos_spec in Hind0.
  injection Hind0. trivial.

- intros ? Hwf Hind ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translatef mkVar (i + (efnlst_length es))%N) in Hin.
  rewrite N.add_comm in Hin.
  rewrite flat_map_map in Hin.
  unfold compose in Hin.
  simpl in Hin.
  apply in_flat_map in Hin. exrepnd.
  apply in_remove_nvars in Hin0. repnd.
  specialize (Hind v).
  rewrite in_flat_map in Hind.
  destruct Hind as [Hyy Hvc]; [eexists; dands; eauto | ].
  clear Hin1 Hin2.
  split; [ | assumption ].
  rewrite in_seq_mkvar_map in Hin0 by assumption.
  rewrite <- seq_shift in Hin0.
  setoid_rewrite in_seq_Nplus in Hin0.
  clear Hvc. lia.

- intros ? Hwf Hind H2wf H2ind ? Hin. simpl in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  fold (L4_to_L4a.translatel mkVar i) in Hin.
  apply in_app_iff in Hin.
  dorn Hin; eauto.
- intros ? Hwf Hind H2wf H2ind ? Hin. simpl in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  fold (L4_to_L4a.translatef mkVar i) in Hin.
  apply in_app_iff in Hin.
  dorn Hin; eauto.
- intros ? ? ? Hwf Hind  H2wf H2ind ? Hin. simpl in Hin.
  fold (L4_to_L4a.translate mkVar (i+n)) in Hin.
  fold (L4_to_L4a.translateb mkVar i) in Hin.
  apply in_app_iff in Hin. 
  dorn Hin; [ clear H2ind | ]; eauto. unfold compose in Hin.
  simpl in Hin.
  rewrite N.add_comm in Hin.
  apply in_remove_nvars in Hin. repnd.
  specialize (Hind v).
  apply Hind in Hin0. clear Hind. rename Hin0 into Hind. repnd.
  split;[ | assumption].
  rewrite in_seq_mkvar_map in Hin by assumption.
  rewrite <- seq_shift in Hin.
  setoid_rewrite in_seq_Nplus in Hin. lia.
Qed.


Lemma L4_to_L4a_preserves_wf : 
  certiClasses.wfPreserving (cTerm certiL4) (cTerm certiL4a).
Proof.
  intros ? ?. simpl. unfold wf. unfold WellFormed_instance_1.
  compute in s.
  compute in H.
Abort.

Print Nat.even.
Fixpoint isEven (n:nat) : bool := 
match n with
| 0 => true
| S n' => isOdd n' (* && isEven n' *)
end
with isOdd (n:nat) : bool :=
match n with
| 0 => false
| S n' => isEven n' (* && isOdd n' *)
end.

Quote Recursively Definition isEven3 := (isEven 3).
Require Import Arith.
Quote Recursively Definition even3 := (Nat.even 3).

(* Move to an earlier file because it is more generally useful *)
Ltac cexact x := let t := eval compute in x in exact t.
Require Import L2.instances.

Definition isEven3L4 := ltac:(cexact (translateTo (cTerm certiL4) isEven3)).

Open Scope string_scope.
Print isEven3.

Local Opaque Match_e.
Local Opaque Fix_e.
Local Opaque Con_e.
Local Opaque Lam_e.
Local Opaque Let_e.
Local Opaque App_e.

Local Transparent ssubst_aux.
Local Transparent ssubst_bterm_aux.
Definition isEven3L4a := ltac:(cexact (translateTo (cTerm certiL4a) isEven3)).
Definition even3L4a := ltac:(cexact (translateTo (cTerm certiL4a) even3)).

Print isEven3L4.
Print isEven3L4a.

Eval vm_compute in isEven3L4a.
Eval vm_compute in even3L4a.

Eval compute in (DecidableClass.decide (2=3))%positive.



Require Import L4.expression.
Require Import Common.Common.

Hint Constructors expression.eval.
Hint Constructors expression.evals.
Lemma isEven3Eval : exists v, isEven3L4 ⇓ v.
Proof.
  compute.
  evar (v: (cTerm certiL4)).
  exists (Ret v).
  econstructor; eauto.
  compute.
  try (econstructor; eauto;compute;[]).
  eapply expression.eval_FixApp_e; try (compute; eauto; fail);
    [apply eval_Con_e; repeat (econstructor; eauto) | ].
(* Constructors are numbered as listed in Coq definition : e.g. 0 for O and 1 for S --
see how 3 gets represented.

In Template Coq, [(tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1)] 
the "1" at the end represents "S". The "0" perhaps signifies that this constructor
is one of the first inductive block in the (trivially)mutually inductive block.


Var_e 2  revers to isOdd. in the sibling of the branch where 
Var_e 2 is mentioned, true is returned in the other case. 
Var_e 3  revers to isEven.

In a nominal (w.r.t. variable bindings) setting,
 this ordering is reverse of how these definitions appear in the mutually inductive block.
However, note that these are DB indices. So, the highest number is the outermost (head) 
of the list of fix bodies, which is isEven. So it makes sense in the DB setting.

Also, note how sbst_fix accounts for this by folding over the list of indices in a 
decreasing order. Also, note that this choice of reverse ordering goes back to Template Coq--
see isEven3

*)
  unfold sbst_fix.
  simpl list_to_zero.
  remember (0%nat :: nil) as l0.
  simpl.
  compute.
  subst l0. compute.
  econstructor; eauto;
    [apply eval_Con_e; repeat (econstructor; eauto) | ].
  compute.
  econstructor; eauto;
    [apply eval_Con_e; repeat (econstructor; eauto) | | ].
  compute.
  econstructor; eauto.
  compute.
  eapply expression.eval_FixApp_e; try (compute; eauto; fail);
    [apply eval_Con_e; repeat (econstructor; eauto) | ].
  compute.
  compute.
Abort.



