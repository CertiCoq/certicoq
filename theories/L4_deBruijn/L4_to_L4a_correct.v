Require Import L4.expression.
Require Import L4.L4a_to_L5.
Require Import L4.L4_to_L4a.

Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.

(* circularity watch: this correctness property cannot go to L4.instances. Should we have
L4.correctnessInstances for such instances? *)
Require Import L4.instances.
Require Import Common.certiClasses.

Require Import BinNat.
Require Import BinPos.
Require Import Omega.
Require Import Psatz.
Require Import Arith.
Require Import PArith.
Require Import NArith.


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

Require Import SquiggleEq.tactics.
Print my_exp_wf_ind.
Require Import Basics.
SearchAbout Basics.compose. 
Require Import Coq.Unicode.Utf8.
Require Import List.
Require Import SquiggleEq.list.


Open Scope program_scope.
Print exp_wf.
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
    -> forall v, List.In v (flat_map free_vars (translatef mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
 ∧
  (forall n (s : branches_e),
    L4.expression.branches_wf n s 
    -> forall v, List.In v (flat_map (free_vars_bterm ∘ snd)  (translateb mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *))
.
Proof.
  apply my_exp_wf_ind;
  intros ? ?.
- intros Hwf ? Hin. simpl in Hin. rewrite or_false_r in Hin.
  subst. split; [ | refl].
  simpl.
  rewrite N.succ_pos_spec.
  rewrite N.sub_1_r.
  rewrite N.lt_succ_pred with (z:=0%N); lia.

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

- intros ? ? H1ind H1wf H2ind ? Hin. simpl in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  repeat (rewrite list.in_app_iff in Hin).
  rewrite or_false_r in Hin.
  dorn Hin; eauto.

- intros ? Hwf Hind ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translatel mkVar i) in Hin.
  rewrite flat_map_bterm_nil in Hin.
  eauto.

- intros ? ? Hwf Hind ? Hindb ? Hin.
  simpl in Hin.
  fold (L4_to_L4a.translateb mkVar i) in Hin.
  fold (L4_to_L4a.translate mkVar i) in Hin.
  apply list.in_app_iff in Hin.
  rewrite list.flat_map_map in Hin.
  dorn Hin; eauto.

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
  fold (L4_to_L4a.translatef  mkVar (N.succ i)) in Hin.

Print exp_wf.
Print sbst_fix. 

Print exp_wf.
(*  rewrite flat_map_bterm_nil in Hin.
  rwsimpl Hin.
   
  eauto.
compute in Hin. *)
Abort.


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



