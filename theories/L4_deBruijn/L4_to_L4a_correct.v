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



Lemma mkVarDiv : forall i s, 
  N.pos (Pos.div2 (fst (mkVar i s))) = N.succ i.
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
    -> forall v, List.In v (flat_map (free_vars_bterm ∘ snd)  (translatelb mkVar n s)) -> 
        (Npos (Pos.div2 v) < N.succ n)%N /\ varClass v = true (* user variable *)).
Proof using.
  apply my_exp_wf_ind; try (simpl; tauto); [ | | | | | | | | | ];
  intros ? ?.
(* Var_e *)
- intros Hwf ? Hin. simpl in Hin. rewrite or_false_r in Hin.
  subst. split; [ | refl].
  rewrite mkVarDiv.
  rewrite N.sub_1_r.
  rewrite N.lt_succ_pred with (z:=0%N); lia.

(* Lam_e *)
- intros e Hwf Hind ? Hin.
  simpl in Hin.
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
  repeat (rewrite list.in_app_iff in Hin).
  rewrite or_false_r in Hin.
  dorn Hin; eauto.

(* Con_e *)
- intros ? Hwf Hind ? Hin.
  simpl in Hin.
  rewrite flat_map_bterm_nil in Hin.
  eauto.

(* Match_e *)
- intros ? ? Hwf Hind ? Hindb ? Hin.
  simpl in Hin.
  apply list.in_app_iff in Hin.
  rewrite list.flat_map_map in Hin.
  dorn Hin; eauto.
  (* the crux of this proof comes later, in the translateb case *)

(* Let_e *)
- intros ? ? Hwf Hind H2wf H2ind ? Hin.
  simpl in Hin.
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
  apply in_app_iff in Hin.
  dorn Hin; eauto.
- intros ? Hwf Hind H2wf H2ind ? Hin. simpl in Hin.
  apply in_app_iff in Hin.
  dorn Hin; eauto.
- intros ? ? ? Hwf Hind  H2wf H2ind ? Hin. simpl in Hin.
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

Lemma L4_to_L4a_closed: 
  forall (s : exp),
    L4.expression.exp_wf 0 s 
    -> closed (L4_to_L4a 0 s).
Proof using.
  intros.
  pose proof L4_to_L4a_fvars. repnd. clear H2 H3 H0.
  unfold closed.
  apply' H1  H.
  clear H1.
  apply null_iff_nil.
  intros ? Hin.
  apply_clear H in Hin. lia.
Qed.

Require Import Morphisms.

Definition lsbst (es:list exp) (e : exp) : exp :=
  fold_left (* _right ? Matthieu's email Thu, Aug 11, 2016 at 3:03 PM EST *)
      (fun e esi => e{0 ::= esi}) es e. (* generalize over 0? *)

Open Scope N_scope.
Require Import RandyPrelude.


Lemma succ_sub_1 : forall n,  N.succ n - 1 = n.
Proof using.
intros. lia.
Qed.

Lemma mkVarInj : forall a b, mkVar a = mkVar b -> a = b.
Proof using.
  intros ? ? Heq.
  apply (f_equal (fun x =>  N.pos (Pos.div2 x))) in Heq.
  do 2 rewrite mkVarDiv in Heq. lia.
Qed.


Lemma L4_to_L4a_ssubst:
    forall (ls : list exp),
    let sub n := combine 
                (map mkVar (rev (L4_to_L4a.seq N.succ n (length ls))))
                (map (L4_to_L4a 0) ls) in
 lforall (exp_wf 0) ls
  ->
 (forall n (e : exp),
    L4.expression.exp_wf n e
    -> L4_to_L4a n (lsbst ls e) = ssubst (L4_to_L4a n e) (sub n))
 ∧
  (forall n (s : exps),
    L4.expression.exps_wf n s 
    -> True)
 ∧
  (forall n (s : efnlst),
    L4.expression.efnlst_wf n s 
    -> True)
 ∧
  (forall n (s : branches_e),
    L4.expression.branches_wf n s 
    -> True).
Proof using.
  intros ? ? Hlwf. unfold sub. clear sub.
  apply my_exp_wf_ind; try (simpl; tauto); [ | | | | | | | ];
  intros ? ?.
(* Var_e *)
- intros Hlt. simpl. revert dependent i. revert j.
  induction ls as [ |s ls]; intros ? ? ?;[ refl | ].
  simpl.
  case_if as Hj;[ lia | ]. clear Hj.
  rename i into n.
  destruct n;[ lia | ].
  rewrite <- N.sub_add_distr, N.add_1_r.
(*  rewrite (@rev_unit _ _ (N.pos p)).
SearchAbout rev.
  rewrite Nat2N.inj_succ in *.
  destruct (N.zero_or_succ j) as [ Hd | Hd]; subst.
  + simpl. rewrite OrdersEx.N_as_OT.sub_0_r. simpl.
    rewrite <- beq_var_refl.
    SearchAbout exp_wf sbstitute.
    pose proof (proj1 (sbst_closed_id s) 0).
    admit.
  + destruct Hd as [j' Hd]. subst. rename j' into j.
    rewrite N.compare_lt_iff in H0.
    rewrite cons_as_app in Hlwf.
    apply lforallApp in Hlwf. repnd.
    rewrite <- N.succ_lt_mono in H0.
    specialize (IHls Hlwf _ _ H0).
    rewrite Nat2N.id in IHls.
    specialize (IHls eq_refl).
    cases_if; [ lia | ].
    rewrite succ_sub_1. rewrite IHls.
    rewrite <- N.sub_add_distr, N.add_1_r.
    rewrite beq_deq.
    cases_if as Hd;[provefalse |  refl].
    apply mkVarInj in Hd. lia.

- intros Hwf Hl.
Qed.
*)
Abort.


Lemma translatel_len : forall A f n es, 
  length (@translatel A f n es) = N.to_nat (exps_length es).
Proof using.
  induction es; auto.
  simpl. rewrite IHes.
  rewrite <- N2Nat.inj_succ.
  rewrite <- N.add_1_l.
  refl.
Qed.

(* exact same as above *)
Lemma translatef_len : forall A f n es, 
  length (@translatef A f n es) = N.to_nat (efnlst_length es).
Proof using.
  induction es; auto.
  simpl. rewrite IHes.
  rewrite <- N2Nat.inj_succ.
  rewrite <- N.add_1_l.
  refl.
Qed.


Lemma gseq_length A (f:A->A) n x : length (L4_to_L4a.seq f x n) = n.
Proof using.
  intros.
  rewrite seq_spec, map_length, seq_length. refl.
Qed.

Hint Rewrite translatef_len translatel_len gseq_length: list.

SearchAbout L4_to_L4a.seq.

Lemma translate_find_branch : ∀ d vs bs e,
expression.find_branch d (exps_length vs) bs = Some e
-> find_branch d (N.to_nat (exps_length vs)) (translatelb mkVar 0 bs) = 
   Some (snd (translateb mkVar 0 L4_to_L4a.translate d  (exps_length vs) e)).
Proof using.
  intros ? ? ? ? Hfb. unfold find_branch.
  induction bs; auto;[ inverts Hfb | ]; simpl in *.
  unfold num_bvars. simpl.
  rewrite seq_spec, map_length. rewrite map_length.
  rewrite seq_length.
  cases_if as Hd.
- apply Bool.andb_true_iff in Hd.
  setoid_rewrite DecidableClass.Decidable_spec in Hd.
  repnd.
  apply beq_nat_true in Hd. symmetry in Hd0. rewrite Hd0 in *.
  clear Hd0. clear d0.
  simpl in *.
  apply N2Nat.inj_iff in Hd.
  cases_if; try tauto.
  subst.
  cases_if; try tauto.
  inverts Hfb. refl.
- 
Admitted.

Lemma exps_skipn0 es : exps_skipn 0 es = es.
Proof using.
  destruct es; auto.
Qed.

Local Lemma eval_eq_l : forall a a' b, 
  eval a b
  -> a=a'
  -> eval a' b.
Proof using.
  intros; subst; auto.
Qed.

(* move to expression.v *)
Lemma evals_length es vs: 
evals es vs
-> exps_length es = exps_length vs.
Proof using.
 intro H. induction H; auto.
 simpl. rewrite IHevals. refl.
Qed.

Lemma sbst_translate_comm e1 v2:
exp_wf 1 e1
-> exp_wf 0 v2
-> L4_to_L4a.translate mkVar 0 (sbst v2 0 e1)
   = ssubst (L4_to_L4a.translate mkVar 1 e1) [(mkVar 0, L4_to_L4a.translate mkVar 0 v2)].
Admitted.

Lemma sbst_list_translate_comm e vs:
exp_wf (exps_length vs) e
-> exps_wf 0 vs
-> L4_to_L4a.translate mkVar 0 (sbst_list e vs) =
   ssubst (L4_to_L4a.translate mkVar (exps_length vs) e)
    (combine (map mkVar (L4_to_L4a.seq N.succ 0 (N.to_nat (exps_length vs))))
    (translatel mkVar 0 vs)).
Admitted.

Lemma sbst_fix_translate_comm  e es:
exp_wf (efnlst_length es) e
-> efnlst_wf (efnlst_length es) es
-> L4_to_L4a.translate mkVar 0 (sbst_fix es e) =
ssubst (L4_to_L4a (efnlst_length es) e)
  (combine (map mkVar (L4_to_L4a.seq N.succ 0 (N.to_nat (efnlst_length es))))
     (map
        (Fix_e'
           (map (bterm (map mkVar (L4_to_L4a.seq N.succ 0 (N.to_nat (efnlst_length es)))))
              (translatef mkVar (efnlst_length es) es)))
        (seq 0 (N.to_nat (efnlst_length es))))).
(* can sbst_fix implemented using sbst_list, and then can this be a corollary of 
sbst_list_translate_comm above *)
Admitted.


Lemma enthopt_translate max e n es:
enthopt (N.to_nat n) es = Some e
-> select (N.to_nat n) (translatef mkVar max es) 
   = Some (L4_to_L4a max e).
Proof using.
 revert es.
 induction n using N.peano_rect; simpl; destruct es as [ | he es]; simpl;
 try rewrite N2Nat.inj_succ;
 intros Hnth; try  invertsn Hnth; eauto.
Qed.


Lemma preserves_eval :
(∀ (e v : exp),expression.eval e v 
  -> exp_wf 0 e -> eval (L4_to_L4a 0 e) (L4_to_L4a 0 v))
∧ (∀ (es vs : exps), evals es vs
    -> exps_wf 0 es
    -> forall e v, 
       In (e,v) (combine (translatel mkVar 0 es) (translatel mkVar 0 vs)) 
       -> eval e v).
Proof using.
  apply my_eval_ind; [ | | | | | | | | | ]; unfold L4_to_L4a.
- intros ? ? _. simpl. constructor.
(* beta *)
- intros ? ? ? ? ? ? H1s H1t H2s H2t H3s H3t Hwf.
  simpl in *.
  inverts Hwf.
  econstructor; eauto.
  clear H1t H2t.
  eapply eval_preserves_wf in H1s; eauto.
  eapply eval_preserves_wf in H2s; eauto.
  clear H2 H3.
  inverts H1s as H1s.
  eapply eval_eq_l; eauto.
  simpl. unfold subst. simpl in H1s.
  apply sbst_translate_comm; auto.

- intros ? ? ? H1s H1t Hwf.
  simpl.
  inverts Hwf.
  econstructor; eauto.
  do 2 rewrite translatel_len. f_equal.
  apply evals_length; auto.

(* zeta *)
- intros ? ? ? ? ? H1s H1t H2s H2t Hwf.
  inverts Hwf. simpl.
  econstructor; eauto.
  clear H1t.
  eapply eval_preserves_wf in H1s; eauto.
  eapply eval_eq_l; eauto.
  simpl. unfold subst.
  eapply sbst_translate_comm; eauto.

(* iota *)
- intros ? ? ? ? ? ? ? H1s H1t Hfb H2s H2t Hwf.
  simpl in *.
  inverts Hwf.
  assert (p=0) by admit. (* fix either L4.eval or L4a.eval,L5.eval *)
  subst.
  rewrite exps_skipn0 in *.
  econstructor; eauto.
  rewrite translatel_len.
  eapply translate_find_branch; eauto.
  simpl. unfold apply_bterm. simpl.
  eapply find_branch_preserves_wf in Hfb; eauto.
  eapply eval_preserves_wf in H1s; eauto.
  inverts H1s.
  eapply eval_eq_l; eauto using subst_list_preserves_exp_wf.
  rewrite N.add_0_r in Hfb.
  apply sbst_list_translate_comm; auto.

(* eval_Fix_e  *)
- intros.  econstructor; eauto.

(*  eval_FixApp_e *)
- intros ? ? ? ? ? ? ? H1s H1t  H2s H2t Hnth H3s H3t Hwf.
  simpl in *.
  inverts Hwf.
  pose proof Hnth as Hnthb.
  eapply enthopt_translate with (max:= efnlst_length es) in Hnth; eauto.
  eapply eval_FixApp_e; eauto;
    [ apply select_map; apply Hnth 
      | 
      | unfold num_bvars; simpl; autorewrite with list;refl].
  
  autorewrite with list.
  unfold apply_bterm. simpl.
  eapply eval_preserves_wf in H1s; eauto.
  invertsn H1s.
  rewrite N.add_0_r in H1s.
  eapply eval_preserves_wf in H2s; eauto.
  eapply nthopt_preserves_wf in Hnthb; eauto.
  eapply eval_eq_l; [ apply H3t; constructor; eauto using sbst_fix_preserves_wf; fail | ].
  f_equal.
  apply sbst_fix_translate_comm; auto.

- intros. simpl. constructor; auto. cpx.

- simpl. tauto.

- intros ? ? ? ? H1s H1t H2s H2t Hwf ? ? Hin. inverts Hwf. 
  simpl in Hin. dorn Hin; eauto;[].
  inverts Hin; auto; fail.

Admitted.

  

(*
subst (L4_to_L4a.translate mkVar 1 t) (mkVar 0) (L4_to_L4a.translate mkVar 0 v2) =
L4_to_L4a.translate mkVar 0 (sbst v2 0 t)
*)
  
  


  
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
| O => true
| S n' => isOdd n' (* && isEven n' *)
end
with isOdd (n:nat) : bool :=
match n with
| O => false
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


Eval compute in 
  let s1 := (Con_e (Ast.mkInd "" 0,1) enil) in
  let s2 := (Con_e (Ast.mkInd "" 0,0) enil) in
  let t := App_e (Var_e 0) (Var_e 1) in
  (sbst s2 1 (sbst s1 0 t), sbst s1 0 (sbst s2 1 t)).

Hint Constructors expression.eval.
Hint Constructors expression.evals.
Print Instances BigStepOpSem.
(*
Lemma isEven3Eval : exists (v : exception exp), (isEven3L4) ⇓ v.
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
*)


