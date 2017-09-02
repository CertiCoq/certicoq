Require Import L2k.compile.
Require Import L2k.wcbvEval.
Require Import L2k.term.
Require Import certiClasses.
Require Import Common.Common.
Require Import L2.instances.
Require Import certiClasses2.
Require Import L2k.stripEvalCommute.


(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL2Term: GoodTerm (Program L2k.compile.Term) :=
  fun _  => True.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L2k.compile.Term) :
  (L2k.compile.Term * (list L2k.compile.Term)) :=
  match t with
    | TApp fn arg args => (fn, cons arg (Terms_list args))
    | s => (s, nil)
  end.

Global Instance QuestionHeadL2kTerm: QuestionHead (Program L2k.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false
    end.

Global Instance ObsSubtermL2kTerm :
  ObserveNthSubterm (Program L2k.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _, subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Global Instance certiL2kEval:
  BigStepOpSem (Program L2k.compile.Term) (Program L2k.compile.Term).
Proof.
  intros s sv. destruct s, sv. exact (WcbvEval env main main0 /\ env = env0).
Defined.

Global Instance certiL2k: CerticoqLanguage (Program L2k.compile.Term).

Instance certiL2_to_L2k: 
  CerticoqTotalTranslation (Program L2.compile.Term)
                           (Program L2k.compile.Term) :=
  stripProgram.


Require Import certiClasses2.

(* Lemma flattenAppCommutes: *)
(*   forall main : L2.compile.Term, *)
(*   flattenApp (L2k.compile.strip main) = *)
(*   (strip (fst (L2.instances.flattenApp main)), *)
(*    List.map strip (snd (L2.instances.flattenApp main))). *)
(* Proof using. *)
(*   destruct main; auto. *)
(*   simpl. f_equal. f_equal. *)
(*   induction t; auto. *)
(*   simpl. f_equal. auto. *)
(* Qed. *)

Require Import Coq.btauto.Btauto.
Require Import SquiggleEq.list.

(** funny behavior of yesPreserved and ⊑ **)
Quote Recursively Definition p_true := (fun (x:True) => true).
Definition P_true := Eval cbv in (program_Program p_true).

Quote Recursively Definition p_false := (fun (x:True) => false).
Definition P_false := Eval cbv in (program_Program p_false).

Lemma foo:
  yesPreserved P_true P_false.
Proof.
  unfold P_true, P_false, yesPreserved, questionHead, QuestionHeadL2Term; cbn.
  unfold implb. destruct q; reflexivity.
Qed.

(**  This seems wrong! **)
Goal P_true ⊑ P_false.
Proof.
  unfold P_true, P_false. constructor.
  - apply foo.
  - intros. unfold observeNthSubterm, ObsSubtermL2Term. cbn. constructor.
Qed.


Lemma identity_pres_yes:
  forall (p:Program Term), yesPreserved p p.
Proof.
  destruct p. unfold yesPreserved, questionHead, QuestionHeadL2kTerm; cbn.
  destruct q.
  - destruct (fst (flattenApp main)); unfold implb; try reflexivity.
    btauto.
  - destruct (fst (flattenApp main)); unfold implb; try reflexivity.
Qed.

Lemma stripProgram_pres_yes:
  forall (p:Program L2.compile.Term), yesPreserved p (stripProgram p).
Proof.
  destruct p. unfold stripProgram. cbn.
  unfold yesPreserved, questionHead, QuestionHeadL2Term.
  cbn.
Admitted.
(*
Lemma my_stripProgram_pres_yes:
  forall (main: L2.compile.Term) (env: environ L2.compile.Term) stv otv,
    L2.wcbvEval.WcbvEval env main stv ->
    WcbvEval (stripEnv env) (strip main) otv ->
    yesPreserved {| main := stv; env := env |}
      {| main := otv; env := stripEnv env |}.
Proof.
  intros.
  (* pose proof (sac_sound H H0). subst. *)
  unfold yesPreserved, questionHead, QuestionHeadL2Term, QuestionHeadL2kTerm.
  cbn. rewrite flattenAppCommutes.
  remember (fst (L1g.instances.flattenApp stv)) as mm. cbn.
  destruct mm, q; cbn; try reflexivity.
  unfold implb. btauto.
Qed.

Lemma compileObsEq:
  forall (main: L1g.compile.Term) (env: environ L1g.compile.Term),
    {| main := main; env := env |} ⊑
      stripProgram {| main := main; env := env |}.
Proof.
  cofix.
  intros. constructor.
  - set (p:= {| main := main; env := env |}). apply stripProgram_pres_yes.
  - intros ?.
    unfold observeNthSubterm, ObsSubtermL1gTerm, ObsSubtermL2Term. cbn.
    rewrite flattenAppCommutes.
    destruct (L1g.instances.flattenApp main) as [f args].
    cbn. clear main.
    destruct f; cbn; try constructor.
    rewrite nth_error_map.
    unfold compile.L1gTerm.
    remember  (List.nth_error args n) as ln.
    clear Heqln. destruct ln; try constructor.
    apply compileObsEq.
Qed.
Print Assumptions compileObsEq.

Goal
  forall (main: L1g.compile.Term) (env: environ L1g.compile.Term),
    {| main := main; env := env |} ⊑
      stripProgram {| main := main; env := env |}.
Proof.
  cofix.
  intros. constructor.
  - set (p:= {| main := main; env := env |}). apply stripProgram_pres_yes.
  - intros ?. 
    unfold observeNthSubterm, ObsSubtermL1gTerm, ObsSubtermL2Term. cbn.
    rewrite flattenAppCommutes.
    destruct (L1g.instances.flattenApp main) as [f args].
    cbn. clear main.
    destruct f; cbn; try constructor.
    rewrite nth_error_map.
    unfold compile.L1gTerm.
    remember  (List.nth_error args n) as ln.
    clear Heqln. destruct ln; try constructor.
    apply compileObsEq.
Qed.


Global Instance certiL1g_to_L2Correct:
  CerticoqTranslationCorrect certiL1g certiL2.
Proof.
  split.
  - intros ? ?. cbn. unfold translateT, certiL1g_to_L2. trivial.
  - unfold obsPreserving. intros s sv _ Hev.
    destruct s as [smain senv], sv as [svmain svenv]. cbn.
    destruct Hev as [Hev HevEnv]. subst svenv.
    exists (stripProgram {| main := svmain; env := senv |}).
    split. split.
    + cbn. apply (proj1 (stripEvalCommute.WcbvEval_hom _) _ _ Hev).
    + reflexivity.
    + apply compileObsEq.
Qed.
Print Assumptions certiL1g_to_L2Correct.
(* Closed under the global context *)

*************)