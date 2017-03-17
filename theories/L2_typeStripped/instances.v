Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import L2.term.
Require Import certiClasses.
Require Import Common.Common.
Require Import L1g.instances.
Require Import certiClasses2.
Require Import L2.stripEvalCommute.


(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL2Term: GoodTerm (Program L2.compile.Term) :=
  fun _  => True.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.

Definition flattenApp (t:L2.compile.Term) :
  (L2.compile.Term * (list L2.compile.Term)) :=
  match t with
    | TApp fn arg args => (fn, cons arg (Terms_list args))
    | s => (s, nil)
  end.

Global Instance QuestionHeadL2Term: QuestionHead (Program L2.compile.Term) :=
  fun q t =>
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _(*nargs*) =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL2Term :
  ObserveNthSubterm (Program L2.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ , subterms) =>
        match List.nth_error subterms  n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Global Instance certiL2Eval:
  BigStepOpSem (Program L2.compile.Term) (Program L2.compile.Term).
  apply BigStepOpWEnv.
  exact WcbvEval.
Defined.

Global Instance certiL2: CerticoqLanguage (Program L2.compile.Term).

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.

Lemma flattenAppCommutes:
  forall main : L1g.compile.Term,
  flattenApp (L2.compile.strip main) =
  (strip (fst (L1g.instances.flattenApp main)),
   List.map strip (snd (L1g.instances.flattenApp main))).
Proof using.
  destruct main; auto.
  simpl. f_equal. f_equal.
  induction t; auto.
  simpl. f_equal. auto.
Qed.

Require Import Coq.btauto.Btauto.
Require Import SquiggleEq.list.

(****
Lemma compileObsEq:
  forall L1gp: Program L1g.compile.Term, L1gp ⊑ stripProgram L1gp.
Proof.
  cofix.
  intros. constructor.
  - unfold yesPreserved. intros q.
    unfold questionHead, QuestionHeadL1gTerm, QuestionHeadL2Term.
    cbn. rewrite flattenAppCommutes. clear.

  destruct L1gp.
  cofix.
  intros. constructor.
  - intros q. unfold questionHead, QuestionHeadL1gTerm, QuestionHeadL2Term.
    simpl. rewrite flattenAppCommutes.
    clear.
    remember (fst (L1g.instances.flattenApp main)) as mm.
    clear Heqmm. simpl.
    clear main.
    destruct mm, q; cbn; try reflexivity.
    unfold implb.
    btauto.
  - intros ?.
    unfold observeNthSubterm, ObsSubtermL1gTerm, ObsSubtermL2Term. simpl.
    rewrite flattenAppCommutes.
    destruct (L1g.instances.flattenApp main) as [f args].
    simpl. 
    destruct f; cbn; try constructor.
    rewrite nth_error_map.
    unfold compile.L1gTerm.
    remember  (List.nth_error args n) as ln.
    clear Heqln. destruct ln; try constructor. Check compileObsEq.
    apply compileObsEq.
Qed.
****)
    
Lemma compileObsEq:
  forall (main: L1g.compile.Term) (env: environ L1g.compile.Term),
    {| main := main; env := env |} ⊑
      stripProgram {| main := main; env := env |}.
Proof.
  cofix.
  intros. constructor.
  - intros q. unfold questionHead, QuestionHeadL1gTerm, QuestionHeadL2Term.
    simpl. rewrite flattenAppCommutes.
    clear.
    remember (fst (L1g.instances.flattenApp main)) as mm.
    clear Heqmm. simpl.
    clear main.
    destruct mm, q; cbn; try reflexivity.
    unfold implb.
    btauto.
  - intros ?.
    unfold observeNthSubterm, ObsSubtermL1gTerm, ObsSubtermL2Term. simpl.
    rewrite flattenAppCommutes.
    destruct (L1g.instances.flattenApp main) as [f args].
    simpl. clear main.
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
  - intros ? ? _ Hev. cbn. unfold translateT, certiL1g_to_L2.
    destruct Hev as [Hev HevEnv].
    destruct s as [smain senv]. 
    destruct sv as [svmain svenv]. cbn in *. subst svenv.
    exists (stripProgram {| main := svmain; env := senv |}).
    split. split.
    + cbn. apply (proj1 (stripEvalCommute.WcbvEval_hom _) _ _ Hev).
    + reflexivity.
    + clear. apply compileObsEq.
Qed.

Print Assumptions certiL1g_to_L2Correct.
(* Closed under the global context *)