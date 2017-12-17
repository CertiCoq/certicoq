
Require Import Common.Common.
Require Import L1g.instances.
Require Import L2.compile.
Require Import L2.term.
Require Import L2.wcbvEval.
Require Import L2.stripEvalCommute.
Require Import certiClasses.
Require Import certiClasses2.
Require Import ExtLib.Data.ListNth.
Set Template Cast Propositions.



(** If the compiler only correctly compiles terms with some properties,
 add them here. *)
Instance WfL2Term : GoodTerm (Program L2.compile.Term) :=
   fun P:Program Term =>
     match P with
       mkPgm trm e => WFapp trm /\ WFaEnv WFapp e
     end.

Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.


Fixpoint Terms_list (ts:Terms) : list Term :=
  match ts with
    | tnil => nil
    | tcons u us => cons u (Terms_list us)
  end.

Lemma Terms_list_hom:
  forall ts:L1g.compile.Terms,
    Terms_list (strips ts) = List.map strip (L1g.instances.Terms_list ts).
Proof.
  induction ts.
  - reflexivity.
  - rewrite tcons_hom.
    change
      (cons (strip t) (Terms_list (strips ts)) =
       cons (strip t) (List.map strip (L1g.instances.Terms_list ts))).
    rewrite IHts. reflexivity.
Qed.

Function flattenApp
         (t:L2.compile.Term): (L2.compile.Term * (list L2.compile.Term)) :=
  match t with
  | TApp fn arg args => (fn, cons arg (Terms_list args))
  | s => (s, nil)
  end.

Lemma flattenAppCommutes: 
  forall main: L1g.compile.Term,
    L1g.term.WFapp main ->
    flattenApp (L2.compile.strip main) =
    (strip (fst (L1g.instances.flattenApp main)),
     List.map strip (snd (L1g.instances.flattenApp main))).
Proof.
  destruct 1; try reflexivity.
  rewrite TApp_hom. rewrite mkApp_goodFn.
  - cbn. rewrite Terms_list_hom. reflexivity.
  - intros k. elim H. apply isApp_L1g_term_isApp. assumption.
Qed.

Lemma WFapp_flattenApp:
  forall main,
    L1g.term.WFapp main ->
    L1g.instances.WFapps_list (snd (L1g.instances.flattenApp main)).
Proof.
  destruct main; cbn; intros; try constructor.
  - inversion_Clear H. assumption.
  - inversion_Clear H. apply WFapps_WFapps_list. assumption.
Qed.


Global Instance QuestionHeadL2Term: QuestionHead (Program L2.compile.Term) :=
  fun (q:Question) (t:Program Term) => 
    match q, fst (flattenApp (main t)) with
      | Cnstr ind ci, TConstruct ind2 ci2 _ _ =>
        andb (decide (ind=ind2)) (decide (ci=ci2))
      | Abs, TLambda _ _ => true
      | _, _ => false 
    end.

Global Instance ObsSubtermL2Term :
  ObserveNthSubterm (Program L2.compile.Term) :=
  fun n t =>
    match  (flattenApp (main t)) with
      | (TConstruct _ _ _ _, subterms) =>
        match List.nth_error subterms n with
          | Some st => Some {| env := env t; main := st |}
          | None => None
        end
      | _ => None
    end.

Global Instance certiL2Eval:
  BigStepOpSem (Program L2.compile.Term) (Program L2.compile.Term).
Proof.
  intros s sv. destruct s, sv. exact (WcbvEval env main main0 /\ env = env0).
Defined.

Global Instance certiL2: CerticoqLanguage (Program L2.compile.Term).

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.


Require Import Coq.btauto.Btauto.
Require Import SquiggleEq.list.

(** funny behavior of yesPreserved and ⊑ **)
Quote Recursively Definition p_true := (fun (x:True) => true).
Definition P_true := Eval cbv in (program_Program p_true).

Quote Recursively Definition p_false := (fun (x:True) => false).
Definition P_false := Eval cbv in (program_Program p_false).

Lemma foo1:
  yesPreserved P_true P_false.
Proof.
  unfold P_true, P_false, yesPreserved, questionHead, QuestionHeadL2Term; cbn.
  unfold implb. destruct q; reflexivity.
Qed.

(**  This seems wrong! **)
Goal P_true ⊑ P_false.
Proof.
  unfold P_true, P_false. constructor.
  - apply foo1.
  - intros. unfold observeNthSubterm, ObsSubtermL2Term. cbn. constructor.
Qed.

(** yesPreserved and proofs **)
Inductive NN: Prop := NN0: NN | NNS: NN -> NN.
Quote Recursively Definition p_NN0 := NN0.
Definition P_NN0 := Eval cbv in (program_Program p_NN0).

Quote Recursively Definition p_NN1:= (NNS NN0).
Definition P_NN1 := Eval cbv in (program_Program p_NN1).

Goal
  yesPreserved P_NN0 P_NN1.
Proof.
  unfold P_NN0, P_NN1, yesPreserved, questionHead, QuestionHeadL2Term.
  cbn. unfold implb. destruct q; try reflexivity.
Qed.
Goal
  yesPreserved P_NN1 P_NN0.
Proof.
  unfold P_NN0, P_NN1, yesPreserved, questionHead, QuestionHeadL2Term.
  cbn. unfold implb. destruct q; try reflexivity.
Qed.
Goal
  forall (p:Program Term), yesPreserved p p.
Proof.
  destruct p. unfold yesPreserved, questionHead, QuestionHeadL2Term; cbn.
  destruct q.
  - destruct (fst (flattenApp main)); unfold implb; try reflexivity.
    btauto.
  - destruct (fst (flattenApp main)); unfold implb; try reflexivity.
Qed.

Lemma stripProgram_pres_yes:
  forall (p:Program L1g.compile.Term),
    L1g.term.WFapp (main p) -> yesPreserved p (stripProgram p).
Proof.
  intros p hp. destruct p. unfold stripProgram.
  unfold yesPreserved, questionHead, QuestionHeadL1gTerm, QuestionHeadL2Term.
  cbn. rewrite flattenAppCommutes.
  remember (fst (L1g.instances.flattenApp main)) as mm. cbn.
  destruct mm, q; cbn; try reflexivity.
  unfold implb. btauto.
  assumption.
Qed.

Lemma compileObsEq:
  forall (main: L1g.compile.Term) (env: environ L1g.compile.Term),
    L1g.term.WFapp main ->
    {| main := main; env := env |} ⊑
      stripProgram {| main := main; env := env |}.
Proof.
  cofix.
  intros. constructor.
  - set (p:= {| main := main; env := env |}).
    apply stripProgram_pres_yes. assumption.
  - intros ?.
    unfold observeNthSubterm, ObsSubtermL1gTerm, ObsSubtermL2Term. cbn.
    rewrite flattenAppCommutes; try assumption.
    case_eq (L1g.instances.flattenApp main); intros f args j.
    cbn; try constructor.
    rewrite nth_error_map.
    unfold compile.L1gTerm.
    remember (List.nth_error args n) as ln.
    destruct ln; try constructor; cbn; destruct f; cbn; try constructor.
    apply compileObsEq. eapply (nth_pres_WFapp args).
    + destruct (args_pres_WFapp _ H). rewrite j in H1. assumption.
    + symmetry. eassumption.
Qed.
Print Assumptions compileObsEq.

Global Instance certiL1g_to_L2Correct:
  CerticoqTranslationCorrect certiL1g certiL2.
Proof.
  split.
  - intros ? ?. cbn. unfold translateT, certiL1g_to_L2.
    destruct s. cbn in *. destruct H. split.
    + eapply (proj1 WFapp_hom). assumption.
    + apply (WFaEnv_hom H0).
  - unfold obsPreserving. intros s sv _ Hev.
    destruct s as [smain senv], sv as [svmain svenv]. cbn.
    destruct Hev as [Hev HevEnv]. subst svenv.
    exists (stripProgram {| main := svmain; env := senv |}).
    split. split.
    + cbn. refine (proj1 (stripEvalCommute.WcbvEval_hom _) _ _ Hev _).
      * admit.
      * admit.
    + reflexivity.
    + apply compileObsEq.
Admitted.
Print Assumptions certiL1g_to_L2Correct.
